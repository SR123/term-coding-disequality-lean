import UnitFlowCost
import CostMonad

/-! # Execution-linked cost of the augmenting-path algorithm: an instrumented program

Every executable definition of `UnitFlow.lean` is re-implemented as an instrumented program
in the step-counting monad `Costed` (`CostMonad.lean`).  The primitives and their charges are
exactly those of `UnitFlowCost.lean`: `tick 1` per list cell examined or produced (scan, map,
filter, append, reverse, flatten, cons, measuring a length), `tick (c x)` per label copied,
compared or constructed, `tick (natC f)` per operation on the binary fuel counter.  Scans are
full scans (the instrumented membership test, `find?` and `any` visit every cell, which is
what the cost functions charge); the recomputation of `layers` by `augPath` and of `steps p`
inside the augmentation filter are executed, not shared.

For every definition `X` the theorems `XM_val` and `XM_cost` prove that the instrumented
program computes the pure definition and that its step count is the cost function.  In
particular `maxflowM_spec`: the instrumented maximum-flow program computes `maxflow` in
exactly `maxflowC` steps, hence in at most `flowBound n m L` steps (`maxflowC_le`). -/

namespace DisequalityDispersion.Flow
namespace Network

open DisequalityDispersion.Costed
open DisequalityDispersion.Encoded (natC)

variable {ν : Type} [DecidableEq ν] (N : Network ν) (c : ν → ℕ)

/-! ### Scans -/

/-- Full-scan membership of a pair: every cell costs a comparison of two pairs. -/
def memM (l : List (ν × ν)) (e : ν × ν) : Costed Bool :=
  anyM 0 (fun e' => do tick (1 + pc c e + pc c e'); Pure.pure (decide (e' = e))) l

theorem any_eq_decide_mem {α : Type} [DecidableEq α] (e : α) :
    ∀ (l : List α), l.any (fun e' => decide (e' = e)) = decide (e ∈ l)
  | [] => by simp
  | a :: l => by
      rw [List.any_cons, any_eq_decide_mem e l]
      by_cases h : a = e
      · subst h; simp
      · have h' : ¬ e = a := fun h'' => h h''.symm
        simp [h, h', List.mem_cons]

theorem memM_val (l : List (ν × ν)) (e : ν × ν) : (memM c l e).val = decide (e ∈ l) := by
  unfold memM
  rw [anyM_val 0 _ (fun e' => decide (e' = e)) (fun e' => rfl)]
  convert any_eq_decide_mem e l

theorem memM_cost (l : List (ν × ν)) (e : ν × ν) : (memM c l e).cost = memC c l e := by
  unfold memM memC
  rw [anyM_cost 0 _ (fun e' => 1 + pc c e + pc c e') (fun e' => rfl)]
  simp

/-- Full-scan membership of a label. -/
def memNM (l : List ν) (x : ν) : Costed Bool :=
  anyM 0 (fun y => do tick (1 + c x + c y); Pure.pure (decide (y = x))) l

theorem memNM_val (l : List ν) (x : ν) : (memNM c l x).val = decide (x ∈ l) := by
  unfold memNM
  rw [anyM_val 0 _ (fun y => decide (y = x)) (fun y => rfl)]
  exact any_eq_decide_mem x l

theorem memNM_cost (l : List ν) (x : ν) : (memNM c l x).cost = memNC c l x := by
  unfold memNM memNC
  rw [anyM_cost 0 _ (fun y => 1 + c x + c y) (fun y => rfl)]
  simp

/-- Deciding `ResL U a b`: build the two pairs, three scans. -/
def resM (U : List (ν × ν)) (a b : ν) : Costed Bool := do
  tick (pc c (a, b) + pc c (b, a))
  let m1 ← memM c N.arcs (a, b)
  let m2 ← memM c U (a, b)
  let m3 ← memM c U (b, a)
  Pure.pure ((m1 && !m2) || m3)

theorem resM_val (U : List (ν × ν)) (a b : ν) : (N.resM c U a b).val = decide (N.ResL U a b) := by
  simp only [resM, bind_val, memM_val, pure_val, ResL]
  by_cases h1 : (a, b) ∈ N.arcs <;> by_cases h2 : (a, b) ∈ U <;> by_cases h3 : (b, a) ∈ U <;>
    simp [h1, h2, h3]

theorem resM_cost (U : List (ν × ν)) (a b : ν) : (N.resM c U a b).cost = N.resC c U a b := by
  simp only [resM, resC, bind_cost, tick_cost, memM_cost, memM_val, pure_cost]
  omega

/-! ### Layers -/

/-- `newFront`: a filter over the nodes; at every node two scans and one `any` of residual
tests. -/
def newFrontM (U : List (ν × ν)) (seen front : List ν) : Costed (List ν) :=
  filterM 1 (fun y => do
    let s1 ← memNM c seen y
    let s2 ← memNM c front y
    let r ← anyM 1 (fun x => N.resM c U x y) front
    Pure.pure (!s1 && !s2 && r)) N.nodes

theorem newFrontM_val (U : List (ν × ν)) (seen front : List ν) :
    (N.newFrontM c U seen front).val = N.newFront U seen front := by
  unfold newFrontM newFront
  rw [filterM_val 1 _ (fun y => decide (y ∉ seen ∧ y ∉ front ∧ front.any (fun x => decide (N.ResL U x y))))]
  intro y
  simp only [bind_val, memNM_val, pure_val]
  rw [anyM_val 1 _ (fun x => decide (N.ResL U x y)) (fun x => N.resM_val c U x y)]
  apply Bool.eq_iff_iff.mpr
  simp [and_assoc]

theorem newFrontM_cost (U : List (ν × ν)) (seen front : List ν) :
    (N.newFrontM c U seen front).cost = N.newFrontC c U seen front := by
  unfold newFrontM newFrontC
  rw [filterM_cost 1 _ (fun y => memNC c seen y + memNC c front y +
    (front.map (fun x => 1 + N.resC c U x y)).sum)]
  · congr 1
    apply List.map_congr_left
    intro y _
    omega
  · intro y
    simp only [bind_cost, memNM_cost, memNM_val, pure_cost]
    rw [anyM_cost 1 _ (fun x => N.resC c U x y) (fun x => N.resM_cost c U x y)]
    omega

/-- `layersAux`: fuel decrement, cons, `newFront`, append. -/
def layersAuxM (U : List (ν × ν)) : ℕ → List ν → List ν → Costed (List (List ν))
  | 0, _, front => do tick (front.length + 1); Pure.pure [front]
  | k + 1, seen, front => do
      tick (natC (k + 1) + front.length + 1)
      let nf ← N.newFrontM c U seen front
      tick (seen.length + front.length)
      let rest ← layersAuxM U k (seen ++ front) nf
      Pure.pure (front :: rest)

theorem layersAuxM_val (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    (N.layersAuxM c U k seen front).val = N.layersAux U k seen front
  | 0, _, _ => rfl
  | k + 1, seen, front => by
      simp only [layersAuxM, layersAux, bind_val, newFrontM_val, pure_val]
      rw [layersAuxM_val U k]

theorem layersAuxM_cost (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    (N.layersAuxM c U k seen front).cost = N.layersAuxC c U k seen front
  | 0, _, _ => by simp [layersAuxM, layersAuxC]
  | k + 1, seen, front => by
      simp only [layersAuxM, layersAuxC, bind_cost, tick_cost, newFrontM_cost,
        newFrontM_val, pure_cost]
      rw [layersAuxM_cost U k]
      omega

/-- `layers`: measure the node count, build `[s]`, run the rounds. -/
def layersM (U : List (ν × ν)) : Costed (List (List ν)) := do
  tick (N.nodes.length + 1 + c N.s)
  N.layersAuxM c U N.nodes.length [] [N.s]

theorem layersM_val (U : List (ν × ν)) : (N.layersM c U).val = N.layers U := by
  simp [layersM, layers, layersAuxM_val]

theorem layersM_cost (U : List (ν × ν)) : (N.layersM c U).cost = N.layersC c U := by
  simp [layersM, layersC, layersAuxM_cost]

/-- `seen`: the layers, then a flatten. -/
def seenM (U : List (ν × ν)) : Costed (List ν) := do
  let L ← N.layersM c U
  tick (L.length + L.flatten.length)
  Pure.pure L.flatten

theorem seenM_val (U : List (ν × ν)) : (N.seenM c U).val = N.seen U := by
  simp [seenM, seen, layersM_val]

theorem seenM_cost (U : List (ν × ν)) : (N.seenM c U).cost = N.seenC c U := by
  simp only [seenM, seenC, bind_cost, layersM_cost, layersM_val, tick_cost,
    pure_cost]
  omega

/-! ### Path extraction -/

def descendRM (U : List (ν × ν)) : List (List ν) → ν → Costed (List ν)
  | [], y => do tick 1; Pure.pure [y]
  | L :: rest, y => do
      tick 1
      let r ← findM 1 (fun x => N.resM c U x y) L
      match r with
      | some x => do
          let p ← descendRM U rest x
          Pure.pure (y :: p)
      | none => Pure.pure [y]

theorem descendRM_val (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y : ν),
    (N.descendRM c U rls y).val = N.descendR U rls y
  | [], y => rfl
  | L :: rest, y => by
      simp only [descendRM, descendR, bind_val]
      rw [findM_val 1 _ (fun x => decide (N.ResL U x y)) (fun x => N.resM_val c U x y)]
      cases L.find? (fun x => decide (N.ResL U x y)) with
      | none => rfl
      | some x => simp [descendRM_val U rest x]

theorem descendRM_cost (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y : ν),
    (N.descendRM c U rls y).cost = N.descendRC c U rls y
  | [], y => rfl
  | L :: rest, y => by
      simp only [descendRM, descendRC, bind_cost, tick_cost]
      rw [findM_cost 1 _ (fun x => N.resC c U x y) (fun x => N.resM_cost c U x y),
        findM_val 1 _ (fun x => decide (N.ResL U x y)) (fun x => N.resM_val c U x y)]
      cases L.find? (fun x => decide (N.ResL U x y)) with
      | none => simp
      | some x => simp only [bind_cost, descendRM_cost U rest x, pure_cost]; omega

def extractRM (U : List (ν × ν)) : List (List ν) → ν → Costed (List ν)
  | [], _ => do tick 1; Pure.pure []
  | L :: rest, y => do
      tick 1
      let m ← memNM c L y
      if m then N.descendRM c U rest y else extractRM U rest y

theorem extractRM_val (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y : ν),
    (N.extractRM c U rls y).val = N.extractR U rls y
  | [], y => rfl
  | L :: rest, y => by
      simp only [extractRM, extractR, bind_val, memNM_val]
      by_cases h : y ∈ L
      · simp [h, descendRM_val]
      · simp [h, extractRM_val U rest y]

theorem extractRM_cost (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y : ν),
    (N.extractRM c U rls y).cost = N.extractRC c U rls y
  | [], y => rfl
  | L :: rest, y => by
      simp only [extractRM, extractRC, bind_cost, tick_cost, memNM_cost, memNM_val]
      by_cases h : y ∈ L
      · simp [h, descendRM_cost]; omega
      · simp [h, extractRM_cost U rest y]; omega

/-- `augPath`: recompute the layers, reverse, extract, reverse. -/
def augPathM (U : List (ν × ν)) : Costed (List ν) := do
  let L ← N.layersM c U
  tick L.length
  let p ← N.extractRM c U L.reverse N.t
  tick p.length
  Pure.pure p.reverse

theorem augPathM_val (U : List (ν × ν)) : (N.augPathM c U).val = N.augPath U := by
  simp [augPathM, augPath, layersM_val, extractRM_val]

theorem augPathM_cost (U : List (ν × ν)) : (N.augPathM c U).cost = N.augPathC c U := by
  simp only [augPathM, augPathC, bind_cost, layersM_cost, layersM_val, tick_cost,
    extractRM_cost, extractRM_val, pure_cost]
  omega

/-! ### Augmentation -/

/-- `steps`: one cell per zipped pair. -/
def stepsM (p : List ν) : Costed (List (ν × ν)) := do tick p.length; Pure.pure (steps p)

omit [DecidableEq ν] in
theorem stepsM_val (p : List ν) : (stepsM p).val = steps p := rfl
omit [DecidableEq ν] in
theorem stepsM_cost (p : List ν) : (stepsM p).cost = p.length := by simp [stepsM]

/-- `augment`: the filter over `U` recomputes `steps p` and builds the swapped pair at every
element; then `steps p` again, the forward filter and the append. -/
def augmentM (U : List (ν × ν)) (p : List ν) : Costed (List (ν × ν)) := do
  let A ← filterM 1 (fun a => do
    let st ← stepsM p
    tick (1 + pc c (a.2, a.1))
    let m ← memM c st (a.2, a.1)
    Pure.pure (!m)) U
  let st ← stepsM p
  let B ← filterM 1 (fun e => memM c N.arcs e) st
  tick U.length
  Pure.pure (A ++ B)

theorem augmentM_val (U : List (ν × ν)) (p : List ν) : (N.augmentM c U p).val = N.augment U p := by
  unfold augmentM augment
  simp only [bind_val, stepsM_val, pure_val]
  rw [filterM_val 1 _ (fun a => decide ((a.2, a.1) ∉ steps p)) (fun a => by
      simp [bind_val, stepsM_val, memM_val]),
    filterM_val 1 _ (fun e => decide (e ∈ N.arcs)) (fun e => by simp [memM_val])]

theorem augmentM_cost (U : List (ν × ν)) (p : List ν) : (N.augmentM c U p).cost = N.augmentC c U p := by
  unfold augmentM augmentC
  simp only [bind_cost, stepsM_cost, stepsM_val, tick_cost, pure_cost]
  rw [filterM_cost 1 _ (fun a => p.length + (1 + pc c (a.2, a.1) + memC c (steps p) (a.2, a.1)))
      (fun a => by simp [bind_cost, stepsM_cost, stepsM_val, tick_cost, memM_cost]),
    filterM_cost 1 _ (fun e => memC c N.arcs e) (fun e => by simp [memM_cost])]
  have e1 : (U.map (fun a => 1 + (p.length + (1 + pc c (a.2, a.1) + memC c (steps p) (a.2, a.1))))).sum =
      (U.map (fun a => 1 + (p.length + 1) + pc c (a.2, a.1) + memC c (steps p) (a.2, a.1))).sum := by
    congr 1; apply List.map_congr_left; intro a _; omega
  rw [e1]
  omega

/-! ### The loop -/

def ffAuxM : ℕ → List (ν × ν) → Costed (List (ν × ν))
  | 0, U => do tick 1; Pure.pure U
  | f + 1, U => do
      tick (natC (f + 1) + 1)
      let S ← N.seenM c U
      let m ← memNM c S N.t
      if m then do
        let p ← N.augPathM c U
        let U' ← N.augmentM c U p
        ffAuxM f U'
      else Pure.pure U

theorem ffAuxM_val : ∀ (f : ℕ) (U : List (ν × ν)), (N.ffAuxM c f U).val = N.ffAux f U
  | 0, U => rfl
  | f + 1, U => by
      simp only [ffAuxM, ffAux, bind_val, seenM_val, memNM_val]
      by_cases h : N.t ∈ N.seen U
      · simp [h, augPathM_val, augmentM_val, ffAuxM_val f]
      · simp [h]

theorem ffAuxM_cost : ∀ (f : ℕ) (U : List (ν × ν)), (N.ffAuxM c f U).cost = N.ffAuxC c f U
  | 0, U => rfl
  | f + 1, U => by
      simp only [ffAuxM, ffAuxC, bind_cost, tick_cost, seenM_cost, seenM_val,
        memNM_cost, memNM_val]
      by_cases h : N.t ∈ N.seen U
      · simp [h, augPathM_cost, augPathM_val, augmentM_cost, augmentM_val, ffAuxM_cost f]
        omega
      · simp [h]; omega

/-- `maxflow`: measure the arc count, run the rounds. -/
def maxflowM : Costed (List (ν × ν)) := do
  tick (N.arcs.length + 1)
  N.ffAuxM c (N.arcs.length + 1) []

theorem maxflowM_val : (N.maxflowM c).val = N.maxflow := by simp [maxflowM, maxflow, ffAuxM_val]

theorem maxflowM_cost : (N.maxflowM c).cost = N.maxflowC c := by
  simp [maxflowM, maxflowC, ffAuxM_cost]

/-- **The maximum-flow cost function is the step count of the instrumented program**: the
instrumented program computes `maxflow` and executes exactly `maxflowC` primitive steps, hence
at most `flowBound n m L` of them. -/
theorem maxflowM_spec (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) :
    (N.maxflowM c).val = N.maxflow ∧ (N.maxflowM c).cost = N.maxflowC c ∧
      (N.maxflowM c).cost ≤ flowBound N.nodes.length N.arcs.length L :=
  ⟨N.maxflowM_val c, N.maxflowM_cost c, by rw [N.maxflowM_cost c]; exact N.maxflowC_le c hN L hL⟩

end Network
end DisequalityDispersion.Flow
