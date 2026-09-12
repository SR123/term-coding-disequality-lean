import FlowCost
import UnitFlowExec

/-! # Execution-linked cost of the Phase-A validity check: an instrumented program

The Phase-A executable validity check `Instance.isValid` (`EncodedSyntax.lean`) is
re-implemented as an instrumented program in the step-counting monad `Costed`
(`CostMonad.lean`), with the primitives and charges of `EncodingCost.lean` plus the
recomputations inside closures that `isValidC` omits and `FlowCost.isValidSurcharge` adds:
`γ.k = sources.length` is re-measured in `x < k`, `y < k` and inside every node closure,
`γ.m = symbols.length` and `args.length` inside every node closure, `nodes.length` is
measured and `range nodes.length` produced, and `nodes.length` is re-measured twice at every
test.  `&&` evaluates every operand (no laziness assumed).  `isValidM_val` and
`isValidM_cost` prove that the program computes `isValid` and executes exactly `isValidC'`
primitive steps. -/

namespace DisequalityDispersion.Encoded
namespace Instance

open DisequalityDispersion.Costed

variable (γ : Instance)

/-- Reading `l.getD j d`, charged `accessC l j`. -/
def getDM' {α : Type} (l : List α) (j : ℕ) (d : α) : Costed α := do
  tick (accessC l j); Pure.pure (l.getD j d)

@[simp] theorem getDM'_val {α : Type} (l : List α) (j : ℕ) (d : α) :
    (getDM' l j d).val = l.getD j d := rfl
@[simp] theorem getDM'_cost {α : Type} (l : List α) (j : ℕ) (d : α) :
    (getDM' l j d).cost = accessC l j := by simp [getDM']

/-- Pairwise scan deciding `l.Nodup`: every earlier entry is compared with every later one. -/
def nodupM : List ℕ → Costed Bool
  | [] => Pure.pure true
  | a :: l => do
      let m ← anyM 0 (fun b => do tick (natC a + natC b); Pure.pure (decide (b = a))) l
      let r ← nodupM l
      Pure.pure (!m && r)

theorem nodupM_val : ∀ (l : List ℕ), (nodupM l).val = decide l.Nodup
  | [] => by simp [nodupM]
  | a :: l => by
      simp only [nodupM, bind_val, pure_val, nodupM_val l]
      rw [anyM_val 0 _ (fun b => decide (b = a)) (fun b => rfl), Flow.Network.any_eq_decide_mem]
      simp [List.nodup_cons]

theorem nodupM_cost : ∀ (l : List ℕ), (nodupM l).cost = nodupC l
  | [] => rfl
  | a :: l => by
      simp only [nodupM, nodupC, bind_cost, pure_cost, nodupM_cost l, add_zero]
      rw [anyM_cost 0 _ (fun b => natC a + natC b) (fun b => by simp)]
      simp only [zero_add]

/-- `nodeOk j nd`: the bound comparisons and, for an application, the arity lookup and the
argument scan (no cell charge, as in `nodeOkC`). -/
def nodeOkM (j : ℕ) : Node → Costed Bool
  | .src i => do tick (natC i + natC γ.k); Pure.pure (decide (i < γ.k))
  | .app f args => do
      tick (natC f + natC γ.m)
      tick (accessC γ.symbols f)
      tick (natC args.length + natC (γ.arityOf f))
      let c ← allM 0 (fun a => do tick (natC a + natC j); Pure.pure (decide (a < j))) args
      Pure.pure (decide (f < γ.m) && decide (args.length = γ.arityOf f) && c)

theorem nodeOkM_val (j : ℕ) : ∀ (nd : Node), (γ.nodeOkM j nd).val = γ.nodeOk j nd
  | .src i => rfl
  | .app f args => by
      simp only [nodeOkM, nodeOk, bind_val, pure_val]
      rw [allM_val 0 _ (fun a => decide (a < j)) (fun a => rfl)]

theorem nodeOkM_cost (j : ℕ) : ∀ (nd : Node), (γ.nodeOkM j nd).cost = γ.nodeOkC j nd
  | .src i => by simp [nodeOkM, nodeOkC]
  | .app f args => by
      simp only [nodeOkM, nodeOkC, bind_cost, pure_cost, tick_cost, add_zero]
      rw [allM_cost 0 _ (fun a => natC a + natC j) (fun a => by simp)]
      simp only [zero_add, Nat.add_assoc]

/-- `nodesOk`: measure `nodes.length`, produce the range, then at every index read the node,
re-measure `k`, `m` and the argument count inside the closure, and check it. -/
def nodesOkM : Costed Bool := do
  tick (2 * γ.nodes.length)
  allM 1 (fun j => do
    let nd ← getDM' γ.nodes j (.src 0)
    tick (γ.sources.length + γ.symbols.length + argsLen nd)
    γ.nodeOkM j nd) (List.range γ.nodes.length)

theorem nodesOkM_val : γ.nodesOkM.val = γ.nodesOk := by
  simp only [nodesOkM, nodesOk, bind_val]
  rw [allM_val 1 _ (fun j => γ.nodeOk j (γ.nodes.getD j (.src 0))) (fun j => by
    simp only [bind_val, getDM'_val, nodeOkM_val])]

theorem nodesOkM_cost : γ.nodesOkM.cost = 2 * γ.nodes.length + γ.nodesOkC +
    (γ.nodes.map (fun nd => γ.sources.length + γ.symbols.length + argsLen nd)).sum := by
  simp only [nodesOkM, nodesOkC, bind_cost, tick_cost]
  rw [allM_cost 1 _ (fun j => accessC γ.nodes j +
      ((γ.sources.length + γ.symbols.length + argsLen (γ.nodes.getD j (.src 0))) +
        γ.nodeOkC j (γ.nodes.getD j (.src 0)))) (fun j => by
    simp only [bind_cost, tick_cost, getDM'_cost, getDM'_val, nodeOkM_cost])]
  have hs : ((List.range γ.nodes.length).map (fun j => 1 + (accessC γ.nodes j +
      ((γ.sources.length + γ.symbols.length + argsLen (γ.nodes.getD j (.src 0))) +
        γ.nodeOkC j (γ.nodes.getD j (.src 0)))))).sum =
      ((List.range γ.nodes.length).map (fun j => 1 + accessC γ.nodes j +
        γ.nodeOkC j (γ.nodes.getD j (.src 0)))).sum +
      ((List.range γ.nodes.length).map (fun j =>
        γ.sources.length + γ.symbols.length + argsLen (γ.nodes.getD j (.src 0)))).sum := by
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro j _
    omega
  have h3 := sum_range_getD γ.nodes (.src 0)
    (fun nd => γ.sources.length + γ.symbols.length + argsLen nd)
  rw [hs, h3, Nat.add_assoc]

/-- `guardOk`: every test is scanned, both nodes read (default `app 0 []`), built into `src`
nodes and compared. -/
def guardOkM : Costed Bool :=
  anyM 1 (fun ij => do
    let a ← getDM' γ.nodes ij.1 (.app 0 [])
    let b ← getDM' γ.nodes ij.2 (.app 0 [])
    tick (nodeC a + nodeC b + natC γ.x + natC γ.y)
    Pure.pure (decide (a = .src γ.x) && decide (b = .src γ.y))) γ.tests

theorem guardOkM_val : γ.guardOkM.val = γ.guardOk := by
  unfold guardOkM guardOk
  rw [anyM_val 1 _ (fun ij => decide (γ.nodes.getD ij.1 (.app 0 []) = .src γ.x) &&
    decide (γ.nodes.getD ij.2 (.app 0 []) = .src γ.y)) (fun ij => rfl)]

theorem guardOkM_cost : γ.guardOkM.cost = γ.guardC := by
  unfold guardOkM guardC
  rw [anyM_cost 1 _ (fun ij => accessC γ.nodes ij.1 + (accessC γ.nodes ij.2 +
    (nodeC (γ.nodes.getD ij.1 (.app 0 [])) + nodeC (γ.nodes.getD ij.2 (.app 0 [])) +
      natC γ.x + natC γ.y))) (fun ij => by simp)]
  simp only [Nat.add_assoc]

/-- **The instrumented validity check**, conjunct by conjunct as in `isValid` (every operand
of `&&` is evaluated). -/
def isValidM : Costed Bool := do
  tick γ.sources.length
  tick (natC γ.k + 1)
  let b2 ← nodupM γ.sources
  let syms ← mapM 1 (fun p : ℕ × ℕ => Pure.pure p.1) γ.symbols
  let b3 ← nodupM syms
  tick γ.sources.length
  tick (natC γ.x + natC γ.k)
  tick γ.sources.length
  tick (natC γ.y + natC γ.k)
  tick (natC γ.x + natC γ.y)
  let b7 ← γ.nodesOkM
  tick (γ.nodes.length + natC γ.t + natC γ.nodes.length)
  let b9 ← allM 1 (fun ij : ℕ × ℕ => do
      tick γ.nodes.length
      tick (natC ij.1 + natC γ.nodes.length)
      tick γ.nodes.length
      tick (natC ij.2 + natC γ.nodes.length)
      Pure.pure (decide (ij.1 < γ.nodes.length) && decide (ij.2 < γ.nodes.length))) γ.tests
  let b10 ← γ.guardOkM
  Pure.pure (decide (2 ≤ γ.k) && b2 && b3 && decide (γ.x < γ.k) && decide (γ.y < γ.k) &&
    decide (γ.x ≠ γ.y) && b7 && decide (γ.t < γ.nodes.length) && b9 && b10)

theorem isValidM_val : γ.isValidM.val = γ.isValid := by
  simp only [isValidM, isValid, bind_val, pure_val, nodupM_val, nodesOkM_val, guardOkM_val]
  rw [mapM_val 1 _ Prod.fst (fun p => rfl),
    allM_val 1 _ (fun ij : ℕ × ℕ => decide (ij.1 < γ.nodes.length) &&
      decide (ij.2 < γ.nodes.length)) (fun ij => rfl)]

theorem isValidM_cost : γ.isValidM.cost = γ.isValidC' := by
  simp only [isValidM, isValidC', isValidC, isValidSurcharge, bind_cost, pure_cost, tick_cost,
    nodupM_cost, nodesOkM_cost, guardOkM_cost]
  rw [mapM_val 1 _ Prod.fst (fun p => rfl), mapM_cost 1 _ (fun _ => 0) (fun p => rfl),
    allM_cost 1 _ (fun ij : ℕ × ℕ => γ.nodes.length + (natC ij.1 + natC γ.nodes.length +
      (γ.nodes.length + (natC ij.2 + natC γ.nodes.length)))) (fun ij => by simp)]
  have h1 : (γ.symbols.map (fun _ => 1 + 0)).sum = γ.symbols.length := by
    simp [List.map_const', List.sum_replicate]
  have h2 : (γ.tests.map (fun ij : ℕ × ℕ => 1 + (γ.nodes.length + (natC ij.1 +
      natC γ.nodes.length + (γ.nodes.length + (natC ij.2 + natC γ.nodes.length)))))).sum =
      (γ.tests.map (fun ij => 1 + natC ij.1 + natC ij.2 + 2 * natC γ.nodes.length)).sum +
        γ.tests.length * (2 * γ.nodes.length) := by
    have : (γ.tests.map (fun _ => 2 * γ.nodes.length)).sum = γ.tests.length * (2 * γ.nodes.length) := by
      simp [List.map_const', List.sum_replicate]
    rw [← this, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro ij _
    omega
  rw [h1, h2]
  omega

/-! ### The identifier table `canonIds` -/

/-- `sigWith ids nd`: the node is copied (`nodeC nd`, the surcharge) and each argument is
replaced by its identifier (`accessC ids a`); one cell for the constructor. -/
def sigWithM (ids : List ℕ) : Node → Costed Node
  | .src i => do tick 1; tick (nodeC (.src i)); Pure.pure (.src i)
  | .app f args => do
      tick 1
      tick (nodeC (.app f args))
      let as ← mapM 0 (fun a => getDM' ids a 0) args
      Pure.pure (.app f as)

theorem sigWithM_val (ids : List ℕ) : ∀ (nd : Node), (sigWithM ids nd).val = sigWith ids nd
  | .src i => rfl
  | .app f args => by
      simp only [sigWithM, sigWith, bind_val, pure_val]
      rw [mapM_val 0 _ (fun a => ids.getD a 0) (fun a => rfl)]

theorem sigWithM_cost (ids : List ℕ) : ∀ (nd : Node),
    (sigWithM ids nd).cost = sigC ids nd + nodeC nd
  | .src i => by simp [sigWithM, sigC]
  | .app f args => by
      simp only [sigWithM, sigC, bind_cost, pure_cost, tick_cost]
      rw [mapM_cost 0 _ (fun a => accessC ids a) (fun a => by simp)]
      simp only [zero_add]
      omega

/-- `firstIndex p n` with the predicate evaluated at every level (a full scan, as charged):
one cell per level, and every counter comparison charged `natC J + 1` for the outer bound
`J`. -/
def firstIndexM (J : ℕ) (pM : ℕ → Costed Bool) : ℕ → Costed ℕ
  | 0 => Pure.pure 0
  | n + 1 => do
      let r ← firstIndexM J pM n
      tick 1
      let b ← pM n
      tick (natC J + 1)
      Pure.pure (if r < n then r else if b then n else n + 1)

theorem firstIndexM_val (J : ℕ) (pM : ℕ → Costed Bool) (p : ℕ → Bool)
    (hp : ∀ i, (pM i).val = p i) : ∀ (n : ℕ), (firstIndexM J pM n).val = firstIndex p n
  | 0 => rfl
  | n + 1 => by
      simp only [firstIndexM, firstIndex, bind_val, pure_val, hp, firstIndexM_val J pM p hp n]

theorem firstIndexM_cost (J : ℕ) (pM : ℕ → Costed Bool) (pc : ℕ → ℕ)
    (hp : ∀ i, (pM i).cost = pc i) : ∀ (n : ℕ),
    (firstIndexM J pM n).cost = ((List.range n).map (fun i => 1 + pc i + (natC J + 1))).sum
  | 0 => rfl
  | n + 1 => by
      simp only [firstIndexM, bind_cost, pure_cost, tick_cost, hp, firstIndexM_cost J pM pc hp n,
        List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      omega

/-- `buildList step n`: at every step one range cell, the step, and the copy of the
accumulator by `acc ++ [_]`. -/
def buildListM {α : Type} (stepM : List α → ℕ → Costed α) : ℕ → Costed (List α)
  | 0 => Pure.pure []
  | n + 1 => do
      let acc ← buildListM stepM n
      tick 1
      let a ← stepM acc n
      tick acc.length
      Pure.pure (acc ++ [a])

theorem buildListM_val {α : Type} (stepM : List α → ℕ → Costed α) (step : List α → ℕ → α)
    (hs : ∀ acc j, (stepM acc j).val = step acc j) :
    ∀ (n : ℕ), (buildListM stepM n).val = buildList step n
  | 0 => rfl
  | n + 1 => by
      simp only [buildListM, bind_val, pure_val, hs, buildListM_val stepM step hs n,
        buildList_succ]

theorem buildListM_cost {α : Type} (stepM : List α → ℕ → Costed α) (step : List α → ℕ → α)
    (sc : List α → ℕ → ℕ) (hs : ∀ acc j, (stepM acc j).val = step acc j)
    (hc : ∀ acc j, (stepM acc j).cost = sc acc j) :
    ∀ (n : ℕ), (buildListM stepM n).cost =
      ((List.range n).map (fun j => 1 + sc (buildList step j) j + j)).sum
  | 0 => rfl
  | n + 1 => by
      simp only [buildListM, bind_cost, pure_cost, tick_cost, hc,
        buildListM_val stepM step hs n, buildListM_cost stepM step sc hs hc n, buildList_length,
        List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      omega

/-- `canonStep ids j`: read node `j`, form its signature, scan all `i < j` (read, signature,
compare the two signatures), then the final comparison and lookup. -/
def canonStepM (ids : List ℕ) (j : ℕ) : Costed ℕ := do
  let nd ← getDM' γ.nodes j (.src 0)
  let sg ← sigWithM ids nd
  let r ← firstIndexM j (fun i => do
      let nd' ← getDM' γ.nodes i (.src 0)
      let s ← sigWithM ids nd'
      tick (nodeC s + nodeC sg)
      Pure.pure (decide (s = sg))) j
  tick (natC j + natC r)
  let v ← getDM' ids r 0
  Pure.pure (if r < j then v else j)

theorem canonStepM_val (ids : List ℕ) (j : ℕ) : (γ.canonStepM ids j).val = γ.canonStep ids j := by
  simp only [canonStepM, canonStep, bind_val, pure_val, getDM'_val, sigWithM_val]
  rw [firstIndexM_val j _ (fun i => decide (sigWith ids (γ.nodes.getD i (.src 0)) =
    sigWith ids (γ.nodes.getD j (.src 0)))) (fun i => by simp only [bind_val, pure_val,
      getDM'_val, sigWithM_val])]

theorem canonStepM_cost (ids : List ℕ) (j : ℕ) : (γ.canonStepM ids j).cost =
    γ.canonStepC ids j + nodeC (γ.nodes.getD j (.src 0)) +
      ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum + j * (natC j + 1) := by
  simp only [canonStepM, canonStepC, bind_cost, pure_cost, tick_cost,
    getDM'_val, getDM'_cost, sigWithM_val, sigWithM_cost]
  rw [firstIndexM_val j _ (fun i => decide (sigWith ids (γ.nodes.getD i (.src 0)) =
    sigWith ids (γ.nodes.getD j (.src 0)))) (fun i => by simp only [bind_val, pure_val,
      getDM'_val, sigWithM_val])]
  rw [firstIndexM_cost j _ (fun i => accessC γ.nodes i + (sigC ids (γ.nodes.getD i (.src 0)) +
      nodeC (γ.nodes.getD i (.src 0)) + (nodeC (sigWith ids (γ.nodes.getD i (.src 0))) +
        nodeC (sigWith ids (γ.nodes.getD j (.src 0)))))) (fun i => by
    simp only [bind_cost, pure_cost, tick_cost, getDM'_val, getDM'_cost, sigWithM_val,
      sigWithM_cost, add_zero])]
  have hs : ((List.range j).map (fun i => 1 + (accessC γ.nodes i +
      (sigC ids (γ.nodes.getD i (.src 0)) + nodeC (γ.nodes.getD i (.src 0)) +
        (nodeC (sigWith ids (γ.nodes.getD i (.src 0))) +
          nodeC (sigWith ids (γ.nodes.getD j (.src 0)))))) + (natC j + 1))).sum =
      ((List.range j).map (fun i => 1 + accessC γ.nodes i + sigC ids (γ.nodes.getD i (.src 0)) +
        nodeC (sigWith ids (γ.nodes.getD i (.src 0))) +
        nodeC (sigWith ids (γ.nodes.getD j (.src 0))))).sum +
      ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum +
      ((List.range j).map (fun _ => natC j + 1)).sum := by
    rw [← List.sum_map_add, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro i _
    omega
  have hc : ((List.range j).map (fun _ => natC j + 1)).sum = j * (natC j + 1) := by
    simp [List.map_const', List.sum_replicate]
  rw [hs, hc]
  omega

/-- **The instrumented identifier table**: measure `nodes.length`, produce the range, and
build the table step by step. -/
def canonIdsM : Costed (List ℕ) := do
  tick (2 * γ.nodes.length)
  buildListM γ.canonStepM γ.nodes.length

theorem canonIdsM_val : γ.canonIdsM.val = γ.canonIds := by
  simp only [canonIdsM, canonIds, bind_val]
  exact buildListM_val _ _ γ.canonStepM_val _

theorem canonIdsM_cost : γ.canonIdsM.cost = γ.canonIdsC' := by
  simp only [canonIdsM, canonIdsC', canonIdsC, canonSurcharge, bind_cost, tick_cost]
  rw [buildListM_cost _ _ (fun acc j => γ.canonStepC acc j + nodeC (γ.nodes.getD j (.src 0)) +
      ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum + j * (natC j + 1))
      γ.canonStepM_val γ.canonStepM_cost]
  have hs : ((List.range γ.nodes.length).map (fun j =>
      1 + (γ.canonStepC (buildList γ.canonStep j) j + nodeC (γ.nodes.getD j (.src 0)) +
        ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum + j * (natC j + 1)) +
        j)).sum =
      ((List.range γ.nodes.length).map (fun j =>
        1 + γ.canonStepC (buildList γ.canonStep j) j)).sum +
      ((List.range γ.nodes.length).map (fun j =>
        j + j * (natC j + 1) + nodeC (γ.nodes.getD j (.src 0)) +
          ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum)).sum := by
    rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro j _
    omega
  rw [hs]
  omega

end Instance
end DisequalityDispersion.Encoded
