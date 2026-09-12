import UnitFlow
import EncodingCost

/-! # Bit cost of the augmenting-path algorithm

One cost function per executable definition of `UnitFlow.lean`, with the same
recursion shape, in the cost model of `EncodingCost.lean`: comparing, copying or
constructing a node label `x` costs `c x` (its code length), every list cell
visited by a scan costs `1` plus the work at that cell, appending or reversing a
list costs its length, measuring a length costs its length, and every operation
on a binary counter (the fuel of `layersAux`/`ffAux`) costs its bit length.

Operational rules charged (no compiler optimisation is assumed): arguments and
`let`-bound values are evaluated once before the call (call-by-value); `if` and
`match` evaluate only the selected branch; a closure re-evaluates its whole body
at every call, so a subexpression inside a `fun` is charged once per call — in
particular `augPath` recomputes `layers U` after `ffAux` has computed `seen U`,
and `augment` recomputes `steps p` inside the filter predicate; both are charged.
`maxflowC_le` bounds the total by an explicit polynomial in the number of nodes
`n`, the number of arcs `m` and a bound `L` on the label cost. -/

namespace DisequalityDispersion.Flow
namespace Network

open DisequalityDispersion.Encoded (sum_map_le_of_le natC natC_le_linear natC_mono)

variable {ν : Type} [DecidableEq ν] (N : Network ν) (c : ν → ℕ)

/-! ### Cost functions -/

/-- Code length of a pair of labels. -/
def pc (e : ν × ν) : ℕ := c e.1 + c e.2

/-- Scanning `l` for the pair `e`. -/
def memC (l : List (ν × ν)) (e : ν × ν) : ℕ := (l.map (fun e' => 1 + pc c e + pc c e')).sum

/-- Scanning `l` for the label `x`. -/
def memNC (l : List ν) (x : ν) : ℕ := (l.map (fun y => 1 + c x + c y)).sum

/-- Deciding `ResL U a b`: two pair constructions and three scans. -/
def resC (U : List (ν × ν)) (a b : ν) : ℕ :=
  pc c (a, b) + pc c (b, a) + memC c N.arcs (a, b) + memC c U (a, b) + memC c U (b, a)

/-- Cost of `newFront`. -/
def newFrontC (U : List (ν × ν)) (seen front : List ν) : ℕ :=
  (N.nodes.map (fun y => 1 + memNC c seen y + memNC c front y +
    (front.map (fun x => 1 + N.resC c U x y)).sum)).sum

/-- Cost of `layersAux` (one fuel decrement, one `newFront`, one append and one cons per
round). -/
def layersAuxC (U : List (ν × ν)) : ℕ → List ν → List ν → ℕ
  | 0, _, front => front.length + 1
  | k + 1, seen, front =>
      natC (k + 1) + front.length + 1 + N.newFrontC c U seen front + seen.length + front.length +
        layersAuxC U k (seen ++ front) (N.newFront U seen front)

/-- Cost of `layers`: measuring `nodes.length`, building `[s]`, then the rounds. -/
def layersC (U : List (ν × ν)) : ℕ :=
  N.nodes.length + 1 + c N.s + N.layersAuxC c U N.nodes.length [] [N.s]

/-- Cost of `seen` (the layers, then flattening). -/
def seenC (U : List (ν × ν)) : ℕ :=
  N.layersC c U + (N.layers U).length + (N.layers U).flatten.length

/-- Cost of `descendR`. -/
def descendRC (U : List (ν × ν)) : List (List ν) → ν → ℕ
  | [], _ => 1
  | L :: rest, y =>
      1 + (L.map (fun x => 1 + N.resC c U x y)).sum +
        (match L.find? (fun x => decide (N.ResL U x y)) with
          | some x => descendRC U rest x
          | none => 0)

/-- Cost of `extractR`. -/
def extractRC (U : List (ν × ν)) : List (List ν) → ν → ℕ
  | [], _ => 1
  | L :: rest, y =>
      1 + memNC c L y + (if y ∈ L then N.descendRC c U rest y else extractRC U rest y)

/-- Cost of `augPath`: the layers are recomputed, then two reversals and the extraction. -/
def augPathC (U : List (ν × ν)) : ℕ :=
  N.layersC c U + (N.layers U).length + N.extractRC c U (N.layers U).reverse N.t +
    (N.extractR U (N.layers U).reverse N.t).length

/-- Cost of `augment`: the filter predicate recomputes `steps p` (charged `p.length + 1`) and
builds the swapped pair at every element; then the forward steps are checked against the arcs
and the two lists are appended. -/
def augmentC (U : List (ν × ν)) (p : List ν) : ℕ :=
  p.length + (U.map (fun a => 1 + (p.length + 1) + pc c (a.2, a.1) + memC c (steps p) (a.2, a.1))).sum +
    ((steps p).map (fun e => 1 + memC c N.arcs e)).sum + U.length

/-- Cost of `ffAux`: a fuel decrement, the reachable set, the membership test and, when `t` is
reached, the path, the augmentation and the next round. -/
def ffAuxC : ℕ → List (ν × ν) → ℕ
  | 0, _ => 1
  | f + 1, U =>
      natC (f + 1) + 1 + N.seenC c U + memNC c (N.seen U) N.t +
        (if N.t ∈ N.seen U then
          N.augPathC c U + N.augmentC c U (N.augPath U) + ffAuxC f (N.augment U (N.augPath U))
         else 0)

/-- Cost of `maxflow`: measuring `arcs.length`, then the rounds. -/
def maxflowC : ℕ := N.arcs.length + 1 + N.ffAuxC c (N.arcs.length + 1) []

/-! ### Structural facts used by the bounds -/

omit [DecidableEq ν] in
theorem length_le_of_nodup_subset (l : List ν) (hl : l.Nodup) (hsub : ∀ x ∈ l, x ∈ N.nodes) :
    l.length ≤ N.nodes.length := by
  classical
  rw [← List.toFinset_card_of_nodup hl]
  exact (Finset.card_le_card (fun y hy => List.mem_toFinset.mpr
    (hsub y (List.mem_toFinset.mp hy)))).trans (List.toFinset_card_le _)

theorem good_length_le (U : List (ν × ν)) (hU : N.Good U) : U.length ≤ N.arcs.length := by
  rw [← List.toFinset_card_of_nodup hU.nodup]
  exact (Finset.card_le_card (fun a ha => List.mem_toFinset.mpr
    (hU.flow.sub a ha))).trans (List.toFinset_card_le _)

theorem layersAux_length (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    (N.layersAux U k seen front).length = k + 1
  | 0, _, _ => rfl
  | k + 1, seen, front => by
      simp only [layersAux, List.length_cons]
      rw [layersAux_length U k]

theorem layers_length (U : List (ν × ν)) : (N.layers U).length = N.nodes.length + 1 :=
  N.layersAux_length U _ _ _

theorem seen_length_le (U : List (ν × ν)) (hN : N.Ok) : (N.seen U).length ≤ N.nodes.length :=
  N.length_le_of_nodup_subset _ (N.seen_nodup U hN.nodes_nodup) (N.seen_subset U hN.s_mem)

theorem mem_descendR (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y z : ν),
    z ∈ N.descendR U rls y → z = y ∨ z ∈ rls.flatten
  | [], y, z, h => by simp [descendR] at h; exact Or.inl h
  | L :: rest, y, z, h => by
      simp only [descendR, List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · cases hf : L.find? (fun x => decide (N.ResL U x y)) with
        | none => rw [hf] at h; simp at h
        | some x =>
            rw [hf] at h
            rcases mem_descendR U rest x z h with rfl | h'
            · exact Or.inr (by simp [List.mem_of_find?_eq_some hf])
            · exact Or.inr (by simp [h'])

theorem mem_extractR (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y z : ν),
    z ∈ N.extractR U rls y → z ∈ rls.flatten
  | [], y, z, h => by simp [extractR] at h
  | L :: rest, y, z, h => by
      simp only [extractR] at h
      split_ifs at h with hy
      · rcases N.mem_descendR U rest y z h with rfl | h'
        · simp [hy]
        · simp [h']
      · simp [mem_extractR U rest y z h]

theorem augPath_subset (U : List (ν × ν)) (hN : N.Ok) : ∀ x ∈ N.augPath U, x ∈ N.nodes := by
  intro x hx
  unfold augPath at hx
  rw [List.mem_reverse] at hx
  have := N.mem_extractR U _ _ _ hx
  have h2 : x ∈ N.seen U := (List.reverse_perm _).flatten.mem_iff.mp this
  exact N.seen_subset U hN.s_mem x h2

theorem augPath_length_le (U : List (ν × ν)) (hN : N.Ok) (ht : N.t ∈ N.seen U) :
    (N.augPath U).length ≤ N.nodes.length :=
  N.length_le_of_nodup_subset _ (N.augPath_spec U hN.nodes_nodup ht).1 (N.augPath_subset U hN)

omit [DecidableEq ν] in
theorem steps_length (p : List ν) : (steps p).length ≤ p.length := by
  unfold steps
  rw [List.length_zip]
  exact min_le_left _ _

/-! ### Polynomial bounds -/

/-- Bound on `resC` when `|U| ≤ m`. -/
def resB (m L : ℕ) : ℕ := 4 * L + 3 * m * (1 + 4 * L)
/-- Bound on `newFrontC`. -/
def frontB (n m L : ℕ) : ℕ := n * (1 + 2 * n * (1 + 2 * L) + n * (1 + resB m L))
/-- Bound on one round of `layersAux` (fuel `≤ n`). -/
def layerRoundB (n m L : ℕ) : ℕ := 5 * n + 4 + frontB n m L
/-- Bound on `layersC`. -/
def layersB (n m L : ℕ) : ℕ := n + 1 + L + (n + 1) * layerRoundB n m L
/-- Bound on `seenC`. -/
def seenB (n m L : ℕ) : ℕ := layersB n m L + 2 * n + 1
/-- Bound on `augPathC`. -/
def augPathB (n m L : ℕ) : ℕ := layersB n m L + 3 * (n + 1) + 1 + n * (2 + 2 * L + resB m L) + n
/-- Bound on `augmentC`. -/
def augmentB (n m L : ℕ) : ℕ :=
  n + m * (2 + n + 2 * L + n * (1 + 4 * L)) + n * (1 + m * (1 + 4 * L)) + m
/-- Bound on one round of `ffAux` (fuel `≤ m + 1`). -/
def roundB (n m L : ℕ) : ℕ :=
  2 * m + 5 + 1 + seenB n m L + n * (1 + 2 * L) + augPathB n m L + augmentB n m L
/-- Bound on `maxflowC`. -/
def flowBound (n m L : ℕ) : ℕ := m + 1 + 1 + (m + 1) * roundB n m L

omit [DecidableEq ν] in
theorem pc_le (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (e : ν × ν) (h1 : e.1 ∈ N.nodes)
    (h2 : e.2 ∈ N.nodes) : pc c e ≤ 2 * L := by
  unfold pc
  have := hL _ h1; have := hL _ h2; omega

omit [DecidableEq ν] in
theorem memC_le (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (l : List (ν × ν)) (e : ν × ν)
    (hl : ∀ e' ∈ l, e'.1 ∈ N.nodes ∧ e'.2 ∈ N.nodes) (h1 : e.1 ∈ N.nodes) (h2 : e.2 ∈ N.nodes) :
    memC c l e ≤ l.length * (1 + 4 * L) := by
  unfold memC
  apply sum_map_le_of_le
  intro e' he'
  have := N.pc_le c L hL e h1 h2
  have := N.pc_le c L hL e' (hl e' he').1 (hl e' he').2
  omega

omit [DecidableEq ν] in
theorem memNC_le (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (l : List ν) (x : ν)
    (hl : ∀ y ∈ l, y ∈ N.nodes) (hx : x ∈ N.nodes) : memNC c l x ≤ l.length * (1 + 2 * L) := by
  unfold memNC
  apply sum_map_le_of_le
  intro y hy
  have := hL _ hx; have := hL _ (hl y hy); omega

omit [DecidableEq ν] in
theorem resC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) (a b : ν) (ha : a ∈ N.nodes)
    (hb : b ∈ N.nodes) : N.resC c U a b ≤ resB N.arcs.length L := by
  unfold resC resB
  have h1 := N.memC_le c L hL N.arcs (a, b) hN.arcs_mem ha hb
  have h2 := N.memC_le c L hL U (a, b) (fun e he => hN.arcs_mem e (hU e he)) ha hb
  have h3 := N.memC_le c L hL U (b, a) (fun e he => hN.arcs_mem e (hU e he)) hb ha
  have h4 := N.pc_le c L hL (a, b) ha hb
  have h5 := N.pc_le c L hL (b, a) hb ha
  have := Nat.mul_le_mul_right (1 + 4 * L) hm
  nlinarith

omit [DecidableEq ν] in
theorem newFrontC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) (seen front : List ν)
    (hs : ∀ y ∈ seen, y ∈ N.nodes) (hf : ∀ y ∈ front, y ∈ N.nodes)
    (hsl : seen.length ≤ N.nodes.length) (hfl : front.length ≤ N.nodes.length) :
    N.newFrontC c U seen front ≤ frontB N.nodes.length N.arcs.length L := by
  unfold newFrontC frontB
  apply sum_map_le_of_le
  intro y hy
  have h1 := N.memNC_le c L hL seen y hs hy
  have h2 := N.memNC_le c L hL front y hf hy
  have h3 : (front.map (fun x => 1 + N.resC c U x y)).sum ≤
      front.length * (1 + resB N.arcs.length L) := by
    apply sum_map_le_of_le
    intro x hx
    have := N.resC_le c hN L hL U hU hm x y (hf x hx) hy
    omega
  have e1 := Nat.mul_le_mul_right (1 + 2 * L) hsl
  have e2 := Nat.mul_le_mul_right (1 + 2 * L) hfl
  have e3 := Nat.mul_le_mul_right (1 + resB N.arcs.length L) hfl
  nlinarith

theorem layersAuxC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) :
    ∀ (k : ℕ) (seen front : List ν), seen.Nodup → front.Nodup → (∀ y ∈ front, y ∉ seen) →
      (∀ y ∈ seen, y ∈ N.nodes) → (∀ y ∈ front, y ∈ N.nodes) →
      k ≤ N.nodes.length →
      N.layersAuxC c U k seen front ≤ (k + 1) * layerRoundB N.nodes.length N.arcs.length L
  | 0, seen, front, _, hfn, _, _, hf, _ => by
      simp only [layersAuxC, layerRoundB]
      have := N.length_le_of_nodup_subset front hfn hf
      nlinarith
  | k + 1, seen, front, hsn, hfn, hdisj, hs, hf, hk => by
      simp only [layersAuxC]
      have hsl := N.length_le_of_nodup_subset seen hsn hs
      have hfl := N.length_le_of_nodup_subset front hfn hf
      have hfuel : natC (k + 1) ≤ 2 * N.nodes.length + 3 := by
        have := natC_le_linear (k + 1); omega
      have h1 := N.newFrontC_le c hN L hL U hU hm seen front hs hf hsl hfl
      have h2 := layersAuxC_le hN L hL U hU hm k (seen ++ front) (N.newFront U seen front)
        (List.nodup_append.mpr ⟨hsn, hfn, fun a ha b hb hab => hdisj b hb (hab ▸ ha)⟩)
        (hN.nodes_nodup.filter _)
        (fun y hy => by
          rw [N.mem_newFront] at hy
          simp only [List.mem_append, not_or]
          exact ⟨hy.2.1, hy.2.2.1⟩)
        (fun y hy => by
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · exact hs y hy
          · exact hf y hy)
        (fun y hy => ((N.mem_newFront U _ _ y).mp hy).1) (by omega)
      unfold layerRoundB at h2 ⊢
      nlinarith

theorem layersC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) :
    N.layersC c U ≤ layersB N.nodes.length N.arcs.length L := by
  unfold layersC layersB
  have h1 := N.layersAuxC_le c hN L hL U hU hm N.nodes.length [] [N.s] List.nodup_nil
    (List.nodup_singleton _) (by simp) (by simp) (by simpa using hN.s_mem) le_rfl
  have h2 := hL _ hN.s_mem
  omega

theorem seenC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) :
    N.seenC c U ≤ seenB N.nodes.length N.arcs.length L := by
  unfold seenC seenB
  have h1 := N.layersC_le c hN L hL U hU hm
  have h2 := N.layers_length U
  have h3 := N.seen_length_le U hN
  unfold seen at h3
  omega

theorem descendRC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) :
    ∀ (rls : List (List ν)) (y : ν), (∀ Ly ∈ rls, ∀ x ∈ Ly, x ∈ N.nodes) → y ∈ N.nodes →
      N.descendRC c U rls y ≤ rls.length + 1 + rls.flatten.length * (1 + resB N.arcs.length L)
  | [], y, _, _ => by simp [descendRC]
  | Ly :: rest, y, hr, hy => by
      simp only [descendRC, List.length_cons, List.flatten_cons, List.length_append]
      have h1 : (Ly.map (fun x => 1 + N.resC c U x y)).sum ≤
          Ly.length * (1 + resB N.arcs.length L) := by
        apply sum_map_le_of_le
        intro x hx
        have := N.resC_le c hN L hL U hU hm x y (hr Ly (by simp) x hx) hy
        omega
      have h2 : (match Ly.find? (fun x => decide (N.ResL U x y)) with
          | some x => N.descendRC c U rest x
          | none => 0) ≤ rest.length + 1 + rest.flatten.length * (1 + resB N.arcs.length L) := by
        cases hf : Ly.find? (fun x => decide (N.ResL U x y)) with
        | none => simp
        | some x =>
            simp only
            exact descendRC_le hN L hL U hU hm rest x
              (fun L' hL' => hr L' (List.mem_cons_of_mem _ hL'))
              (hr Ly (by simp) x (List.mem_of_find?_eq_some hf))
      nlinarith

theorem extractRC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) :
    ∀ (rls : List (List ν)) (y : ν), (∀ Ly ∈ rls, ∀ x ∈ Ly, x ∈ N.nodes) → y ∈ N.nodes →
      N.extractRC c U rls y ≤
        2 * rls.length + 1 + rls.flatten.length * (2 + 2 * L + resB N.arcs.length L)
  | [], y, _, _ => by simp [extractRC]
  | Ly :: rest, y, hr, hy => by
      simp only [extractRC, List.length_cons, List.flatten_cons, List.length_append]
      have h1 := N.memNC_le c L hL Ly y (hr Ly (by simp)) hy
      have hr' : ∀ L' ∈ rest, ∀ x ∈ L', x ∈ N.nodes :=
        fun L' hL' => hr L' (List.mem_cons_of_mem _ hL')
      split_ifs with hyL
      · have h2 := N.descendRC_le c hN L hL U hU hm rest y hr' hy
        nlinarith
      · have h2 := extractRC_le hN L hL U hU hm rest y hr' hy
        nlinarith

theorem augPathC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) (ht : N.t ∈ N.seen U) :
    N.augPathC c U ≤ augPathB N.nodes.length N.arcs.length L := by
  unfold augPathC augPathB
  have h0 := N.layersC_le c hN L hL U hU hm
  have h1 := N.layers_length U
  have hsub : ∀ Ly ∈ (N.layers U).reverse, ∀ x ∈ Ly, x ∈ N.nodes := by
    intro Ly hLy x hx
    rw [List.mem_reverse] at hLy
    exact N.seen_subset U hN.s_mem x (List.mem_flatten.mpr ⟨Ly, hLy, hx⟩)
  have h2 := N.extractRC_le c hN L hL U hU hm (N.layers U).reverse N.t hsub hN.t_mem
  have h3 : (N.layers U).reverse.flatten.length ≤ N.nodes.length := by
    rw [(List.reverse_perm _).flatten.length_eq]
    exact N.seen_length_le U hN
  have h4 : (N.extractR U (N.layers U).reverse N.t).length ≤ N.nodes.length := by
    have := N.augPath_length_le U hN ht
    unfold augPath at this
    rwa [List.length_reverse] at this
  rw [List.length_reverse, h1] at h2
  have := Nat.mul_le_mul_right (2 + 2 * L + resB N.arcs.length L) h3
  omega

omit [DecidableEq ν] in
theorem augmentC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) (U : List (ν × ν))
    (hU : ∀ a ∈ U, a ∈ N.arcs) (hm : U.length ≤ N.arcs.length) (p : List ν)
    (hp : ∀ x ∈ p, x ∈ N.nodes) (hpl : p.length ≤ N.nodes.length) :
    N.augmentC c U p ≤ augmentB N.nodes.length N.arcs.length L := by
  unfold augmentC augmentB
  have hst : ∀ e ∈ steps p, e.1 ∈ N.nodes ∧ e.2 ∈ N.nodes :=
    fun e he => ⟨hp _ (mem_steps he).1, hp _ (mem_steps he).2⟩
  have hsl : (steps p).length ≤ N.nodes.length := (steps_length p).trans hpl
  have h1 : (U.map (fun a => 1 + (p.length + 1) + pc c (a.2, a.1) + memC c (steps p) (a.2, a.1))).sum ≤
      U.length * (2 + N.nodes.length + 2 * L + N.nodes.length * (1 + 4 * L)) := by
    apply sum_map_le_of_le
    intro a ha
    have := N.memC_le c L hL (steps p) (a.2, a.1) hst (hN.arcs_mem a (hU a ha)).2
      (hN.arcs_mem a (hU a ha)).1
    have := N.pc_le c L hL (a.2, a.1) (hN.arcs_mem a (hU a ha)).2 (hN.arcs_mem a (hU a ha)).1
    have := Nat.mul_le_mul_right (1 + 4 * L) hsl
    omega
  have h2 : ((steps p).map (fun e => 1 + memC c N.arcs e)).sum ≤
      (steps p).length * (1 + N.arcs.length * (1 + 4 * L)) := by
    apply sum_map_le_of_le
    intro e he
    have := N.memC_le c L hL N.arcs e hN.arcs_mem (hst e he).1 (hst e he).2
    omega
  have e1 := Nat.mul_le_mul_right (2 + N.nodes.length + 2 * L + N.nodes.length * (1 + 4 * L)) hm
  have e2 := Nat.mul_le_mul_right (1 + N.arcs.length * (1 + 4 * L)) hsl
  omega

theorem good_augment (hN : N.Ok) (U : List (ν × ν)) (hU : N.Good U) (ht : N.t ∈ N.seen U) :
    N.Good (N.augment U (N.augPath U)) := by
  obtain ⟨hnd, hch, hh, hl⟩ := N.augPath_spec U hN.nodes_nodup ht
  exact ⟨(N.augment_flow hN U _ hU.flow hnd hch hh hl).1,
    N.augment_nodup hN U _ hU.nodup (fun a ha => hU.flow.sub a (List.mem_toFinset.mpr ha)) hnd hch⟩

theorem ffAuxC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) :
    ∀ (f : ℕ) (U : List (ν × ν)), N.Good U → f ≤ N.arcs.length + 1 →
      N.ffAuxC c f U ≤ 1 + f * roundB N.nodes.length N.arcs.length L
  | 0, _, _, _ => by simp [ffAuxC]
  | f + 1, U, hU, hf => by
      simp only [ffAuxC]
      have hfuel : natC (f + 1) ≤ 2 * N.arcs.length + 5 := by
        have := natC_le_linear (f + 1); omega
      have hsub : ∀ a ∈ U, a ∈ N.arcs := fun a ha => hU.flow.sub a (List.mem_toFinset.mpr ha)
      have hm := N.good_length_le U hU
      have h1 := N.seenC_le c hN L hL U hsub hm
      have h2 := N.memNC_le c L hL (N.seen U) N.t (N.seen_subset U hN.s_mem) hN.t_mem
      have h2' := Nat.mul_le_mul_right (1 + 2 * L) (N.seen_length_le U hN)
      unfold roundB
      split_ifs with ht
      · have h3 := N.augPathC_le c hN L hL U hsub hm ht
        have h4 := N.augmentC_le c hN L hL U hsub hm (N.augPath U) (N.augPath_subset U hN)
          (N.augPath_length_le U hN ht)
        have h5 := ffAuxC_le hN L hL f _ (N.good_augment hN U hU ht) (by omega)
        unfold roundB at h5
        nlinarith
      · nlinarith

/-- **Polynomial bit cost of the maximum-flow computation.** -/
theorem maxflowC_le (hN : N.Ok) (L : ℕ) (hL : ∀ x ∈ N.nodes, c x ≤ L) :
    N.maxflowC c ≤ flowBound N.nodes.length N.arcs.length L := by
  unfold maxflowC flowBound
  have := N.ffAuxC_le c hN L hL _ [] N.good_nil le_rfl
  omega

end Network
end DisequalityDispersion.Flow
