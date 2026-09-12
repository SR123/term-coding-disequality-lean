import Core

/-! # Unit-capacity flows on finite digraphs and the augmenting-path algorithm

A `Network` is a finite digraph (lists of nodes and arcs) with a source `s`
and a sink `t`; a flow is a set of arcs (unit capacities) with conservation at
every node other than `s, t`; its value is the out-degree of `s`.

* `cut_identity` / `value_le_cap`: flow across a cut, weak duality;
* `augment_isFlow` / `value_augment`: augmenting along a residual path;
* `layers` (breadth-first residual reachability) with closure and path extraction;
* `maxflow`: the executable augmenting-path loop, with `maxflow_spec`: the result is a
  flow whose value equals the capacity of the residual-reachable cut, hence maximal.

Everything is list-based and executable; proofs use the `Finset` of the flow. -/

namespace DisequalityDispersion.Flow

variable {ν : Type} [DecidableEq ν]

structure Network (ν : Type) where
  nodes : List ν
  arcs : List (ν × ν)
  s : ν
  t : ν

namespace Network
variable (N : Network ν)

/-- Well-formedness: no antiparallel arcs, nothing enters `s`, nothing leaves `t`. -/
structure Ok : Prop where
  nodes_nodup : N.nodes.Nodup
  arcs_nodup : N.arcs.Nodup
  st : N.s ≠ N.t
  s_mem : N.s ∈ N.nodes
  t_mem : N.t ∈ N.nodes
  arcs_mem : ∀ a ∈ N.arcs, a.1 ∈ N.nodes ∧ a.2 ∈ N.nodes
  no_anti : ∀ a ∈ N.arcs, (a.2, a.1) ∉ N.arcs
  no_into_s : ∀ a ∈ N.arcs, a.2 ≠ N.s
  no_out_t : ∀ a ∈ N.arcs, a.1 ≠ N.t

/-! ### Degrees, flows, value -/

def indeg (U : Finset (ν × ν)) (x : ν) : ℕ := (U.filter (fun a => a.2 = x)).card
def outdeg (U : Finset (ν × ν)) (x : ν) : ℕ := (U.filter (fun a => a.1 = x)).card

structure IsFlow (U : Finset (ν × ν)) : Prop where
  sub : ∀ a ∈ U, a ∈ N.arcs
  cons : ∀ x, x ≠ N.s → x ≠ N.t → indeg U x = outdeg U x

def value (U : Finset (ν × ν)) : ℕ := outdeg U N.s

theorem indeg_s_eq_zero (hN : N.Ok) {U : Finset (ν × ν)} (hU : N.IsFlow U) : indeg U N.s = 0 := by
  unfold indeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha h
  exact hN.no_into_s a (hU.sub a ha) h

/-- Capacity of a node set `S` (arcs leaving `S`). -/
def cap (S : Finset ν) : ℕ := (N.arcs.toFinset.filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)).card

/-! ### The flow across a cut -/

theorem sum_outdeg (U : Finset (ν × ν)) (S : Finset ν) :
    ∑ x ∈ S, outdeg U x = (U.filter (fun a => a.1 ∈ S)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S)]
  · apply Finset.sum_congr rfl
    intro x hx
    unfold outdeg
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hax⟩; exact ⟨⟨ha, hax ▸ hx⟩, hax⟩
    · rintro ⟨⟨ha, _⟩, hax⟩; exact ⟨ha, hax⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    exact ha.2

theorem sum_indeg (U : Finset (ν × ν)) (S : Finset ν) :
    ∑ x ∈ S, indeg U x = (U.filter (fun a => a.2 ∈ S)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := S)]
  · apply Finset.sum_congr rfl
    intro x hx
    unfold indeg
    congr 1
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hax⟩; exact ⟨⟨ha, hax ▸ hx⟩, hax⟩
    · rintro ⟨⟨ha, _⟩, hax⟩; exact ⟨ha, hax⟩
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
    exact ha.2

/-- Flow conservation summed over an `s`–`t` cut. -/
theorem sum_cut (hN : N.Ok) {U : Finset (ν × ν)} (hU : N.IsFlow U) (S : Finset ν)
    (hs : N.s ∈ S) (ht : N.t ∉ S) :
    ∑ x ∈ S, outdeg U x = ∑ x ∈ S, indeg U x + N.value U := by
  rw [← Finset.add_sum_erase S _ hs, ← Finset.add_sum_erase S _ hs, N.indeg_s_eq_zero hN hU]
  have : ∑ x ∈ S.erase N.s, outdeg U x = ∑ x ∈ S.erase N.s, indeg U x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_erase] at hx
    exact (hU.cons x hx.1 (fun h => ht (h ▸ hx.2))).symm
  unfold value
  omega

/-- **Cut identity**: `value + |U ∩ (Sᶜ → S)| = |U ∩ (S → Sᶜ)|`. -/
theorem cut_identity (hN : N.Ok) {U : Finset (ν × ν)} (hU : N.IsFlow U) (S : Finset ν)
    (hs : N.s ∈ S) (ht : N.t ∉ S) :
    N.value U + (U.filter (fun a => a.1 ∉ S ∧ a.2 ∈ S)).card =
      (U.filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)).card := by
  have h := N.sum_cut hN hU S hs ht
  rw [sum_outdeg, sum_indeg] at h
  have h1 := Finset.filter_card_add_filter_neg_card_eq_card (s := U.filter (fun a => a.1 ∈ S))
    (fun a => a.2 ∈ S)
  have h2 := Finset.filter_card_add_filter_neg_card_eq_card (s := U.filter (fun a => a.2 ∈ S))
    (fun a => a.1 ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter] at h1 h2
  have e : (U.filter (fun a => a.2 ∈ S ∧ a.1 ∈ S)) = U.filter (fun a => a.1 ∈ S ∧ a.2 ∈ S) := by
    ext a; simp [and_comm]
  have e2 : (U.filter (fun a => a.2 ∈ S ∧ a.1 ∉ S)) = U.filter (fun a => a.1 ∉ S ∧ a.2 ∈ S) := by
    ext a; simp [and_comm]
  rw [e, e2] at h2
  omega

/-- **Weak duality**: `value U ≤ cap S` for every `s`–`t` cut. -/
theorem value_le_cap (hN : N.Ok) {U : Finset (ν × ν)} (hU : N.IsFlow U) (S : Finset ν)
    (hs : N.s ∈ S) (ht : N.t ∉ S) : N.value U ≤ N.cap S := by
  have h := N.cut_identity hN hU S hs ht
  unfold cap
  have : (U.filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)).card ≤
      (N.arcs.toFinset.filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)).card := by
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨List.mem_toFinset.mpr (hU.sub a ha.1), ha.2⟩
  omega

/-- The value is at most the number of arcs. -/
theorem value_le_arcs {U : Finset (ν × ν)} (hU : N.IsFlow U) :
    N.value U ≤ N.arcs.length := by
  unfold value outdeg
  calc (U.filter (fun a => a.1 = N.s)).card ≤ U.card := Finset.card_filter_le _ _
    _ ≤ N.arcs.toFinset.card := Finset.card_le_card (fun a ha => List.mem_toFinset.mpr (hU.sub a ha))
    _ ≤ N.arcs.length := List.toFinset_card_le _


/-! ### Residual steps and breadth-first layers -/

/-- Residual step on list flows: an unused arc forward, or a used arc backward. -/
def ResL (U : List (ν × ν)) (a b : ν) : Prop := ((a, b) ∈ N.arcs ∧ (a, b) ∉ U) ∨ (b, a) ∈ U

instance (U : List (ν × ν)) (a b : ν) : Decidable (N.ResL U a b) := by
  unfold ResL; infer_instance

/-- Nodes reached for the first time from the frontier. -/
def newFront (U : List (ν × ν)) (seen front : List ν) : List ν :=
  N.nodes.filter (fun y => y ∉ seen ∧ y ∉ front ∧ front.any (fun x => decide (N.ResL U x y)))

theorem mem_newFront (U : List (ν × ν)) (seen front : List ν) (y : ν) :
    y ∈ N.newFront U seen front ↔
      y ∈ N.nodes ∧ y ∉ seen ∧ y ∉ front ∧ ∃ x ∈ front, N.ResL U x y := by
  simp [newFront, List.any_eq_true]

/-- Breadth-first layers: `front`, then the new nodes reached from it, and so on. -/
def layersAux (U : List (ν × ν)) : ℕ → List ν → List ν → List (List ν)
  | 0, _, front => [front]
  | k + 1, seen, front => front :: layersAux U k (seen ++ front) (N.newFront U seen front)

def layers (U : List (ν × ν)) : List (List ν) := N.layersAux U N.nodes.length [] [N.s]

/-- All nodes residually reachable from `s` (with `N.nodes.length` rounds). -/
def seen (U : List (ν × ν)) : List ν := (N.layers U).flatten

theorem layersAux_ne_nil (U : List (ν × ν)) (k : ℕ) (seen front : List ν) :
    N.layersAux U k seen front ≠ [] := by
  cases k <;> simp [layersAux]

theorem layersAux_head (U : List (ν × ν)) (k : ℕ) (seen front : List ν) :
    (N.layersAux U k seen front).head? = some front := by
  cases k <;> simp [layersAux]

/-- Nodes of the flattened layers avoid `seen` (given `seen` and `front` are disjoint). -/
theorem layersAux_notMem_seen (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    (∀ y ∈ front, y ∉ seen) → ∀ y ∈ (N.layersAux U k seen front).flatten, y ∉ seen
  | 0, seen, front, h, y, hy => by
      simp only [layersAux, List.flatten_cons, List.flatten_nil, List.append_nil] at hy
      exact h y hy
  | k + 1, seen, front, h, y, hy => by
      simp only [layersAux, List.flatten_cons, List.mem_append] at hy
      rcases hy with hy | hy
      · exact h y hy
      · have := layersAux_notMem_seen U k (seen ++ front) (N.newFront U seen front)
          (fun z hz => by
            rw [N.mem_newFront] at hz
            simp only [List.mem_append, not_or]
            exact ⟨hz.2.1, hz.2.2.1⟩) y hy
        simp only [List.mem_append, not_or] at this
        exact this.1

theorem layersAux_flatten_nodup (U : List (ν × ν)) (hn : N.nodes.Nodup) :
    ∀ (k : ℕ) (seen front : List ν), front.Nodup → (∀ y ∈ front, y ∉ seen) →
      (N.layersAux U k seen front).flatten.Nodup
  | 0, seen, front, hf, _ => by
      simp only [layersAux, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact hf
  | k + 1, seen, front, hf, h => by
      simp only [layersAux, List.flatten_cons]
      rw [List.nodup_append]
      refine ⟨hf, ?_, ?_⟩
      · refine layersAux_flatten_nodup U hn k (seen ++ front) (N.newFront U seen front)
          (hn.filter _) ?_
        intro z hz
        rw [N.mem_newFront] at hz
        simp only [List.mem_append, not_or]
        exact ⟨hz.2.1, hz.2.2.1⟩
      · intro a ha b hb hab
        have := N.layersAux_notMem_seen U k (seen ++ front) (N.newFront U seen front)
          (fun z hz => by
            rw [N.mem_newFront] at hz
            simp only [List.mem_append, not_or]
            exact ⟨hz.2.1, hz.2.2.1⟩) b hb
        simp only [List.mem_append, not_or] at this
        exact this.2 (hab ▸ ha)

theorem layersAux_flatten_subset (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    (∀ y ∈ front, y ∈ N.nodes) → ∀ y ∈ (N.layersAux U k seen front).flatten, y ∈ N.nodes
  | 0, seen, front, h, y, hy => by
      simp only [layersAux, List.flatten_cons, List.flatten_nil, List.append_nil] at hy
      exact h y hy
  | k + 1, seen, front, h, y, hy => by
      simp only [layersAux, List.flatten_cons, List.mem_append] at hy
      rcases hy with hy | hy
      · exact h y hy
      · exact layersAux_flatten_subset U k (seen ++ front) (N.newFront U seen front)
          (fun z hz => ((N.mem_newFront U _ _ z).mp hz).1) y hy

/-- Consecutive layers: every node of a layer is reached from the previous one. -/
theorem layersAux_chain (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    (N.layersAux U k seen front).IsChain (fun L L' => ∀ y ∈ L', ∃ x ∈ L, N.ResL U x y)
  | 0, _, _ => List.isChain_singleton _
  | k + 1, seen, front => by
      simp only [layersAux]
      obtain ⟨L, rest, hL⟩ : ∃ L rest, N.layersAux U k (seen ++ front) (N.newFront U seen front) =
          L :: rest := by
        cases h : N.layersAux U k (seen ++ front) (N.newFront U seen front) with
        | nil => exact absurd h (N.layersAux_ne_nil U _ _ _)
        | cons L rest => exact ⟨L, rest, rfl⟩
      have hhead : L = N.newFront U seen front := by
        have := N.layersAux_head U k (seen ++ front) (N.newFront U seen front)
        rw [hL] at this
        simpa using this
      rw [hL, List.isChain_cons_cons]
      refine ⟨?_, hL ▸ layersAux_chain U k (seen ++ front) (N.newFront U seen front)⟩
      intro y hy
      rw [hhead, N.mem_newFront] at hy
      exact hy.2.2.2

/-- Closedness of a node list under residual steps. -/
def Closed (U : List (ν × ν)) (L : List ν) : Prop :=
  ∀ x ∈ L, ∀ y ∈ N.nodes, N.ResL U x y → y ∈ L

/-- The expansion invariant: successors of expanded nodes lie in `seen ++ front`. -/
def Inv (U : List (ν × ν)) (seen front : List ν) : Prop :=
  ∀ x ∈ seen, ∀ y ∈ N.nodes, N.ResL U x y → y ∈ seen ∨ y ∈ front

theorem inv_step (U : List (ν × ν)) (seen front : List ν) (h : N.Inv U seen front) :
    N.Inv U (seen ++ front) (N.newFront U seen front) := by
  intro x hx y hy hr
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · rcases h x hx y hy hr with h1 | h1
    · exact Or.inl (List.mem_append_left _ h1)
    · exact Or.inl (List.mem_append_right _ h1)
  · by_cases hs : y ∈ seen
    · exact Or.inl (List.mem_append_left _ hs)
    · by_cases hf : y ∈ front
      · exact Or.inl (List.mem_append_right _ hf)
      · exact Or.inr ((N.mem_newFront U seen front y).mpr ⟨hy, hs, hf, x, hx, hr⟩)

theorem newFront_nil (U : List (ν × ν)) (seen : List ν) : N.newFront U seen [] = [] := by
  simp [newFront]

theorem layersAux_nil_front (U : List (ν × ν)) : ∀ (k : ℕ) (seen : List ν),
    (N.layersAux U k seen []).flatten = []
  | 0, _ => rfl
  | k + 1, seen => by
      simp only [layersAux, List.flatten_cons, List.nil_append, N.newFront_nil]
      exact layersAux_nil_front U k _

/-- Either the expansion closes, or every round adds a node. -/
theorem layersAux_closed_or (U : List (ν × ν)) : ∀ (k : ℕ) (seen front : List ν),
    N.Inv U seen front →
      N.Closed U (seen ++ (N.layersAux U k seen front).flatten) ∨
        k + 1 ≤ (N.layersAux U k seen front).flatten.length
  | 0, seen, front, hinv => by
      simp only [layersAux, List.flatten_cons, List.flatten_nil, List.append_nil]
      cases front with
      | nil =>
          left
          simp only [List.append_nil]
          intro x hx y hy hr
          rcases hinv x hx y hy hr with h | h
          · exact h
          · simp at h
      | cons a front => right; simp
  | k + 1, seen, front, hinv => by
      simp only [layersAux, List.flatten_cons]
      by_cases hfe : front = []
      · left
        subst hfe
        rw [N.newFront_nil, N.layersAux_nil_front]
        simp only [List.append_nil]
        intro x hx y hy hr
        rcases hinv x hx y hy hr with h | h
        · exact h
        · simp at h
      · have hlen := List.length_pos_of_ne_nil hfe
        rcases layersAux_closed_or U k (seen ++ front) (N.newFront U seen front)
          (N.inv_step U seen front hinv) with h | h
        · left
          rw [List.append_assoc] at h
          exact h
        · right
          rw [List.length_append]
          omega

theorem seen_nodup (U : List (ν × ν)) (hn : N.nodes.Nodup) : (N.seen U).Nodup :=
  N.layersAux_flatten_nodup U hn _ _ _ (List.nodup_singleton _) (by simp)

theorem seen_subset (U : List (ν × ν)) (hs : N.s ∈ N.nodes) : ∀ y ∈ N.seen U, y ∈ N.nodes :=
  N.layersAux_flatten_subset U _ _ _ (by simpa using hs)

theorem s_mem_seen (U : List (ν × ν)) : N.s ∈ N.seen U := by
  unfold seen layers
  cases N.nodes.length <;> simp [layersAux]

/-- The reachable set is closed under residual steps. -/
theorem seen_closed (U : List (ν × ν)) (hn : N.nodes.Nodup) (hs : N.s ∈ N.nodes) :
    N.Closed U (N.seen U) := by
  have hinv : N.Inv U [] [N.s] := fun x hx => by simp at hx
  rcases N.layersAux_closed_or U N.nodes.length [] [N.s] hinv with h | h
  · simpa [seen, layers] using h
  · exfalso
    have hnd := N.seen_nodup U hn
    have hsub := N.seen_subset U hs
    have : (N.seen U).length ≤ N.nodes.length := by
      rw [← List.toFinset_card_of_nodup hnd]
      exact (Finset.card_le_card (fun y hy => List.mem_toFinset.mpr
        (hsub y (List.mem_toFinset.mp hy)))).trans (List.toFinset_card_le _)
    unfold seen layers at this
    omega

/-! ### Path extraction from the layers -/

/-- Walk back from `y` through the reversed layers, choosing a residual predecessor in each. -/
def descendR (U : List (ν × ν)) : List (List ν) → ν → List ν
  | [], y => [y]
  | L :: rest, y =>
      y :: (match L.find? (fun x => decide (N.ResL U x y)) with
        | some x => descendR U rest x
        | none => [])

/-- Find the layer containing `y` (reversed layers) and descend from there. -/
def extractR (U : List (ν × ν)) : List (List ν) → ν → List ν
  | [], _ => []
  | L :: rest, y => if y ∈ L then N.descendR U rest y else extractR U rest y

/-- The augmenting path (from `s` to `t`) read off the layers. -/
def augPath (U : List (ν × ν)) : List ν := (N.extractR U (N.layers U).reverse N.t).reverse

/-- Reversed chain condition: every node of a list has a residual predecessor in the next list. -/
def RChain (U : List (ν × ν)) (rls : List (List ν)) : Prop :=
  rls.IsChain (fun L L' => ∀ z ∈ L, ∃ x ∈ L', N.ResL U x z)

theorem descendR_spec (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y : ν),
    N.RChain U rls → (∀ L ∈ rls.head?, ∃ x ∈ L, N.ResL U x y) →
    ∃ q : List ν, N.descendR U rls y = y :: q ∧ q.length = rls.length ∧
      (∀ i (hi : i < q.length) (hi' : i < rls.length), q[i] ∈ rls[i]) ∧
      (y :: q).IsChain (fun a b => N.ResL U b a)
  | [], y, _, _ => ⟨[], by simp [descendR], rfl, fun i hi => by simp at hi, List.isChain_singleton _⟩
  | L :: rest, y, hch, hy => by
      obtain ⟨x₀, hx₀, hr₀⟩ := hy L (by simp)
      obtain ⟨x, hfind⟩ : ∃ x, L.find? (fun x => decide (N.ResL U x y)) = some x := by
        cases hf : L.find? (fun x => decide (N.ResL U x y)) with
        | none =>
            exfalso
            have := List.find?_eq_none.mp hf x₀ hx₀
            simp at this
            exact this hr₀
        | some x => exact ⟨x, rfl⟩
      have hxL : x ∈ L := List.mem_of_find?_eq_some hfind
      have hxy : N.ResL U x y := by simpa using List.find?_some hfind
      have hch' : N.RChain U rest := by
        cases rest with
        | nil => exact List.isChain_nil
        | cons L' rest' => exact (List.isChain_cons_cons.mp hch).2
      have hx : ∀ L' ∈ rest.head?, ∃ x' ∈ L', N.ResL U x' x := by
        intro L' hL'
        cases rest with
        | nil => simp at hL'
        | cons L'' rest' =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hL'
            subst hL'
            exact (List.isChain_cons_cons.mp hch).1 x hxL
      obtain ⟨q, hq, hlen, hmem, hchain⟩ := descendR_spec U rest x hch' hx
      refine ⟨x :: q, ?_, by simp [hlen], ?_, ?_⟩
      · simp [descendR, hfind, hq]
      · intro i hi hi'
        cases i with
        | zero => simpa using hxL
        | succ i =>
            simp only [List.getElem_cons_succ]
            exact hmem i (by simpa using hi) (by simpa using hi')
      · exact List.isChain_cons_cons.mpr ⟨hxy, hchain⟩

omit [DecidableEq ν] in
theorem RChain_tail (U : List (ν × ν)) (L : List ν) (rest : List (List ν))
    (h : N.RChain U (L :: rest)) : N.RChain U rest := by
  cases rest with
  | nil => exact List.isChain_nil
  | cons L' rest' => exact (List.isChain_cons_cons.mp h).2

theorem extractR_spec (U : List (ν × ν)) : ∀ (rls : List (List ν)) (y : ν),
    N.RChain U rls → y ∈ rls.flatten →
    ∃ (j : ℕ) (hj : j < rls.length) (q : List ν), y ∈ rls[j] ∧
      N.extractR U rls y = y :: q ∧ q.length + j + 1 = rls.length ∧
      (∀ i (hi : i < q.length) (hi' : i + j + 1 < rls.length), q[i] ∈ rls[i + j + 1]) ∧
      (y :: q).IsChain (fun a b => N.ResL U b a)
  | [], y, _, hy => by simp at hy
  | L :: rest, y, hch, hy => by
      by_cases hyL : y ∈ L
      · have hy' : ∀ L' ∈ rest.head?, ∃ x ∈ L', N.ResL U x y := by
          intro L' hL'
          cases rest with
          | nil => simp at hL'
          | cons L'' rest' =>
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hL'
              subst hL'
              exact (List.isChain_cons_cons.mp hch).1 y hyL
        obtain ⟨q, hq, hlen, hmem, hchain⟩ :=
          N.descendR_spec U rest y (N.RChain_tail U L rest hch) hy'
        refine ⟨0, by simp, q, by simpa using hyL, ?_, by simp [hlen], ?_, hchain⟩
        · simp [extractR, hyL, hq]
        · intro i hi hi'
          simp only [Nat.add_zero, List.getElem_cons_succ]
          exact hmem i hi (by simpa using hi')
      · have hy' : y ∈ rest.flatten := by
          simp only [List.flatten_cons, List.mem_append] at hy
          exact hy.resolve_left hyL
        obtain ⟨j, hj, q, hyj, hq, hlen, hmem, hchain⟩ :=
          extractR_spec U rest y (N.RChain_tail U L rest hch) hy'
        refine ⟨j + 1, by simp; omega, q, by simpa using hyj, ?_, by simp; omega, ?_, hchain⟩
        · simp [extractR, hyL, hq]
        · intro i hi hi'
          have := hmem i hi (by simp at hi'; omega)
          simp only [List.length_cons] at hi'
          have e : i + (j + 1) + 1 = (i + j + 1) + 1 := by omega
          simp only [e, List.getElem_cons_succ]
          exact this

omit [DecidableEq ν] in
/-- Nodes chosen one per layer of a duplicate-free layering are distinct. -/
theorem nodup_of_layers : ∀ (Ls : List (List ν)) (q : List ν),
    Ls.flatten.Nodup → q.length = Ls.length →
    (∀ i (hi : i < q.length) (hi' : i < Ls.length), q[i] ∈ Ls[i]) → q.Nodup
  | [], q, _, hlen, _ => by
      cases q with
      | nil => exact List.nodup_nil
      | cons a q => simp at hlen
  | L :: Ls, q, hnd, hlen, hmem => by
      cases q with
      | nil => simp at hlen
      | cons a q =>
          rw [List.flatten_cons, List.nodup_append] at hnd
          obtain ⟨_, hnd2, hdisj⟩ := hnd
          have haL : a ∈ L := by simpa using hmem 0 (by simp) (by simp)
          rw [List.nodup_cons]
          refine ⟨?_, nodup_of_layers Ls q hnd2 (by simpa using hlen) ?_⟩
          · intro ha
            obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
            have hi' : i < Ls.length := by simp at hlen; omega
            have := hmem (i + 1) (by simpa using hi) (by simpa using hi')
            simp only [List.getElem_cons_succ] at this
            rw [hia] at this
            exact hdisj a haL a (List.mem_flatten.mpr ⟨Ls[i], List.getElem_mem hi', this⟩) rfl
          · intro i hi hi'
            have := hmem (i + 1) (by simpa using hi) (by simpa using hi')
            simpa using this

omit [DecidableEq ν] in
theorem nodup_of_layers_drop (Ls : List (List ν)) (q : List ν) (j : ℕ)
    (hnd : Ls.flatten.Nodup) (hlen : q.length + j = Ls.length)
    (hmem : ∀ i (hi : i < q.length) (hi' : i + j < Ls.length), q[i] ∈ Ls[i + j]) : q.Nodup := by
  apply nodup_of_layers (Ls.drop j) q
  · exact hnd.sublist (List.Sublist.flatten (List.drop_sublist j Ls))
  · simp; omega
  · intro i hi hi'
    rw [List.getElem_drop]
    have := hmem i hi (by simp at hi'; omega)
    simp only [Nat.add_comm j i]
    exact this

/-- Specification of the augmenting path: a simple residual path from `s` to `t`. -/
theorem augPath_spec (U : List (ν × ν)) (hn : N.nodes.Nodup) (ht : N.t ∈ N.seen U) :
    (N.augPath U).Nodup ∧ (N.augPath U).IsChain (N.ResL U) ∧
      (N.augPath U).head? = some N.s ∧ (N.augPath U).getLast? = some N.t := by
  set Ls := N.layers U with hLs
  have hch : N.RChain U Ls.reverse := by
    unfold RChain
    rw [List.isChain_reverse]
    exact N.layersAux_chain U _ _ _
  have hnd : Ls.reverse.flatten.Nodup :=
    ((List.reverse_perm Ls).flatten.nodup_iff).mpr (N.seen_nodup U hn)
  have ht' : N.t ∈ Ls.reverse.flatten := (List.reverse_perm Ls).flatten.mem_iff.mpr ht
  obtain ⟨j, hj, q, htj, hq, hlen, hmem, hchain⟩ := N.extractR_spec U Ls.reverse N.t hch ht'
  have hpath : N.augPath U = (N.t :: q).reverse := by
    unfold augPath; rw [← hLs, hq]
  have hlast : ∀ z, (N.t :: q).getLast? = some z → z = N.s := by
    intro z hz
    -- the last element lies in the last reversed layer, which is the first layer `[s]`
    have hmem' : ∀ i (hi : i < (N.t :: q).length) (hi' : i + j < Ls.reverse.length),
        (N.t :: q)[i] ∈ Ls.reverse[i + j] := by
      intro i hi hi'
      cases i with
      | zero => simpa using htj
      | succ i =>
          simp only [List.getElem_cons_succ]
          have e : i + 1 + j = i + j + 1 := by omega
          have := hmem i (by simpa using hi) (by omega)
          simp only [e]; exact this
    have hl := List.getLast?_eq_getElem? (l := N.t :: q)
    rw [hz] at hl
    have hlen' : (N.t :: q).length - 1 < (N.t :: q).length := by simp
    rw [List.getElem?_eq_getElem hlen'] at hl
    have hz' := hmem' ((N.t :: q).length - 1) hlen' (by simp at hlen ⊢; omega)
    have hz2 : z = (N.t :: q)[(N.t :: q).length - 1] := Option.some.inj hl
    rw [← hz2] at hz'
    -- convert to the first layer
    have hidx : ∀ (h : (N.t :: q).length - 1 + j < Ls.reverse.length),
        Ls.reverse[(N.t :: q).length - 1 + j]'h = [N.s] := by
      intro h
      rw [List.getElem_reverse]
      have h0 : Ls.length - 1 - ((N.t :: q).length - 1 + j) = 0 := by simp at hlen ⊢; omega
      simp only [h0]
      have : Ls.head? = some [N.s] := N.layersAux_head U N.nodes.length [] [N.s]
      rw [List.head?_eq_getElem?] at this
      have hpos : 0 < Ls.length := by simp at hlen ⊢; omega
      rw [List.getElem?_eq_getElem hpos] at this
      simpa using this
    rw [hidx] at hz'
    simpa using hz'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpath, List.nodup_reverse]
    apply nodup_of_layers_drop Ls.reverse (N.t :: q) j hnd (by simp at hlen ⊢; omega)
    intro i hi hi'
    cases i with
    | zero => simpa using htj
    | succ i =>
        simp only [List.getElem_cons_succ]
        have e : i + 1 + j = i + j + 1 := by omega
        have := hmem i (by simpa using hi) (by omega)
        simp only [e]; exact this
  · rw [hpath, List.isChain_reverse]
    exact hchain
  · rw [hpath, List.head?_reverse]
    obtain ⟨z, hz⟩ : ∃ z, (N.t :: q).getLast? = some z := ⟨_, List.getLast?_eq_getLast_of_ne_nil (by simp)⟩
    rw [hz, hlast z hz]
  · rw [hpath, List.getLast?_reverse]; rfl

/-! ### Augmentation along a residual path -/

/-- Consecutive pairs of a list. -/
def steps (p : List ν) : List (ν × ν) := p.zip p.tail

omit [DecidableEq ν] in
theorem steps_cons_cons (a b : ν) (rest : List ν) :
    steps (a :: b :: rest) = (a, b) :: steps (b :: rest) := rfl

omit [DecidableEq ν] in
theorem mem_steps {p : List ν} {e : ν × ν} (h : e ∈ steps p) : e.1 ∈ p ∧ e.2 ∈ p := by
  obtain ⟨a, b⟩ := e
  have := List.of_mem_zip h
  exact ⟨this.1, List.mem_of_mem_tail this.2⟩

omit [DecidableEq ν] in
theorem chain_steps {R : ν → ν → Prop} : ∀ {p : List ν}, p.IsChain R → ∀ e ∈ steps p, R e.1 e.2
  | [], _, e, he => by simp [steps] at he
  | [a], _, e, he => by simp [steps] at he
  | a :: b :: rest, h, e, he => by
      rw [steps_cons_cons, List.mem_cons] at he
      rw [List.isChain_cons_cons] at h
      rcases he with rfl | he
      · exact h.1
      · exact chain_steps h.2 e he

omit [DecidableEq ν] in
theorem steps_nodup : ∀ {p : List ν}, p.Nodup → (steps p).Nodup
  | [], _ => by simp [steps]
  | [a], _ => by simp [steps]
  | a :: b :: rest, h => by
      rw [steps_cons_cons, List.nodup_cons]
      rw [List.nodup_cons] at h
      exact ⟨fun hm => h.1 (mem_steps hm).1, steps_nodup h.2⟩

/-- Number of steps of `p` entering `x`. -/
def din (p : List ν) (x : ν) : ℕ := (steps p).countP (fun e => decide (e.2 = x))
/-- Number of steps of `p` leaving `x`. -/
def dout (p : List ν) (x : ν) : ℕ := (steps p).countP (fun e => decide (e.1 = x))

/-- Telescoping: steps in plus "is the head" equals steps out plus "is the last". -/
theorem din_dout : ∀ (p : List ν) (x : ν),
    din p x + (if p.head? = some x then 1 else 0) =
      dout p x + (if p.getLast? = some x then 1 else 0)
  | [], x => by simp [din, dout, steps]
  | [a], x => by simp [din, dout, steps]
  | a :: b :: rest, x => by
      have ih := din_dout (b :: rest) x
      unfold din dout at ih ⊢
      rw [steps_cons_cons, List.countP_cons, List.countP_cons, List.getLast?_cons_cons]
      simp only [List.head?_cons] at ih ⊢
      generalize (if (b :: rest).getLast? = some x then 1 else 0) = c at ih ⊢
      by_cases hax : a = x <;> by_cases hbx : b = x <;> simp [hax, hbx] at ih ⊢ <;> omega

/-- Augment `U` along `p`: drop the backward arcs, add the forward ones. -/
def augment (U : List (ν × ν)) (p : List ν) : List (ν × ν) :=
  U.filter (fun a => (a.2, a.1) ∉ steps p) ++ (steps p).filter (fun e => e ∈ N.arcs)

omit [DecidableEq ν] in
theorem forward_notMem (hN : N.Ok) {U : List (ν × ν)} (hU : ∀ a ∈ U, a ∈ N.arcs) {p : List ν}
    (hch : p.IsChain (N.ResL U)) {e : ν × ν} (he : e ∈ steps p) (ha : e ∈ N.arcs) : e ∉ U := by
  obtain ⟨e1, e2⟩ := e
  rcases chain_steps hch _ he with ⟨_, h⟩ | h
  · exact h
  · exact absurd (hU _ h) (hN.no_anti _ ha)

theorem augment_nodup (hN : N.Ok) (U : List (ν × ν)) (p : List ν) (hU : U.Nodup)
    (hsub : ∀ a ∈ U, a ∈ N.arcs) (hp : p.Nodup) (hch : p.IsChain (N.ResL U)) :
    (N.augment U p).Nodup := by
  unfold augment
  rw [List.nodup_append]
  refine ⟨hU.filter _, (steps_nodup hp).filter _, ?_⟩
  intro a ha e he hae
  subst hae
  rw [List.mem_filter] at ha he
  simp only [decide_eq_true_eq] at he
  exact N.forward_notMem hN hsub hch he.1 he.2 ha.1

theorem augment_sub (U : List (ν × ν)) (p : List ν) (hsub : ∀ a ∈ U, a ∈ N.arcs) :
    ∀ a ∈ N.augment U p, a ∈ N.arcs := by
  intro a ha
  unfold augment at ha
  rw [List.mem_append, List.mem_filter, List.mem_filter] at ha
  rcases ha with h | h
  · exact hsub a h.1
  · simpa using h.2

/-! Degree bookkeeping. -/

theorem indeg_union (G₁ G₂ : Finset (ν × ν)) (h : Disjoint G₁ G₂) (x : ν) :
    indeg (G₁ ∪ G₂) x = indeg G₁ x + indeg G₂ x := by
  unfold indeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem outdeg_union (G₁ G₂ : Finset (ν × ν)) (h : Disjoint G₁ G₂) (x : ν) :
    outdeg (G₁ ∪ G₂) x = outdeg G₁ x + outdeg G₂ x := by
  unfold outdeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem indeg_split (G : Finset (ν × ν)) (q : ν × ν → Prop) [DecidablePred q] (x : ν) :
    indeg (G.filter q) x + indeg (G.filter (fun a => ¬ q a)) x = indeg G x := by
  unfold indeg
  rw [Finset.filter_filter, Finset.filter_filter,
    ← Finset.filter_card_add_filter_neg_card_eq_card (s := G.filter (fun a => a.2 = x)) q,
    Finset.filter_filter, Finset.filter_filter]
  congr 2 <;> ext a <;> simp only [Finset.mem_filter] <;> tauto

theorem outdeg_split (G : Finset (ν × ν)) (q : ν × ν → Prop) [DecidablePred q] (x : ν) :
    outdeg (G.filter q) x + outdeg (G.filter (fun a => ¬ q a)) x = outdeg G x := by
  unfold outdeg
  rw [Finset.filter_filter, Finset.filter_filter,
    ← Finset.filter_card_add_filter_neg_card_eq_card (s := G.filter (fun a => a.1 = x)) q,
    Finset.filter_filter, Finset.filter_filter]
  congr 2 <;> ext a <;> simp only [Finset.mem_filter] <;> tauto

theorem card_swap_filter (G E' : Finset (ν × ν)) (r : ν × ν → Prop) [DecidablePred r] :
    (G.filter (fun a => r a ∧ (a.2, a.1) ∈ E')).card =
      (E'.filter (fun e => r (e.2, e.1) ∧ (e.2, e.1) ∈ G)).card := by
  refine Finset.card_bij' (fun a _ => (a.2, a.1)) (fun e _ => (e.2, e.1)) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2.2, by simpa using ha.2.1, by simpa using ha.1⟩
  · intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.2.2, he.2.1, by simpa using he.1⟩
  · intro a _; simp
  · intro e _; simp

theorem card_filter_toFinset {E : List (ν × ν)} (hE : E.Nodup) (q : ν × ν → Bool) :
    (E.toFinset.filter (fun e => q e = true)).card = E.countP q := by
  rw [← List.toFinset_filter, List.toFinset_card_of_nodup (hE.filter q),
    List.countP_eq_length_filter]

/-- Augmenting along a simple residual `s`–`t` path keeps a flow and raises its value. -/
theorem augment_flow (hN : N.Ok) (U : List (ν × ν)) (p : List ν)
    (hU : N.IsFlow U.toFinset) (hp : p.Nodup) (hch : p.IsChain (N.ResL U))
    (hhead : p.head? = some N.s) (hlast : p.getLast? = some N.t) :
    N.IsFlow (N.augment U p).toFinset ∧
      N.value U.toFinset + 1 ≤ N.value (N.augment U p).toFinset := by
  set F := U.toFinset with hF
  set E' := (steps p).toFinset with hE'
  have hres : ∀ e ∈ E', N.ResL U e.1 e.2 :=
    fun e he => chain_steps hch e (List.mem_toFinset.mp he)
  have hdich : ∀ e ∈ E', (¬ e ∈ N.arcs ↔ (e.2, e.1) ∈ F) := by
    intro e he
    obtain ⟨e1, e2⟩ := e
    rcases hres _ he with ⟨ha, _⟩ | hb
    · constructor
      · intro h; exact absurd ha h
      · intro h; exact absurd (hU.sub _ h) (hN.no_anti _ ha)
    · constructor
      · intro _; exact List.mem_toFinset.mpr hb
      · intro _ ha; exact hN.no_anti _ ha (hU.sub _ (List.mem_toFinset.mpr hb))
  set Fk := F.filter (fun a => ¬ (a.2, a.1) ∈ steps p) with hFk
  set B := F.filter (fun a => (a.2, a.1) ∈ steps p) with hB
  set A := E'.filter (fun e => e ∈ N.arcs) with hA
  have hF' : (N.augment U p).toFinset = Fk ∪ A := by
    ext a
    simp [augment, hFk, hA, hF, hE']
  have hdisj : Disjoint Fk A := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hFk, Finset.mem_filter] at ha
    rw [hA, Finset.mem_filter] at hb
    exact N.forward_notMem hN (fun a ha => hU.sub a (List.mem_toFinset.mpr ha)) hch
      (List.mem_toFinset.mp hb.1) hb.2 (List.mem_toFinset.mp ha.1)
  -- degree identities
  have hin : ∀ x, indeg (N.augment U p).toFinset x = indeg Fk x + indeg A x :=
    fun x => by rw [hF', indeg_union _ _ hdisj]
  have hout : ∀ x, outdeg (N.augment U p).toFinset x = outdeg Fk x + outdeg A x :=
    fun x => by rw [hF', outdeg_union _ _ hdisj]
  have hinF : ∀ x, indeg B x + indeg Fk x = indeg F x :=
    fun x => indeg_split F (fun a => (a.2, a.1) ∈ steps p) x
  have houtF : ∀ x, outdeg B x + outdeg Fk x = outdeg F x :=
    fun x => outdeg_split F (fun a => (a.2, a.1) ∈ steps p) x
  -- backward steps, seen from the path
  have hinB : ∀ x, indeg B x = (E'.filter (fun e => e.1 = x ∧ (e.2, e.1) ∈ F)).card := by
    intro x
    unfold indeg
    rw [hB, Finset.filter_filter]
    rw [Finset.filter_congr (q := fun a => a.2 = x ∧ (a.2, a.1) ∈ E')
      (fun a _ => by
        show ((a.2, a.1) ∈ steps p ∧ a.2 = x) ↔ (a.2 = x ∧ (a.2, a.1) ∈ E')
        rw [hE', List.mem_toFinset]; exact and_comm)]
    exact card_swap_filter F E' (fun a => a.2 = x)
  have houtB : ∀ x, outdeg B x = (E'.filter (fun e => e.2 = x ∧ (e.2, e.1) ∈ F)).card := by
    intro x
    unfold outdeg
    rw [hB, Finset.filter_filter]
    rw [Finset.filter_congr (q := fun a => a.1 = x ∧ (a.2, a.1) ∈ E')
      (fun a _ => by
        show ((a.2, a.1) ∈ steps p ∧ a.1 = x) ↔ (a.1 = x ∧ (a.2, a.1) ∈ E')
        rw [hE', List.mem_toFinset]; exact and_comm)]
    exact card_swap_filter F E' (fun a => a.1 = x)
  have hinA : ∀ x, indeg A x = (E'.filter (fun e => e.2 = x ∧ e ∈ N.arcs)).card := by
    intro x
    unfold indeg
    rw [hA, Finset.filter_filter]
    congr 1; ext e; simp only [Finset.mem_filter]; tauto
  have houtA : ∀ x, outdeg A x = (E'.filter (fun e => e.1 = x ∧ e ∈ N.arcs)).card := by
    intro x
    unfold outdeg
    rw [hA, Finset.filter_filter]
    congr 1; ext e; simp only [Finset.mem_filter]; tauto
  -- forward + backward = all steps
  have hdin : ∀ x, (E'.filter (fun e => e.2 = x ∧ e ∈ N.arcs)).card +
      (E'.filter (fun e => e.2 = x ∧ (e.2, e.1) ∈ F)).card = din p x := by
    intro x
    have h1 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := E'.filter (fun e => e.2 = x)) (fun e => e ∈ N.arcs)
    rw [Finset.filter_filter, Finset.filter_filter] at h1
    rw [Finset.filter_congr (p := fun e => e.2 = x ∧ ¬ e ∈ N.arcs)
      (q := fun e => e.2 = x ∧ (e.2, e.1) ∈ F) (fun e he => by
        show (e.2 = x ∧ ¬ e ∈ N.arcs) ↔ (e.2 = x ∧ (e.2, e.1) ∈ F)
        rw [hdich e he])] at h1
    rw [h1]
    unfold din
    rw [← card_filter_toFinset (steps_nodup hp)]
    congr 1; ext e; simp [hE']
  have hdout : ∀ x, (E'.filter (fun e => e.1 = x ∧ e ∈ N.arcs)).card +
      (E'.filter (fun e => e.1 = x ∧ (e.2, e.1) ∈ F)).card = dout p x := by
    intro x
    have h1 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := E'.filter (fun e => e.1 = x)) (fun e => e ∈ N.arcs)
    rw [Finset.filter_filter, Finset.filter_filter] at h1
    rw [Finset.filter_congr (p := fun e => e.1 = x ∧ ¬ e ∈ N.arcs)
      (q := fun e => e.1 = x ∧ (e.2, e.1) ∈ F) (fun e he => by
        show (e.1 = x ∧ ¬ e ∈ N.arcs) ↔ (e.1 = x ∧ (e.2, e.1) ∈ F)
        rw [hdich e he])] at h1
    rw [h1]
    unfold dout
    rw [← card_filter_toFinset (steps_nodup hp)]
    congr 1; ext e; simp [hE']
  have htel := fun x => din_dout p x
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    exact N.augment_sub U p (fun a ha => hU.sub a (List.mem_toFinset.mpr ha)) a
      (List.mem_toFinset.mp ha)
  · intro x hxs hxt
    have h1 := hin x; have h2 := hout x; have h3 := hinF x; have h4 := houtF x
    have h5 := hinB x; have h6 := houtB x; have h7 := hinA x; have h8 := houtA x
    have h9 := hdin x; have h10 := hdout x; have h11 := htel x
    have h12 := hU.cons x hxs hxt
    rw [hhead, hlast] at h11
    simp only [Option.some.injEq, hxs.symm, hxt.symm, if_false, add_zero] at h11
    omega
  · unfold value
    have h2 := hout N.s; have h4 := houtF N.s; have h6 := houtB N.s; have h8 := houtA N.s
    have h10 := hdout N.s; have h9 := hdin N.s; have h5 := hinB N.s; have h7 := hinA N.s
    have h11 := htel N.s
    have h3 := hinF N.s
    have h0 := N.indeg_s_eq_zero hN hU
    rw [hhead, hlast] at h11
    simp only [Option.some.injEq, hN.st.symm, if_true, if_false, add_zero] at h11
    omega

/-! ### Residual closure gives a tight cut -/

/-- A flow whose residual-reachable set `S` is closed saturates the cut `S`. -/
theorem value_eq_cap_of_closed (hN : N.Ok) (U : List (ν × ν)) (hU : N.IsFlow U.toFinset)
    (S : Finset ν) (hS : ∀ x ∈ S, ∀ y ∈ N.nodes, N.ResL U x y → y ∈ S)
    (hs : N.s ∈ S) (ht : N.t ∉ S) : N.value U.toFinset = N.cap S := by
  have h := N.cut_identity hN hU S hs ht
  have h0 : (U.toFinset.filter (fun a => a.1 ∉ S ∧ a.2 ∈ S)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨a1, a2⟩ ha ⟨h1, h2⟩
    exact h1 (hS a2 h2 a1 (hN.arcs_mem _ (hU.sub _ ha)).1 (Or.inr (List.mem_toFinset.mp ha)))
  have h1 : (U.toFinset.filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)) =
      N.arcs.toFinset.filter (fun a => a.1 ∈ S ∧ a.2 ∉ S) := by
    ext ⟨a1, a2⟩
    simp only [Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨ha, h⟩; exact ⟨hU.sub _ (List.mem_toFinset.mpr ha), h⟩
    · rintro ⟨ha, hS1, hS2⟩
      refine ⟨?_, hS1, hS2⟩
      by_contra hu
      exact hS2 (hS a1 hS1 a2 (hN.arcs_mem _ ha).2 (Or.inl ⟨ha, hu⟩))
  unfold cap
  rw [← h1]
  omega

/-! ### The augmenting-path loop -/

/-- The loop invariant: a duplicate-free list of arcs forming a flow. -/
structure Good (U : List (ν × ν)) : Prop where
  flow : N.IsFlow U.toFinset
  nodup : U.Nodup

/-- `fuel` rounds of: find a residual path, augment. -/
def ffAux : ℕ → List (ν × ν) → List (ν × ν)
  | 0, U => U
  | f + 1, U => if N.t ∈ N.seen U then ffAux f (N.augment U (N.augPath U)) else U

/-- The maximum flow, computed with `|arcs| + 1` rounds. -/
def maxflow : List (ν × ν) := N.ffAux (N.arcs.length + 1) []

theorem ffAux_spec (hN : N.Ok) : ∀ (f : ℕ) (U : List (ν × ν)), N.Good U →
    N.arcs.length < N.value U.toFinset + f →
    N.Good (N.ffAux f U) ∧ N.t ∉ N.seen (N.ffAux f U)
  | 0, U, hU, hf => by
      have := N.value_le_arcs hU.flow
      omega
  | f + 1, U, hU, hf => by
      simp only [ffAux]
      split_ifs with ht
      · obtain ⟨hnd, hch, hh, hl⟩ := N.augPath_spec U hN.nodes_nodup ht
        obtain ⟨hflow, hval⟩ := N.augment_flow hN U _ hU.flow hnd hch hh hl
        exact ffAux_spec hN f _
          ⟨hflow, N.augment_nodup hN U _ hU.nodup
            (fun a ha => hU.flow.sub a (List.mem_toFinset.mpr ha)) hnd hch⟩ (by omega)
      · exact ⟨hU, ht⟩

theorem good_nil : N.Good [] :=
  ⟨⟨fun a ha => by simp at ha, fun x _ _ => by simp [indeg, outdeg]⟩, List.nodup_nil⟩

/-- **Max-flow specification**: `maxflow` is a flow, `t` is residually unreachable, and the
value equals the capacity of the reachable cut. -/
theorem maxflow_spec (hN : N.Ok) :
    N.Good N.maxflow ∧ N.t ∉ N.seen N.maxflow ∧
      N.s ∈ (N.seen N.maxflow).toFinset ∧ N.t ∉ (N.seen N.maxflow).toFinset ∧
      N.value N.maxflow.toFinset = N.cap (N.seen N.maxflow).toFinset := by
  obtain ⟨hg, ht⟩ := N.ffAux_spec hN (N.arcs.length + 1) [] N.good_nil (by omega)
  refine ⟨hg, ht, List.mem_toFinset.mpr (N.s_mem_seen _), fun h => ht (List.mem_toFinset.mp h), ?_⟩
  apply N.value_eq_cap_of_closed hN _ hg.flow
  · intro x hx y hy hr
    exact List.mem_toFinset.mpr
      (N.seen_closed _ hN.nodes_nodup hN.s_mem x (List.mem_toFinset.mp hx) y hy hr)
  · exact List.mem_toFinset.mpr (N.s_mem_seen _)
  · exact fun h => ht (List.mem_toFinset.mp h)

/-- **Max-flow min-cut** for unit capacities: the value of `maxflow` is the minimum capacity
of an `s`–`t` cut, and it is attained by the reachable cut. -/
theorem maxflow_minCut (hN : N.Ok) :
    (∀ S : Finset ν, N.s ∈ S → N.t ∉ S → N.value N.maxflow.toFinset ≤ N.cap S) ∧
      ∃ S : Finset ν, N.s ∈ S ∧ N.t ∉ S ∧ N.value N.maxflow.toFinset = N.cap S := by
  obtain ⟨hg, -, hs, ht, hv⟩ := N.maxflow_spec hN
  exact ⟨fun S hsS htS => N.value_le_cap hN hg.flow S hsS htS, _, hs, ht, hv⟩

/-- The reachable set of the maximum flow, as an executable node list. -/
def minCutSet : List ν := N.seen N.maxflow

theorem minCutSet_spec (hN : N.Ok) :
    N.s ∈ N.minCutSet ∧ N.t ∉ N.minCutSet ∧
      (∀ x ∈ N.minCutSet, ∀ y ∈ N.nodes, N.ResL N.maxflow x y → y ∈ N.minCutSet) ∧
      N.value N.maxflow.toFinset = N.cap N.minCutSet.toFinset :=
  ⟨N.s_mem_seen _, (N.maxflow_spec hN).2.1,
    N.seen_closed _ hN.nodes_nodup hN.s_mem, (N.maxflow_spec hN).2.2.2.2⟩

end Network
end DisequalityDispersion.Flow
