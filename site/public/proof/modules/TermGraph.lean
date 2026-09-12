import GeneralSemantics

/-! # The shared term DAG, source-output paths and vertex cuts (R1)

Vertices are terms; there is an edge from each immediate argument to its
parent term.  A source-output path is a chain of immediate arguments that
starts at a source `var v` and ends at an output.  `Avoids K t` says that
some source path ending at `t` avoids the vertex set `K` (this is the
inductive shape of a path in the DAG of subterms; a source that is itself an
output gives the length-zero path).  A vertex cut is a set meeting every
source-output path; `cutSize` is the minimum cardinality of a cut inside the
support `S` (all subterms of outputs and tests together with all sources).
Repeated outputs designate one vertex because vertices are terms. -/

namespace DisequalityDispersion

variable {V F : Type} {arity : F → ℕ}

/-- `u` is an immediate argument of `t`. -/
def IsArg (u t : Term V F arity) : Prop :=
  ∃ (f : F) (ts : Fin (arity f) → Term V F arity) (i : Fin (arity f)), t = .app f ts ∧ ts i = u

/-- Some source path ending at `t` avoids `K` (a path is a chain of immediate
arguments starting at a source variable). -/
inductive Avoids (K : Finset (Term V F arity)) : Term V F arity → Prop
  | var (v : V) (h : Term.var v ∉ K) : Avoids K (.var v)
  | app (f : F) (ts : Fin (arity f) → Term V F arity) (h : Term.app f ts ∉ K)
      (i : Fin (arity f)) (hi : Avoids K (ts i)) : Avoids K (.app f ts)

/-- `K` is a vertex cut between the sources and the outputs. -/
def IsCut (K : Finset (Term V F arity)) (outputs : List (Term V F arity)) : Prop :=
  ∀ t ∈ outputs, ¬ Avoids K t

theorem avoids_var_iff (K : Finset (Term V F arity)) (v : V) :
    Avoids K (.var v) ↔ Term.var v ∉ K := by
  constructor
  · intro h
    cases h with
    | var _ h => exact h
  · exact Avoids.var v

/-- Every cut contains every source that is an output (the length-zero path). -/
theorem source_output_mem_cut (K : Finset (Term V F arity)) (outputs : List (Term V F arity))
    (hK : IsCut K outputs) (v : V) (hv : Term.var v ∈ outputs) : Term.var v ∈ K := by
  by_contra h
  exact hK _ hv (Avoids.var v h)

theorem avoids_mono {K K' : Finset (Term V F arity)} (h : K' ⊆ K) {t : Term V F arity}
    (ha : Avoids K t) : Avoids K' t := by
  induction ha with
  | var v hv => exact Avoids.var v (fun h' => hv (h h'))
  | app f ts hn i hi ih => exact Avoids.app f ts (fun h' => hn (h h')) i ih

/-! ### Support -/

/-- All subterms of the outputs and tests together with all declared sources. -/
noncomputable def tupleSupport [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Finset (Term V F arity) := by
  classical
  exact (Finset.univ.image Term.var ∪ outputs.toFinset.biUnion Term.support) ∪
    tests.toFinset.biUnion (fun uv => uv.1.support ∪ uv.2.support)

theorem source_mem_tupleSupport [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (v : V) :
    Term.var v ∈ tupleSupport outputs tests := by
  classical
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem output_support_subset_tupleSupport [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (t : Term V F arity) (ht : t ∈ outputs) :
    t.support ⊆ tupleSupport outputs tests := by
  classical
  intro u hu
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨t, List.mem_toFinset.mpr ht, hu⟩

theorem output_mem_tupleSupport [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (t : Term V F arity) (ht : t ∈ outputs) :
    t ∈ tupleSupport outputs tests :=
  output_support_subset_tupleSupport outputs tests t ht t.mem_support_self

theorem tests_mem_tupleSupport [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (uv : Term V F arity × Term V F arity)
    (huv : uv ∈ tests) : uv.1 ∈ tupleSupport outputs tests ∧ uv.2 ∈ tupleSupport outputs tests := by
  classical
  constructor
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨uv, List.mem_toFinset.mpr huv, Finset.mem_union_left _ uv.1.mem_support_self⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨uv, List.mem_toFinset.mpr huv, Finset.mem_union_right _ uv.2.mem_support_self⟩)

theorem tupleSupport_closed [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    SubtermClosed (tupleSupport outputs tests) := by
  classical
  apply SubtermClosed.union
  · apply SubtermClosed.union
    · intro f ts h
      exfalso
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h
      cases hv
    · intro f ts h i
      obtain ⟨t, ht, hmem⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_biUnion.mpr ⟨t, ht, t.support_closed f ts hmem i⟩
  · intro f ts h i
    obtain ⟨uv, huv, hmem⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨uv, huv,
      (SubtermClosed.union uv.1.support_closed uv.2.support_closed) f ts hmem i⟩

/-- Two distinct retained sources give a support of size at least two. -/
theorem two_le_tupleSupport_card [Fintype V] (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity)) :
    2 ≤ (tupleSupport outputs tests).card := by
  classical
  apply Finset.one_lt_card.mpr
  exact ⟨.var x, source_mem_tupleSupport outputs tests x, .var y,
    source_mem_tupleSupport outputs tests y, fun h => hxy (Term.var.inj h)⟩

/-- The whole support is a cut. -/
theorem tupleSupport_isCut [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    IsCut (tupleSupport outputs tests) outputs := by
  intro t ht ha
  induction ha with
  | var v hv => exact hv (source_mem_tupleSupport outputs tests v)
  | app f ts hn i hi ih => exact hn (output_mem_tupleSupport outputs tests _ ht)

open Classical in
/-- A path avoiding `K` from a source to a subterm of an output stays inside the
support; hence intersecting a cut with the support keeps it a cut. -/
theorem avoids_inter_support [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (K : Finset (Term V F arity))
    (t : Term V F arity) (ht : t.support ⊆ tupleSupport outputs tests)
    (ha : Avoids (K ∩ tupleSupport outputs tests) t) : Avoids K t := by
  classical
  induction ha with
  | var v hv =>
      apply Avoids.var
      intro hK
      exact hv (Finset.mem_inter.mpr ⟨hK, source_mem_tupleSupport outputs tests v⟩)
  | app f ts hn i hi ih =>
      apply Avoids.app f ts _ i
      · apply ih
        intro u hu
        apply ht
        simp only [Term.support, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        exact Or.inr ⟨i, hu⟩
      · intro hK
        exact hn (Finset.mem_inter.mpr ⟨hK, ht (Term.mem_support_self _)⟩)

open Classical in
theorem isCut_inter_support [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (K : Finset (Term V F arity))
    (hK : IsCut K outputs) : IsCut (K ∩ tupleSupport outputs tests) outputs := by
  intro t ht ha
  exact hK t ht (avoids_inter_support outputs tests K t
    (output_support_subset_tupleSupport outputs tests t ht) ha)

/-! ### The minimum cut -/

/-- The cuts inside the support. -/
noncomputable def cutsIn [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Finset (Finset (Term V F arity)) := by
  classical
  exact (tupleSupport outputs tests).powerset.filter (fun K => IsCut K outputs)

theorem tupleSupport_mem_cutsIn [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    tupleSupport outputs tests ∈ cutsIn outputs tests := by
  classical
  simp only [cutsIn, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨subset_rfl, tupleSupport_isCut outputs tests⟩

theorem cutsIn_nonempty [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    ((cutsIn outputs tests).image Finset.card).Nonempty :=
  ⟨_, Finset.mem_image.mpr ⟨_, tupleSupport_mem_cutsIn outputs tests, rfl⟩⟩

/-- `ρ`: the minimum cardinality of a vertex cut inside the support. -/
noncomputable def cutSize [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : ℕ :=
  ((cutsIn outputs tests).image Finset.card).min' (cutsIn_nonempty outputs tests)

/-- A minimum cut exists inside the support. -/
theorem exists_min_cut [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    ∃ K : Finset (Term V F arity), K ⊆ tupleSupport outputs tests ∧ IsCut K outputs ∧
      K.card = cutSize outputs tests := by
  classical
  have h := Finset.min'_mem _ (cutsIn_nonempty outputs tests)
  obtain ⟨K, hK, hc⟩ := Finset.mem_image.mp h
  simp only [cutsIn, Finset.mem_filter, Finset.mem_powerset] at hK
  exact ⟨K, hK.1, hK.2, hc⟩

/-- Every cut has at least `ρ` vertices. -/
theorem cutSize_le_card_of_isCut [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (K : Finset (Term V F arity))
    (hK : IsCut K outputs) : cutSize outputs tests ≤ K.card := by
  classical
  have hmem : K ∩ tupleSupport outputs tests ∈ cutsIn outputs tests := by
    simp only [cutsIn, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, isCut_inter_support outputs tests K hK⟩
  have h1 : cutSize outputs tests ≤ (K ∩ tupleSupport outputs tests).card :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_, hmem, rfl⟩)
  exact h1.trans (Finset.card_le_card Finset.inter_subset_left)

theorem cutSize_le_support_card [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    cutSize outputs tests ≤ (tupleSupport outputs tests).card :=
  cutSize_le_card_of_isCut outputs tests _ (tupleSupport_isCut outputs tests)

/-- **Retained pair in every cut**: if `var x` and `var y` are outputs, every
cut contains both, so `ρ ≥ 2` when `x ≠ y`. -/
theorem retained_pair_mem_cut (K : Finset (Term V F arity)) (outputs : List (Term V F arity))
    (hK : IsCut K outputs) (x y : V) (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) :
    Term.var x ∈ K ∧ Term.var y ∈ K :=
  ⟨source_output_mem_cut K outputs hK x hx, source_output_mem_cut K outputs hK y hy⟩

theorem two_le_card_of_isCut (K : Finset (Term V F arity)) (outputs : List (Term V F arity))
    (hK : IsCut K outputs) (x y : V) (hxy : x ≠ y) (hx : Term.var x ∈ outputs)
    (hy : Term.var y ∈ outputs) : 2 ≤ K.card := by
  obtain ⟨h1, h2⟩ := retained_pair_mem_cut K outputs hK x y hx hy
  apply Finset.one_lt_card.mpr
  exact ⟨.var x, h1, .var y, h2, fun h => hxy (Term.var.inj h)⟩

theorem two_le_cutSize [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (x y : V) (hxy : x ≠ y)
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) : 2 ≤ cutSize outputs tests := by
  obtain ⟨K, _, hK, hc⟩ := exists_min_cut outputs tests
  rw [← hc]
  exact two_le_card_of_isCut K outputs hK x y hxy hx hy

end DisequalityDispersion
