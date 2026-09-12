import Semantics
import PresentationBridge

namespace DisequalityDispersion
variable {S A : Type}

abbrev UnaryTerm (S : Type) := Term Bool (Letter S) (fun _ => 1)

def wordTerm : List (Letter S) → UnaryTerm S
  | [] => .var false
  | l :: w => .app l (fun _ => wordTerm w)

def unaryInterpretation (p m : S → A → A) : Interpretation (Letter S) (fun _ => 1) A :=
  fun l a => signedTables p m l (a 0)

theorem eval_wordTerm (p m : S → A → A) (a : Bool → A) (w : List (Letter S)) :
    (wordTerm w).eval (unaryInterpretation p m) a =
      evalWord (signedTables p m) w (a false) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
      simpa only [wordTerm, Term.eval, unaryInterpretation, evalWord] using
        (congrArg (signedTables p m l) ih)

def compilerTests (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) : List (UnaryTerm (Fin d) × UnaryTerm (Fin d)) :=
  [(.var false, .var true)] ++
  (List.finRange d).map (fun i => (wordTerm [(i,true),(i,false)], .var true)) ++
  (List.finRange d).map (fun i => (wordTerm [(i,false),(i,true)], .var true)) ++
  rels.map (fun r => (wordTerm r, .var true)) ++ [(wordTerm w, .var false)]

theorem valid_compiler_iff (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) (p m : Fin d → A → A) (a : Bool → A) :
    Valid (compilerTests d rels w) (unaryInterpretation p m) a ↔
      a false ≠ a true ∧
      (∀ i, p i (m i (a false)) ≠ a true) ∧
      (∀ i, m i (p i (a false)) ≠ a true) ∧
      (∀ r ∈ rels, evalWord (signedTables p m) r (a false) ≠ a true) ∧
      evalWord (signedTables p m) w (a false) ≠ a false := by
  unfold Valid compilerTests
  simp only [List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map]
  simp [eval_wordTerm, Term.eval, evalWord, signedTables, and_assoc]

theorem compiler_image_eq [Fintype A] (d : ℕ)
    (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))
    (p m : Fin d → A → A) :
    filteredTriples false true (.var false) (compilerTests d rels w)
      (unaryInterpretation p m) = compiledTripleImage rels w p m := by
  classical
  ext o
  simp only [filteredTriples, compiledTripleImage, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(a false, a true), ?_, rfl⟩
    simpa only [compiledPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      ← valid_compiler_iff] using (Finset.mem_filter.mp ha).2
  · rintro ⟨xy, hxy, rfl⟩
    let a : Bool → A := fun b => if b then xy.2 else xy.1
    refine ⟨a, ?_, rfl⟩
    simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [valid_compiler_iff]
    simpa only [compiledPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hxy

theorem all_unary_interpretations (I : Interpretation (Letter S) (fun _ => 1) A) :
    I = unaryInterpretation (fun i a => I (i,true) (fun _ => a))
      (fun i a => I (i,false) (fun _ => a)) := by
  funext l a
  have ha : (fun _ : Fin 1 => a 0) = a := by funext i; rw [Fin.eq_zero i]
  rcases l with ⟨i,b⟩
  cases b <;> simp only [unaryInterpretation, signedTables, Bool.false_eq_true,
    if_false, if_true, ha]

theorem compiler_dispersion_saturation_iff [Fintype A] [Nontrivial A]
    (d : ℕ) (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d))) :
    Fintype.card A * (Fintype.card A - 1) ≤
      dispersionOn (A := A) false true (.var false) (compilerTests d rels w) ↔
    ∃ p m : Fin d → A → A,
      (compiledPairs rels w p m).card = Fintype.card A * (Fintype.card A - 1) := by
  classical
  have hpos : 0 < Fintype.card A * (Fintype.card A - 1) := by
    have hn : 1 < Fintype.card A := Fintype.one_lt_card
    exact Nat.mul_pos (by omega) (by omega)
  rw [threshold_iff_interpretation _ _ _ _ _ hpos]
  constructor
  · rintro ⟨I, hi⟩
    let p := fun i a => I (i,true) (fun _ => a)
    let m := fun i a => I (i,false) (fun _ => a)
    have he : I = unaryInterpretation p m := all_unary_interpretations I
    rw [he, compiler_image_eq, compiledTriple_card] at hi
    refine ⟨p, m, le_antisymm ?_ hi⟩
    have hs : compiledPairs rels w p m ⊆ guardPairs (A := A) := by
      intro xy hxy
      simp only [compiledPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.1⟩
    exact (Finset.card_le_card hs).trans_eq card_guardPairs
  · rintro ⟨p,m,he⟩
    refine ⟨unaryInterpretation p m, ?_⟩
    rw [compiler_image_eq, compiledTriple_card, he]


/-- This is the first headline predicate on the actual compiled C3 instance,
with an existential alphabet size and the maximum over all shared tables. -/
def HardThreshold (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ n * (n - 1) ≤ dispersionOn (A := Fin n)
    false true (.var false) (compilerTests d rels w)

theorem compiler_has_guard (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) :
    (.var false, .var true) ∈ compilerTests d rels w := by
  simp [compilerTests]

theorem hard_threshold_iff_cardinality (d : ℕ)
    (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d))) :
    HardThreshold d rels w ↔ HasFinitePerfectCardinality rels w := by
  classical
  constructor
  · rintro ⟨n, hn, h⟩
    letI : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp (by
      simpa only [Fintype.card_fin] using hn)
    obtain ⟨p,m,hpm⟩ := (compiler_dispersion_saturation_iff (A := Fin n) d rels w).mp
      (by simpa only [Fintype.card_fin] using h)
    exact ⟨Fin n, inferInstance, inferInstance, p, m, hpm⟩
  · rintro ⟨A, hfin, hnt, p, m, h⟩
    letI := hfin
    letI := hnt
    have hc := (compiler_dispersion_saturation_iff (A := A) d rels w).mpr ⟨p,m,h⟩
    have he := dispersion_embedding_le (Fintype.equivFin A).toEmbedding
      false true (.var false) (compilerTests d rels w)
    exact ⟨Fintype.card A, Fintype.one_lt_card, hc.trans he⟩

theorem hard_threshold_iff_quotient (d : ℕ)
    (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d))) :
    HardThreshold d rels w ↔ HasFiniteQuotient rels w :=
  (hard_threshold_iff_cardinality d rels w).trans (finite_cardinality_iff_quotient rels w)

theorem undecidable_hard_threshold (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    ¬ ComputablePred (HardThreshold d rels) := by
  intro h
  exact slobodskoiBridsonWilton (h.of_eq (fun w => hard_threshold_iff_quotient d rels w))

end DisequalityDispersion
