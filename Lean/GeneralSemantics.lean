import Transport
import CompilerBridge

/-! # General output tuples: evaluation, filtered image and maximum (R1)

`tupleEval ts I a` evaluates a finite list of output terms; `filteredImage`
is the image of the valid assignments (those passing every disequality test)
under this tuple map, and `dispersionTuple` is its maximum over all shared
interpretations on a finite alphabet.  Bridges to the baseline triple
semantics (`filteredTriples`, `dispersionOn`) and to the compiled pair image
(`compiledPairs`) are proved, together with attainment, alphabet embedding,
identical-side obstruction and transport along signature equivalences. -/

namespace DisequalityDispersion

variable {V F A : Type} {arity : F → ℕ}

/-- Evaluate a list of output terms. -/
def tupleEval (ts : List (Term V F arity)) (I : Interpretation F arity A) (a : V → A) :
    List A :=
  ts.map (fun t => t.eval I a)

/-- The filtered image of the output tuple. -/
noncomputable def filteredImage [Fintype V] [Fintype A] (ts : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (I : Interpretation F arity A) :
    Finset (List A) := by
  classical
  exact (validAssignments tests I).image (tupleEval ts I)

/-- The maximum filtered image size over all shared tables on `A`. -/
noncomputable def dispersionTuple [Fintype V] [Fintype F] [Fintype A]
    (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity)) : ℕ := by
  classical
  exact Finset.univ.sup (fun I : Interpretation F arity A => (filteredImage ts tests I).card)

theorem image_le_dispersionTuple [Fintype V] [Fintype F] [Fintype A]
    (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) :
    (filteredImage ts tests I).card ≤ dispersionTuple (A := A) ts tests := by
  classical
  exact Finset.le_sup (f := fun J => (filteredImage ts tests J).card) (Finset.mem_univ I)

theorem dispersionTuple_le_of_forall [Fintype V] [Fintype F] [Fintype A]
    (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity)) (N : ℕ)
    (h : ∀ I : Interpretation F arity A, (filteredImage ts tests I).card ≤ N) :
    dispersionTuple (A := A) ts tests ≤ N := by
  classical
  unfold dispersionTuple
  exact Finset.sup_le (fun I _ => h I)

/-- Attainment: a positive threshold is reached by the maximum iff by some table. -/
theorem dispersionTuple_ge_iff [Fintype V] [Fintype F] [Fintype A]
    (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (h : ℕ) (hh : 0 < h) :
    h ≤ dispersionTuple (A := A) ts tests ↔
      ∃ I : Interpretation F arity A, h ≤ (filteredImage ts tests I).card := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  simp only [dispersionTuple, Nat.succ_le_iff, Finset.lt_sup_iff, Finset.mem_univ, true_and]

/-- An identical-side test empties every filtered image. -/
theorem identical_test_dispersionTuple_zero [Fintype V] [Fintype F] [Fintype A]
    (ts : List (Term V F arity)) (u : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hu : (u, u) ∈ tests) :
    dispersionTuple (A := A) ts tests = 0 := by
  classical
  apply Nat.le_zero.mp
  apply dispersionTuple_le_of_forall
  intro I
  have hc : validAssignments tests I = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _ ha
    exact ha (u, u) hu rfl
  simp [filteredImage, hc]

/-! ### Bridge to the baseline triple semantics -/

open Classical in
theorem filteredImage_triple [Fintype V] [Fintype A] (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (I : Interpretation F arity A) :
    filteredImage [.var x, .var y, t] tests I =
      (filteredTriples x y t tests I).image (fun o => [o.1, o.2.1, o.2.2]) := by
  classical
  ext l
  simp only [filteredImage, filteredTriples, Finset.mem_image, tupleEval, List.map_cons,
    List.map_nil, Term.eval]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a x, a y, t.eval I a), ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨o, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem filteredImage_triple_card [Fintype V] [Fintype A] (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (I : Interpretation F arity A) :
    (filteredImage [.var x, .var y, t] tests I).card = (filteredTriples x y t tests I).card := by
  classical
  rw [filteredImage_triple]
  apply Finset.card_image_of_injective
  intro o o' h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- The three-output tuple maximum is the baseline `dispersionOn`. -/
theorem dispersionTuple_triple [Fintype V] [Fintype F] [Fintype A] (x y : V)
    (t : Term V F arity) (tests : List (Term V F arity × Term V F arity)) :
    dispersionTuple (A := A) [.var x, .var y, t] tests = dispersionOn (A := A) x y t tests := by
  classical
  apply le_antisymm
  · apply dispersionTuple_le_of_forall
    intro I
    rw [filteredImage_triple_card]
    exact image_le_dispersion x y t tests I
  · apply SigEquiv.dispersionOn_le_of_forall
    intro I
    rw [← filteredImage_triple_card]
    exact image_le_dispersionTuple _ _ I

/-! ### Bridge to the compiled pair image -/

open Classical in
theorem filteredImage_pair_card [Fintype V] [Fintype A] (x y : V)
    (tests : List (Term V F arity × Term V F arity)) (I : Interpretation F arity A) :
    (filteredImage [.var x, .var y] tests I).card =
      ((validAssignments tests I).image (fun a => (a x, a y))).card := by
  classical
  have : filteredImage [.var x, .var y] tests I =
      ((validAssignments tests I).image (fun a => (a x, a y))).image (fun p => [p.1, p.2]) := by
    ext l
    simp only [filteredImage, Finset.mem_image, tupleEval, List.map_cons, List.map_nil,
      Term.eval]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a x, a y), ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [this]
  apply Finset.card_image_of_injective
  intro p q h
  simp only [List.cons.injEq, and_true] at h
  exact Prod.ext h.1 h.2

open Classical in
theorem compiled_pair_image [Fintype A] (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) (p m : Fin d → A → A) :
    (validAssignments (compilerTests d rels w) (unaryInterpretation p m)).image
        (fun a => (a false, a true)) = compiledPairs rels w p m := by
  classical
  ext xy
  simp only [Finset.mem_image, validAssignments, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa only [compiledPairs, Finset.mem_filter, Finset.mem_univ, true_and,
      ← valid_compiler_iff] using ha
  · intro hxy
    refine ⟨fun b => if b then xy.2 else xy.1, ?_, rfl⟩
    rw [valid_compiler_iff]
    simpa only [compiledPairs, Finset.mem_filter, Finset.mem_univ, true_and] using hxy

/-- The two-output compiled tuple image has the cardinality of `compiledPairs`. -/
theorem filteredImage_compiled_card [Fintype A] (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) (p m : Fin d → A → A) :
    (filteredImage [.var false, .var true] (compilerTests d rels w)
        (unaryInterpretation p m)).card = (compiledPairs rels w p m).card := by
  rw [filteredImage_pair_card, compiled_pair_image]

/-! ### Alphabet extension -/

theorem filteredImage_embedding_le {B : Type} [Fintype V] [Fintype A] [Fintype B] [Nonempty A]
    (e : A ↪ B) (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) :
    (filteredImage ts tests I).card ≤
      (filteredImage ts tests (extendInterpretation e I)).card := by
  classical
  let f : List A → List B := fun l => l.map e
  have hinj : Function.Injective f := List.map_injective_iff.mpr e.injective
  have hsub : (filteredImage ts tests I).image f ⊆
      filteredImage ts tests (extendInterpretation e I) := by
    intro o ho
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨fun v => e (a v), ?_, ?_⟩
    · simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      intro uv huv he
      apply ha uv huv
      rw [eval_extend, eval_extend] at he
      exact e.injective he
    · simp only [tupleEval, f, List.map_map]
      apply List.map_congr_left
      intro t _
      simp only [Function.comp, eval_extend]
  calc (filteredImage ts tests I).card = ((filteredImage ts tests I).image f).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem dispersionTuple_embedding_le {B : Type} [Fintype V] [Fintype F] [Fintype A] [Fintype B]
    [Nonempty A] (e : A ↪ B) (ts : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    dispersionTuple (A := A) ts tests ≤ dispersionTuple (A := B) ts tests := by
  classical
  apply dispersionTuple_le_of_forall
  intro I
  exact (filteredImage_embedding_le e ts tests I).trans (image_le_dispersionTuple _ _ _)

/-! ### Transport along signature equivalences -/

namespace SigEquiv
variable {V' F' : Type} {arity' : F' → ℕ} (σ : SigEquiv V F arity V' F' arity')

theorem filteredImage_rename [Fintype V] [Fintype V'] [Fintype A]
    (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (I' : Interpretation F' arity' A) :
    filteredImage (ts.map σ.rename) (tests.map (fun uv => (σ.rename uv.1, σ.rename uv.2))) I' =
      filteredImage ts tests (σ.pullI I') := by
  classical
  ext o
  simp only [filteredImage, validAssignments, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a', ha', rfl⟩
    refine ⟨fun v => a' (σ.eV v), (σ.Valid_rename tests I' a').mp ha', ?_⟩
    simp only [tupleEval, List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, eval_rename]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun v' => a (σ.eV.symm v'), ?_, ?_⟩
    · rw [σ.Valid_rename tests I']
      simpa only [Equiv.symm_apply_apply] using ha
    · simp only [tupleEval, List.map_map]
      apply List.map_congr_left
      intro t _
      simp only [Function.comp, eval_rename, Equiv.symm_apply_apply]

theorem dispersionTuple_rename [Fintype V] [Fintype F] [Fintype V'] [Fintype F'] [Fintype A]
    (ts : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity)) :
    dispersionTuple (A := A) (ts.map σ.rename)
        (tests.map (fun uv => (σ.rename uv.1, σ.rename uv.2))) =
      dispersionTuple (A := A) ts tests := by
  apply le_antisymm
  · apply dispersionTuple_le_of_forall
    intro I'
    rw [σ.filteredImage_rename]
    exact image_le_dispersionTuple ts tests (σ.pullI I')
  · apply dispersionTuple_le_of_forall
    intro I
    obtain ⟨I', rfl⟩ := σ.pullI_surjective I
    rw [← σ.filteredImage_rename]
    exact image_le_dispersionTuple _ _ I'

end SigEquiv

end DisequalityDispersion
