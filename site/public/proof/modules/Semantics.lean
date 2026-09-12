import Threshold

namespace DisequalityDispersion
variable {V F A : Type} {arity : F → ℕ}

abbrev Interpretation (F : Type) (arity : F → ℕ) (A : Type) :=
  (f : F) → (Fin (arity f) → A) → A

def Valid (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) (a : V → A) : Prop :=
  ∀ uv ∈ tests, uv.1.eval I a ≠ uv.2.eval I a

noncomputable def validAssignments [Fintype V] [Fintype A]
    (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) : Finset (V → A) := by
  classical
  exact Finset.univ.filter (Valid tests I)

noncomputable def filteredTriples [Fintype V] [Fintype A]
    (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) : Finset (A × A × A) := by
  classical
  exact (validAssignments tests I).image (fun a => (a x, a y, t.eval I a))

noncomputable def dispersionOn [Fintype V] [Fintype F] [Fintype A]
    (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : ℕ := by
  classical
  exact Finset.univ.sup (fun I : Interpretation F arity A =>
    (filteredTriples x y t tests I).card)

theorem image_le_dispersion [Fintype V] [Fintype F] [Fintype A]
    (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) :
    (filteredTriples x y t tests I).card ≤ dispersionOn (A := A) x y t tests := by
  classical
  exact Finset.le_sup (f := fun J => (filteredTriples x y t tests J).card)
    (Finset.mem_univ I)

theorem threshold_iff_interpretation [Fintype V] [Fintype F] [Fintype A]
    (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (k : ℕ) (hk : 0 < k) :
    k ≤ dispersionOn (A := A) x y t tests ↔
      ∃ I : Interpretation F arity A, k ≤ (filteredTriples x y t tests I).card := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [dispersionOn, Nat.succ_le_iff, Finset.lt_sup_iff,
    Finset.mem_univ, true_and]

theorem identical_test_zero [Fintype V] [Fintype F] [Fintype A]
    (x y : V) (t u : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hu : (u,u) ∈ tests) :
    dispersionOn (A := A) x y t tests = 0 := by
  classical
  have hc (I : Interpretation F arity A) : validAssignments tests I = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _ hv
    exact hv (u,u) hu rfl
  simp [dispersionOn, filteredTriples, hc]

theorem retained_term_dispersion_le [Fintype V] [Fintype F] [Fintype A]
    (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity))
    (hguard : (.var x, .var y) ∈ tests)
    (huses : ∀ z, t.Uses z → z = x ∨ z = y) :
    dispersionOn (A := A) x y t tests ≤ Fintype.card A * (Fintype.card A - 1) := by
  classical
  apply Finset.sup_le
  intro I _
  apply card_retained_term_le _ x y t I _ huses
  intro a ha
  have hv := (Finset.mem_filter.mp ha).2
  exact hv (.var x, .var y) hguard


noncomputable def extendInterpretation {B : Type} [Nonempty A]
    (e : A ↪ B) (I : Interpretation F arity A) : Interpretation F arity B :=
  fun f as => e (I f (fun i => Function.invFun e (as i)))

theorem eval_extend {B : Type} [Nonempty A] (e : A ↪ B)
    (I : Interpretation F arity A) (a : V → A) (t : Term V F arity) :
    t.eval (extendInterpretation e I) (fun v => e (a v)) = e (t.eval I a) := by
  induction t with
  | var v => rfl
  | app f ts ih =>
      have hi (a : A) : Function.invFun e (e a) = a :=
        Function.leftInverse_invFun e.injective a
      simp only [Term.eval, extendInterpretation, ih, hi]

theorem filtered_image_embedding_le {B : Type} [Fintype V] [Fintype A]
    [Fintype B] [Nonempty A] (e : A ↪ B) (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) :
    (filteredTriples x y t tests I).card ≤
      (filteredTriples x y t tests (extendInterpretation e I)).card := by
  classical
  let f : A × A × A → B × B × B := fun o => (e o.1, e o.2.1, e o.2.2)
  have hinj : Function.Injective f := by
    intro p q h
    exact Prod.ext (e.injective (congrArg Prod.fst h))
      (Prod.ext (e.injective (congrArg (fun o => o.2.1) h))
        (e.injective (congrArg (fun o => o.2.2) h)))
  have hsub : (filteredTriples x y t tests I).image f ⊆
      filteredTriples x y t tests (extendInterpretation e I) := by
    intro o ho
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ho
    simp only [filteredTriples, Finset.mem_image] at hp ⊢
    obtain ⟨a, ha, rfl⟩ := hp
    refine ⟨(fun v => e (a v)), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro uv huv he
      rw [eval_extend, eval_extend] at he
      exact (Finset.mem_filter.mp ha).2 uv huv (e.injective he)
    · simp only [eval_extend, f]
  calc
    (filteredTriples x y t tests I).card =
        ((filteredTriples x y t tests I).image f).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

theorem dispersion_embedding_le {B : Type} [Fintype V] [Fintype F]
    [Fintype A] [Fintype B] [Nonempty A] (e : A ↪ B)
    (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) :
    dispersionOn (A := A) x y t tests ≤ dispersionOn (A := B) x y t tests := by
  classical
  apply Finset.sup_le
  intro I _
  exact (filtered_image_embedding_le e x y t tests I).trans
    (image_le_dispersion x y t tests (extendInterpretation e I))

end DisequalityDispersion
