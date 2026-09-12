import Tagged

/-! Positive and negative strict-threshold instances with exactly the same
three source variables and the same sole disequality test. -/
namespace DisequalityDispersion
variable {F A : Type} {arity : F → ℕ}

def pairGuard : List (Term (Fin 3) F arity × Term (Fin 3) F arity) :=
  [(.var 0, .var 1)]

theorem valid_pairGuard (I : Interpretation F arity A) (a : Fin 3 → A) :
    Valid pairGuard I a ↔ a 0 ≠ a 1 := by
  simp [Valid, pairGuard, Term.eval]

theorem identity_triple_image [Fintype A] [DecidableEq A] (I : Interpretation F arity A) :
    filteredTriples 0 1 (.var 2) pairGuard I =
      ((guardPairs (A := A)).product Finset.univ).image
        (fun p : (A × A) × A => (p.1.1,p.1.2,p.2)) := by
  classical
  ext o
  simp only [filteredTriples, Finset.mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨((a 0,a 1),a 2), ?_, rfl⟩
    simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and,
      valid_pairGuard] at ha
    simp [guardPairs, ha]
  · rintro ⟨p,hp,rfl⟩
    refine ⟨![p.1.1,p.1.2,p.2], ?_, ?_⟩
    · simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and,
        valid_pairGuard]
      simpa [guardPairs] using hp
    · simp [Term.eval]

theorem identity_triple_image_card [Fintype A] (I : Interpretation F arity A) :
    (filteredTriples 0 1 (.var 2) pairGuard I).card =
      Fintype.card A ^ 2 * (Fintype.card A - 1) := by
  classical
  rw [identity_triple_image]
  have hinj : Function.Injective (fun p : (A × A) × A => (p.1.1,p.1.2,p.2)) := by
    intro p q h
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun o : A × A × A => o.1) h
      · exact congrArg (fun o : A × A × A => o.2.1) h
    · exact congrArg (fun o : A × A × A => o.2.2) h
  rw [Finset.card_image_of_injective _ hinj, Finset.product_eq_sprod,
    Finset.card_product, card_guardPairs,
    Finset.card_univ]
  ring

theorem identity_triple_dispersion [Fintype F] [Fintype A] [Nonempty A] :
    dispersionOn (F := F) (arity := arity) (A := A) 0 1 (.var 2) pairGuard =
      Fintype.card A ^ 2 * (Fintype.card A - 1) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro I _
    exact (identity_triple_image_card I).le
  · let I : Interpretation F arity A := fun _ _ => Classical.choice inferInstance
    exact (identity_triple_image_card I).symm.le.trans
      (image_le_dispersion 0 1 (.var 2) pairGuard I)

theorem repeated_triple_image [Fintype A] [DecidableEq A] (I : Interpretation F arity A) :
    filteredTriples 0 1 (.var 0) pairGuard I =
      (guardPairs (A := A)).image (fun p => (p.1,p.2,p.1)) := by
  classical
  ext o
  simp only [filteredTriples, Finset.mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨(a 0,a 1), ?_, rfl⟩
    simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and,
      valid_pairGuard] at ha
    simp [guardPairs, ha]
  · rintro ⟨p,hp,rfl⟩
    refine ⟨![p.1,p.2,p.1], ?_, ?_⟩
    · simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and,
        valid_pairGuard]
      simpa [guardPairs] using hp
    · simp [Term.eval]

theorem repeated_triple_dispersion [Fintype F] [Fintype A] [Nonempty A] :
    dispersionOn (F := F) (arity := arity) (A := A) 0 1 (.var 0) pairGuard =
      Fintype.card A * (Fintype.card A - 1) := by
  classical
  have hc (I : Interpretation F arity A) :
      (filteredTriples 0 1 (.var 0) pairGuard I).card =
        Fintype.card A * (Fintype.card A - 1) := by
    rw [repeated_triple_image]
    rw [card_append_determined (guardPairs (A := A)) (fun p => p.1), card_guardPairs]
  apply le_antisymm
  · apply Finset.sup_le
    intro I _
    exact (hc I).le
  · let I : Interpretation F arity A := fun _ _ => Classical.choice inferInstance
    exact (hc I).symm.le.trans (image_le_dispersion 0 1 (.var 0) pairGuard I)

theorem strict_positive_example [Fintype F] :
    2 * (2 - 1) + 1 ≤
      dispersionOn (F := F) (arity := arity) (A := Fin 2) 0 1 (.var 2) pairGuard := by
  rw [identity_triple_dispersion]
  norm_num

theorem strict_negative_example [Fintype F] :
    ¬ ∃ n : ℕ, 2 ≤ n ∧ n * (n - 1) + 1 ≤
      dispersionOn (F := F) (arity := arity) (A := Fin n) 0 1 (.var 0) pairGuard := by
  rintro ⟨n,hn,h⟩
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [repeated_triple_dispersion, Fintype.card_fin] at h
  omega

end DisequalityDispersion
