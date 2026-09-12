import Tagged

/-! # Transport of dispersion along signature equivalences

Renaming sources and symbols along bijections (with matching arities) does
not change the shared-table maximum image size `dispersionOn`.  This is the
bridge between the encoded instance types `Fin k`, `Fin m` and the abstract
types used by the existing hard compiler (`Bool`, `Letter (Fin d)`). -/

namespace DisequalityDispersion

/-- A signature equivalence: bijections on sources and symbols preserving arity. -/
structure SigEquiv (V F : Type) (arity : F → ℕ) (V' F' : Type) (arity' : F' → ℕ) where
  eV : V ≃ V'
  eF : F ≃ F'
  har : ∀ f, arity' (eF f) = arity f

variable {V F : Type} {arity : F → ℕ} {V' F' : Type} {arity' : F' → ℕ} {A : Type}

namespace SigEquiv
variable (σ : SigEquiv V F arity V' F' arity')

/-- Rename a term along a signature equivalence. -/
def rename : Term V F arity → Term V' F' arity'
  | .var v => .var (σ.eV v)
  | .app f ts => .app (σ.eF f) (fun i => rename (ts (Fin.cast (σ.har f) i)))

/-- Pull an interpretation of the renamed signature back to the original one. -/
def pullI (I' : Interpretation F' arity' A) : Interpretation F arity A :=
  fun f args => I' (σ.eF f) (fun i => args (Fin.cast (σ.har f) i))

theorem eval_rename (I' : Interpretation F' arity' A) (a' : V' → A) (t : Term V F arity) :
    (σ.rename t).eval I' a' = t.eval (σ.pullI I') (fun v => a' (σ.eV v)) := by
  induction t with
  | var v => rfl
  | app f ts ih =>
      simp only [rename, Term.eval, pullI]
      congr 1
      funext i
      exact ih _

theorem Uses_rename (t : Term V F arity) (z : V) :
    (σ.rename t).Uses (σ.eV z) ↔ t.Uses z := by
  induction t with
  | var v =>
      simp only [rename, Term.Uses]
      exact σ.eV.injective.eq_iff
  | app f ts ih =>
      simp only [rename, Term.Uses]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨Fin.cast (σ.har f) i, (ih _).mp hi⟩
      · rintro ⟨i, hi⟩
        refine ⟨Fin.cast (σ.har f).symm i, ?_⟩
        have : Fin.cast (σ.har f) (Fin.cast (σ.har f).symm i) = i := by
          ext; rfl
        rw [this]
        exact (ih i).mpr hi

/-- The fibrewise equivalence of table types for one symbol. -/
def tableEquiv (f : F) :
    ((Fin (arity f) → A) → A) ≃ ((Fin (arity' (σ.eF f)) → A) → A) :=
  Equiv.arrowCongr (Equiv.arrowCongr (finCongr (σ.har f).symm) (Equiv.refl A)) (Equiv.refl A)

/-- The equivalence of interpretations induced by a signature equivalence. -/
def interpEquiv : Interpretation F arity A ≃ Interpretation F' arity' A :=
  Equiv.piCongr σ.eF (fun f => σ.tableEquiv (A := A) f)

theorem interpEquiv_symm_apply (I' : Interpretation F' arity' A) :
    (σ.interpEquiv (A := A)).symm I' = σ.pullI I' := by
  rfl

theorem pullI_surjective : Function.Surjective (σ.pullI (A := A)) := by
  intro I
  exact ⟨σ.interpEquiv I, by rw [← interpEquiv_symm_apply, Equiv.symm_apply_apply]⟩

theorem Valid_rename (tests : List (Term V F arity × Term V F arity))
    (I' : Interpretation F' arity' A) (a' : V' → A) :
    Valid (tests.map (fun uv => (σ.rename uv.1, σ.rename uv.2))) I' a' ↔
      Valid tests (σ.pullI I') (fun v => a' (σ.eV v)) := by
  unfold Valid
  simp only [List.forall_mem_map, eval_rename]

theorem filteredTriples_rename [Fintype V] [Fintype V'] [Fintype A]
    (x y : V) (t : Term V F arity) (tests : List (Term V F arity × Term V F arity))
    (I' : Interpretation F' arity' A) :
    filteredTriples (σ.eV x) (σ.eV y) (σ.rename t)
        (tests.map (fun uv => (σ.rename uv.1, σ.rename uv.2))) I' =
      filteredTriples x y t tests (σ.pullI I') := by
  classical
  ext o
  simp only [filteredTriples, validAssignments, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a', ha', rfl⟩
    refine ⟨fun v => a' (σ.eV v), (σ.Valid_rename tests I' a').mp ha', ?_⟩
    simp only [eval_rename]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun v' => a (σ.eV.symm v'), ?_, ?_⟩
    · rw [σ.Valid_rename tests I']
      simpa only [Equiv.symm_apply_apply] using ha
    · simp only [Equiv.symm_apply_apply, eval_rename]

theorem dispersionOn_le_of_forall [Fintype V] [Fintype F] [Fintype A]
    (x y : V) (t : Term V F arity) (tests : List (Term V F arity × Term V F arity)) (N : ℕ)
    (h : ∀ I : Interpretation F arity A, (filteredTriples x y t tests I).card ≤ N) :
    dispersionOn (A := A) x y t tests ≤ N := by
  classical
  unfold dispersionOn
  exact Finset.sup_le (fun I _ => h I)

/-- Dispersion is invariant under renaming along a signature equivalence. -/
theorem dispersionOn_rename [Fintype V] [Fintype F] [Fintype V'] [Fintype F'] [Fintype A]
    (x y : V) (t : Term V F arity) (tests : List (Term V F arity × Term V F arity)) :
    dispersionOn (A := A) (σ.eV x) (σ.eV y) (σ.rename t)
        (tests.map (fun uv => (σ.rename uv.1, σ.rename uv.2))) =
      dispersionOn (A := A) x y t tests := by
  apply le_antisymm
  · apply dispersionOn_le_of_forall
    intro I'
    rw [σ.filteredTriples_rename]
    exact image_le_dispersion x y t tests (σ.pullI I')
  · apply dispersionOn_le_of_forall
    intro I
    obtain ⟨I', rfl⟩ := σ.pullI_surjective I
    rw [← σ.filteredTriples_rename]
    exact image_le_dispersion _ _ _ _ I'

end SigEquiv
end DisequalityDispersion
