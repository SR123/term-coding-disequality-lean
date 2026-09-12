import Core

/-! Connect the concrete signed-word model to a finite quotient of mathlib's
PresentedGroup. Slobodskoi--Bridson--Wilton remains an explicit input. -/
namespace DisequalityDispersion
variable {S Q R : Type} [Group Q] [Group R]

theorem groupWord_map (φ : Q →* R) (g : S → Q) (w : List (Letter S)) :
    φ (groupWord g w) = groupWord (fun i => φ (g i)) w := by
  induction w with
  | nil => simp [groupWord]
  | cons l w ih =>
      have hl : φ (groupLetter g l) = groupLetter (fun i => φ (g i)) l := by
        rcases l with ⟨i, b⟩
        cases b <;> simp [groupLetter]
      simpa only [groupWord, List.map_cons, List.prod_cons, map_mul, hl] using
        congrArg (fun q => groupLetter (fun i => φ (g i)) l * q) ih

def freeWord (w : List (Letter S)) : FreeGroup S := groupWord FreeGroup.of w

def presentationRels (rels : List (List (Letter S))) : Set (FreeGroup S) :=
  {r | ∃ v ∈ rels, freeWord v = r}

abbrev WordPresentation (rels : List (List (Letter S))) :=
  PresentedGroup (presentationRels rels)

def presentedWord (rels : List (List (Letter S))) (w : List (Letter S)) :
    WordPresentation rels := PresentedGroup.mk _ (freeWord w)

theorem lift_freeWord (g : S → Q) (w : List (Letter S)) :
    FreeGroup.lift g (freeWord w) = groupWord g w := by
  rw [freeWord, groupWord_map]
  congr 1
  funext i
  exact FreeGroup.lift_apply_of

theorem presentedWord_eq (rels : List (List (Letter S))) (w : List (Letter S)) :
    presentedWord rels w =
      groupWord (PresentedGroup.of : S → WordPresentation rels) w := by
  exact groupWord_map (PresentedGroup.mk _) FreeGroup.of w

theorem presented_relator (rels : List (List (Letter S)))
    (r : List (Letter S)) (hr : r ∈ rels) : presentedWord rels r = 1 := by
  exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩

def HasFinitePresentationHom (rels : List (List (Letter S)))
    (w : List (Letter S)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Fintype Q)
    (φ : WordPresentation rels →* Q), φ (presentedWord rels w) ≠ 1

def HasFiniteQuotient (rels : List (List (Letter S)))
    (w : List (Letter S)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Fintype Q)
    (φ : WordPresentation rels →* Q),
    Function.Surjective φ ∧ φ (presentedWord rels w) ≠ 1

theorem finite_model_iff_presentation_hom (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFiniteGroupWitness rels w ↔ HasFinitePresentationHom rels w := by
  constructor
  · rintro ⟨Q, hQ, hfin, g, hr, hw⟩
    letI := hQ
    letI := hfin
    have hl : ∀ r ∈ presentationRels rels, FreeGroup.lift g r = 1 := by
      rintro r ⟨v, hv, rfl⟩
      rw [lift_freeWord]
      exact hr v hv
    let φ : WordPresentation rels →* Q := PresentedGroup.toGroup hl
    have hφ (v : List (Letter S)) : φ (presentedWord rels v) = groupWord g v := by
      rw [presentedWord_eq, groupWord_map]
      congr 1
      funext i
      exact PresentedGroup.toGroup.of hl
    exact ⟨Q, hQ, hfin, φ, by simpa only [hφ] using hw⟩
  · rintro ⟨Q, hQ, hfin, φ, hw⟩
    letI := hQ
    letI := hfin
    let g : S → Q := fun i => φ (PresentedGroup.of i)
    have hφ (v : List (Letter S)) : φ (presentedWord rels v) = groupWord g v := by
      rw [presentedWord_eq, groupWord_map]
    refine ⟨Q, hQ, hfin, g, ?_, by simpa only [hφ] using hw⟩
    intro r hr
    rw [← hφ, presented_relator rels r hr, map_one]

theorem finite_hom_iff_quotient (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFinitePresentationHom rels w ↔ HasFiniteQuotient rels w := by
  classical
  constructor
  · rintro ⟨Q, hQ, hfin, φ, hw⟩
    letI := hQ
    letI := hfin
    refine ⟨φ.range, inferInstance, inferInstance, φ.rangeRestrict, ?_, ?_⟩
    · exact φ.rangeRestrict_surjective
    · intro h
      apply hw
      exact congrArg Subtype.val h
  · rintro ⟨Q, hQ, hfin, φ, _, hw⟩
    exact ⟨Q, hQ, hfin, φ, hw⟩

theorem finite_model_iff_quotient (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFiniteGroupWitness rels w ↔ HasFiniteQuotient rels w :=
  (finite_model_iff_presentation_hom rels w).trans (finite_hom_iff_quotient rels w)

theorem finite_cardinality_iff_quotient (rels : List (List (Letter S)))
    (w : List (Letter S)) :
    HasFinitePerfectCardinality rels w ↔ HasFiniteQuotient rels w :=
  (finite_cardinality_reduction rels w).trans (finite_model_iff_quotient rels w)

/-- Exact named input interface: noncomputability of separation in a finite
quotient of one fixed finitely presented group, on lists of signed letters. -/
theorem undecidable_perfection_of_quotient_separation (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    ¬ ComputablePred (HasFinitePerfectCardinality rels) := by
  intro h
  exact slobodskoiBridsonWilton
    (h.of_eq (fun w => finite_cardinality_iff_quotient rels w))

end DisequalityDispersion
