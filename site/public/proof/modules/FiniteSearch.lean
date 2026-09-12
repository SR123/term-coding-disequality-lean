import StrictAlgorithm
import Transport

/-! # Effective finite search for a fixed alphabet (T4, executable part)

For a valid encoded instance and a fixed `n`, `dispersionExec γ hv n`
enumerates every total operation table on `Fin n` (through the computable
`Fintype` structure of the interpretation type), every source assignment,
filters by the executable test evaluator, collects the distinct output triples
and takes the maximum.  It is proved equal to the noncomputable specification
`dispersion hv n` (that is, to `dispersionOn`).  `lowerThresholdAt γ n` is the
resulting Boolean finite decision procedure for the threshold at one `n`, and
`Lower γ ↔ ∃ n, lowerThresholdAt γ n = true` is the semidecision statement by
increasing `n`.  Only the executable definitions and their agreement are
established here; the packaging in mathlib's `REPred` framework is not. -/

namespace DisequalityDispersion.Encoded
namespace Instance

variable (γ : Instance)

/-- Executable valid-assignment set. -/
def validAssignmentsExec (n : ℕ) (I : Interpretation (Fin γ.m) γ.arity (Fin n))
    (d : Fin n) : Finset (Fin γ.k → Fin n) :=
  Finset.univ.filter (fun a => γ.passesTests I a d = true)

/-- Executable filtered triple image. -/
def filteredTriplesExec (hv : γ.Valid) (n : ℕ) (I : Interpretation (Fin γ.m) γ.arity (Fin n))
    (d : Fin n) : Finset (Fin n × Fin n × Fin n) :=
  (γ.validAssignmentsExec n I d).image
    (fun a => (a (γ.xv hv), a (γ.yv hv), (γ.evalNodes I a d).getD γ.t d))

theorem filteredTriplesExec_eq (hv : γ.Valid) (n : ℕ)
    (I : Interpretation (Fin γ.m) γ.arity (Fin n)) (d : Fin n) :
    γ.filteredTriplesExec hv n I d =
      filteredTriples (γ.xv hv) (γ.yv hv) (γ.outTerm hv) (γ.testTerms hv) I := by
  classical
  have ht := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.1
  ext o
  simp only [filteredTriplesExec, validAssignmentsExec, filteredTriples, validAssignments,
    Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, (γ.passesTests_iff hv I a d).mp ha, ?_⟩
    rw [γ.evalNodes_getD hv I a d γ.t ht]
    rfl
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, (γ.passesTests_iff hv I a d).mpr ha, ?_⟩
    rw [γ.evalNodes_getD hv I a d γ.t ht]
    rfl

/-- The executable finite maximum over all tables on `Fin n`. -/
def dispersionExec (hv : γ.Valid) (n : ℕ) : ℕ :=
  if hn : 0 < n then
    (Finset.univ : Finset (Interpretation (Fin γ.m) γ.arity (Fin n))).sup
      (fun I => (γ.filteredTriplesExec hv n I ⟨0, hn⟩).card)
  else 0

/-- Agreement of the finite search with the noncomputable specification. -/
theorem dispersionExec_eq (hv : γ.Valid) (n : ℕ) : γ.dispersionExec hv n = γ.dispersion hv n := by
  unfold dispersionExec Instance.dispersion
  split
  · rename_i hn
    apply le_antisymm
    · apply Finset.sup_le
      intro I _
      rw [γ.filteredTriplesExec_eq]
      exact image_le_dispersion _ _ _ _ I
    · apply SigEquiv.dispersionOn_le_of_forall
      intro I
      rw [← γ.filteredTriplesExec_eq hv n I ⟨0, hn⟩]
      exact Finset.le_sup (f := fun J => (γ.filteredTriplesExec hv n J ⟨0, hn⟩).card)
        (Finset.mem_univ I)
  · rename_i hn
    have h0 : n = 0 := by omega
    subst h0
    symm
    apply Nat.le_zero.mp
    apply SigEquiv.dispersionOn_le_of_forall
    intro I
    exact (Finset.card_le_univ _).trans (by simp)

/-- Boolean finite decision of the lower threshold at one alphabet size. -/
def lowerThresholdAt (n : ℕ) : Bool :=
  if hv : γ.Valid then decide (2 ≤ n ∧ n * (n - 1) ≤ γ.dispersionExec hv n) else false

theorem lowerThresholdAt_iff (n : ℕ) :
    γ.lowerThresholdAt n = true ↔ ∃ hv : γ.Valid, 2 ≤ n ∧ n * (n - 1) ≤ γ.dispersion hv n := by
  unfold lowerThresholdAt
  split
  · rename_i hv
    rw [decide_eq_true_iff, γ.dispersionExec_eq]
    exact ⟨fun h => ⟨hv, h⟩, fun ⟨_, h⟩ => h⟩
  · rename_i hv
    simp only [Bool.false_eq_true, false_iff, not_exists]
    intro hv' _
    exact hv hv'

/-- Semidecision of `Lower` by increasing alphabet size. -/
theorem Lower_iff_exists_lowerThresholdAt : γ.Lower ↔ ∃ n, γ.lowerThresholdAt n = true := by
  unfold Lower
  constructor
  · rintro ⟨hv, n, hn, h⟩
    exact ⟨n, (γ.lowerThresholdAt_iff n).mpr ⟨hv, hn, h⟩⟩
  · rintro ⟨n, h⟩
    obtain ⟨hv, hn, h⟩ := (γ.lowerThresholdAt_iff n).mp h
    exact ⟨hv, n, hn, h⟩

/-- The strict threshold at one alphabet size, by finite search. -/
def strictThresholdAt (n : ℕ) : Bool :=
  if hv : γ.Valid then decide (2 ≤ n ∧ n * (n - 1) + 1 ≤ γ.dispersionExec hv n) else false

theorem strictThresholdAt_iff (n : ℕ) :
    γ.strictThresholdAt n = true ↔
      ∃ hv : γ.Valid, 2 ≤ n ∧ n * (n - 1) + 1 ≤ γ.dispersion hv n := by
  unfold strictThresholdAt
  split
  · rename_i hv
    rw [decide_eq_true_iff, γ.dispersionExec_eq]
    exact ⟨fun h => ⟨hv, h⟩, fun ⟨_, h⟩ => h⟩
  · rename_i hv
    simp only [Bool.false_eq_true, false_iff, not_exists]
    intro hv' _
    exact hv hv'

theorem Strict_iff_exists_strictThresholdAt : γ.Strict ↔ ∃ n, γ.strictThresholdAt n = true := by
  unfold Strict
  constructor
  · rintro ⟨hv, n, hn, h⟩
    exact ⟨n, (γ.strictThresholdAt_iff n).mpr ⟨hv, hn, h⟩⟩
  · rintro ⟨n, h⟩
    obtain ⟨hv, hn, h⟩ := (γ.strictThresholdAt_iff n).mp h
    exact ⟨hv, n, hn, h⟩

end Instance
end DisequalityDispersion.Encoded
