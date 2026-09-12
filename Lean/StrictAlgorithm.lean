import EncodedSyntax

/-! # The strict-threshold decision procedure (T2, correctness part)

`strictDecide` validates the encoded instance, computes canonical identifiers,
rejects any test whose two sides have the same identifier, and accepts iff the
output node's occurrence flag records a source outside `{x, y}`.  Its answer is
proved equal to the actual existential strict predicate `Strict` through
`strict_threshold_iff`. -/

namespace DisequalityDispersion.Encoded
namespace Instance

variable (γ : Instance)

/-- Every test has two distinct identifiers. -/
def testsDistinct (ids : List ℕ) : Bool :=
  γ.tests.all (fun ij => !(ids.getD ij.1 0 == ids.getD ij.2 0))

/-- The executable strict-threshold decision procedure. -/
def strictDecide : Bool :=
  γ.isValid && γ.testsDistinct γ.canonIds && γ.usesOther.getD γ.t false

theorem testsDistinct_iff (hv : γ.Valid) :
    γ.testsDistinct γ.canonIds = true ↔ ∀ uv ∈ γ.testTerms hv, uv.1 ≠ uv.2 := by
  have htests := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  unfold testsDistinct testTerms
  simp only [List.all_eq_true, List.forall_mem_map, Bool.not_eq_eq_eq_not, Bool.not_true,
    beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro h ij hij
    have := h ij hij
    rw [γ.canonIds_eq_iff hv ij.1 ij.2 (htests ij hij).1 (htests ij hij).2] at this
    exact this
  · intro h ij hij
    have := h ij hij
    rw [γ.canonIds_eq_iff hv ij.1 ij.2 (htests ij hij).1 (htests ij hij).2]
    exact this

/-- Boolean correctness of the strict procedure against the semantic predicate. -/
theorem strictDecide_iff : γ.strictDecide = true ↔ γ.Strict := by
  unfold strictDecide Strict
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hv, hdist⟩, hflag⟩ := h
    have hv' : γ.Valid := hv
    refine ⟨hv', ?_⟩
    have ht := (γ.valid_iff.mp hv').2.2.2.2.2.2.2.1
    have hdist' := (γ.testsDistinct_iff hv').mp hdist
    have hflag' := (γ.usesOther_getD hv' γ.t ht).mp hflag
    exact (strict_threshold_iff (γ.xv hv') (γ.yv hv') (γ.xv_ne_yv hv') (γ.outTerm hv')
      (γ.testTerms hv') (γ.guard_mem_testTerms hv')).mpr ⟨hdist', hflag'⟩
  · rintro ⟨hv, hn⟩
    have ht := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.1
    obtain ⟨hdist, huse⟩ := (strict_threshold_iff (γ.xv hv) (γ.yv hv) (γ.xv_ne_yv hv)
      (γ.outTerm hv) (γ.testTerms hv) (γ.guard_mem_testTerms hv)).mp hn
    simp only [Bool.and_eq_true]
    exact ⟨⟨hv, (γ.testsDistinct_iff hv).mpr hdist⟩, (γ.usesOther_getD hv γ.t ht).mpr huse⟩

/-- Malformed encodings are rejected. -/
theorem strictDecide_of_invalid (h : ¬ γ.Valid) : γ.strictDecide = false := by
  unfold strictDecide
  have : γ.isValid = false := by
    unfold Valid at h
    exact Bool.eq_false_iff.mpr h
  simp [this]

/-- `Strict` implies `Lower` (the one-unit gap is one-directional). -/
theorem Lower_of_Strict (h : γ.Strict) : γ.Lower := by
  obtain ⟨hv, n, hn, hD⟩ := h
  exact ⟨hv, n, hn, le_trans (Nat.le_succ _) hD⟩

end Instance
end DisequalityDispersion.Encoded
