import GeneralAlgorithm

/-! # Size of the strict witness on encoded instances (R5, size lemma)

For a valid general encoded instance the support size `s` is at most
`k + |nodes|` (declared sources plus nodes), and the witness alphabet
`n = s^(k+1)` of `strict_witness'` has binary length at most
`(k + 1) · size(k_sources + |nodes|)`: polynomial in the input for every fixed
degree.  No polynomial-size explicit table is claimed. -/

namespace DisequalityDispersion.Encoded
namespace GInstance

variable (g : GInstance)

open Classical in
/-- The support of the decoded general instance consists of sources and decoded nodes. -/
theorem tupleSupport_subset (hv : g.Valid) :
    tupleSupport (g.outputs hv) (g.tests hv) ⊆
      Finset.univ.image Term.var ∪
        (List.range g.base.nodes.length).toFinset.image (g.base.termD (g.baseValid hv)) := by
  have hout := (g.valid_iff.mp hv).2
  have htests := (g.base.valid_iff.mp (g.baseValid hv)).2.2.2.2.2.2.2.2.1
  intro u hu
  unfold tupleSupport at hu
  simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset] at hu
  rcases hu with (hu | ⟨t, ht, hu⟩) | ⟨uv, huv, hu⟩
  · exact Finset.mem_union_left _ hu
  · rw [g.outputs_eq hv] at ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact Finset.mem_union_right _
      (g.base.support_termD_subset (g.baseValid hv) j (g.outNodes_lt hv j hj) hu)
  · unfold GInstance.tests Instance.testTerms at huv
    rw [List.mem_map] at huv
    obtain ⟨ij, hij, rfl⟩ := huv
    obtain ⟨h1, h2⟩ := htests ij hij
    rcases hu with hu | hu
    · exact Finset.mem_union_right _ (g.base.support_termD_subset (g.baseValid hv) ij.1 h1 hu)
    · exact Finset.mem_union_right _ (g.base.support_termD_subset (g.baseValid hv) ij.2 h2 hu)

open Classical in
/-- `s ≤ k + |nodes|`. -/
theorem tupleSupport_card_le (hv : g.Valid) :
    (tupleSupport (g.outputs hv) (g.tests hv)).card ≤ g.base.k + g.base.nodes.length := by
  refine (Finset.card_le_card (g.tupleSupport_subset hv)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  apply Nat.add_le_add
  · refine Finset.card_image_le.trans ?_
    simp [Instance.k]
  · refine Finset.card_image_le.trans ?_
    refine (List.toFinset_card_le _).trans ?_
    simp

/-- Binary length of a power: `size (s^(k+1)) ≤ (k+1) · size s`. -/
theorem size_pow_le (s k : ℕ) : (s ^ (k + 1)).size ≤ (k + 1) * s.size := by
  rw [Nat.size_le, mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left (Nat.lt_size_self s) (Nat.succ_ne_zero k)

/-- **Polynomial witness length**: on any instance the alphabet `s^(k+1)` of the strict
witness has binary length at most `(k+1) · size(k_sources + |nodes|)`. -/
theorem witness_size_le (hv : g.Valid) (k : ℕ) :
    ((tupleSupport (g.outputs hv) (g.tests hv)).card ^ (k + 1)).size ≤
      (k + 1) * (g.base.k + g.base.nodes.length).size :=
  (size_pow_le _ k).trans (Nat.mul_le_mul_left _ (Nat.size_le_size (g.tupleSupport_card_le hv)))

/-- The strict witness on a strict yes-instance, with the size bound (`k ≥ 2`). -/
theorem strict_witness_encoded (hv : g.Valid) (k : ℕ) (hk : 2 ≤ k) (h : g.Strict k) :
    let s := (tupleSupport (g.outputs hv) (g.tests hv)).card
    2 ≤ s ^ (k + 1) ∧ threshold k (s ^ (k + 1)) + 1 ≤ g.dispersion hv (s ^ (k + 1)) ∧
      (s ^ (k + 1)).size ≤ (k + 1) * (g.base.k + g.base.nodes.length).size := by
  obtain ⟨hv', hs⟩ := h
  obtain ⟨distinct, hρ⟩ := (strict_degree_iff' k hk (g.base.xv (g.baseValid hv'))
    (g.base.yv (g.baseValid hv')) (g.base.xv_ne_yv _) (g.outputs hv') (g.tests hv')
    (g.var_x_mem_outputs hv') (g.var_y_mem_outputs hv') (g.guard_mem_tests hv')).mp hs
  obtain ⟨h2, hw⟩ := strict_witness' k (by omega) (g.base.xv (g.baseValid hv'))
    (g.base.yv (g.baseValid hv')) (g.base.xv_ne_yv _) (g.outputs hv') (g.tests hv') distinct hρ
  exact ⟨h2, hw, g.witness_size_le hv' k⟩

/-- **Uniform witness length.**  On a `Strict k` yes-instance (`k ≥ 2`),
`k + 1 ≤ ρ ≤ s ≤ M` with `M = k_sources + |nodes|`, so the witness alphabet `s^(k+1)`
has binary length at most `M · size M`, independently of `k`. -/
theorem witness_size_uniform (hv : g.Valid) (k : ℕ) (hk : 2 ≤ k) (h : g.Strict k) :
    k + 1 ≤ cutSize (g.outputs hv) (g.tests hv) ∧
    cutSize (g.outputs hv) (g.tests hv) ≤ (tupleSupport (g.outputs hv) (g.tests hv)).card ∧
    (tupleSupport (g.outputs hv) (g.tests hv)).card ≤ g.base.k + g.base.nodes.length ∧
    ((tupleSupport (g.outputs hv) (g.tests hv)).card ^ (k + 1)).size ≤
      (g.base.k + g.base.nodes.length) * (g.base.k + g.base.nodes.length).size := by
  obtain ⟨hv', hs⟩ := h
  obtain ⟨_, hρ⟩ := (strict_degree_iff' k hk (g.base.xv (g.baseValid hv'))
    (g.base.yv (g.baseValid hv')) (g.base.xv_ne_yv _) (g.outputs hv') (g.tests hv')
    (g.var_x_mem_outputs hv') (g.var_y_mem_outputs hv') (g.guard_mem_tests hv')).mp hs
  have hρs := cutSize_le_support_card (g.outputs hv) (g.tests hv)
  have hsM := g.tupleSupport_card_le hv
  refine ⟨hρ, hρs, hsM, ?_⟩
  calc ((tupleSupport (g.outputs hv) (g.tests hv)).card ^ (k + 1)).size
      ≤ (k + 1) * (tupleSupport (g.outputs hv) (g.tests hv)).card.size := size_pow_le _ k
    _ ≤ (g.base.k + g.base.nodes.length) * (g.base.k + g.base.nodes.length).size :=
        Nat.mul_le_mul (by omega) (Nat.size_le_size hsM)

end GInstance
end DisequalityDispersion.Encoded
