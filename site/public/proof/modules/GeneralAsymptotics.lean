import TermMenger
import DegreeCompiler
import Density
import Asymptotics

/-! # General-degree consequences: density, sandwich, log-limit, eventual thresholds (R7)

* `paddedRatio_eq`: the density ratio of the degree-`k` compiled instance equals the
  two-source ratio exactly (product identity), hence `paddedRatio_tendsto`.
* `cut_sandwich`: `(n/s)^ρ ≤ D(n) ≤ n^ρ` (`thm:cut`), unconditional.
* `log_ratio_tendsto`: `log D(n) / log n → ρ` (`thm:cut`, growth exponent).
* `eventual_strict_iff` / `strictT_iff_eventual`: the strict threshold at degree `k`
  is reached for one alphabet iff for all large alphabets iff `k + 1 ≤ ρ`
  (`cor:eventual`); `eventual_power_lower`: `n^(k+1/2) ≤ D(n)` for all large `n`
  when `k + 1 ≤ ρ`. -/

open Filter Topology

namespace DisequalityDispersion

/-! ### Padded density -/

section density
variable (k d : ℕ) (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))

/-- The degree-`k` density ratio `D_padded(n) / b_k(n)`. -/
noncomputable def paddedRatio (n : ℕ) : ℝ :=
  ((Encoded.compileDegree k d rels w).dispersion (Encoded.compileDegree_valid k d rels w) n : ℝ) /
    (threshold k n : ℝ)

/-- **Exact ratio identity**: the padded ratio is the two-source ratio, for every `n ≥ 2`. -/
theorem paddedRatio_eq (hk : 2 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    paddedRatio k d rels w n = compiledRatio rels w n := by
  unfold paddedRatio compiledRatio compiledMax
  rw [Encoded.compileDegree_dispersion k d rels w hk, ← guard_count_eq_threshold k n hk]
  have hpos : (0 : ℝ) < (n : ℝ) ^ (k - 2) := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
  rw [mul_div_mul_right _ _ (ne_of_gt hpos)]

/-- Padded density: `D_padded(n) / b_k(n) → 1` for a nonempty target word. -/
theorem paddedRatio_tendsto (hk : 2 ≤ k) (hL : 0 < w.length) :
    Tendsto (fun n : ℕ => paddedRatio k d rels w n) atTop (𝓝 1) := by
  refine (compiledRatio_tendsto rels w hL).congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨2, fun n hn => (paddedRatio_eq k d rels w hk n hn).symm⟩

end density

/-! ### The sandwich `(n/s)^ρ ≤ D(n) ≤ n^ρ` -/

variable {V F : Type} {arity : F → ℕ}

/-- Standing hypotheses of class `C`: retained distinct sources among the outputs
and the guard among the tests. -/
structure InClassC (x y : V) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Prop where
  hxy : x ≠ y
  hx : Term.var x ∈ outputs
  hy : Term.var y ∈ outputs
  hguard : (.var x, .var y) ∈ tests

theorem threshold_le_pow (k n : ℕ) : threshold k n ≤ n ^ k := Nat.sub_le _ _

/-- `thm:cut`, upper half: `D(n) ≤ b_ρ(n) ≤ n^ρ`. -/
theorem dispersionTuple_le_pow [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (n : ℕ) :
    dispersionTuple (A := Fin n) outputs tests ≤ n ^ cutSize outputs tests :=
  (dispersionTuple_le_threshold x y hC.hxy outputs tests hC.hx hC.hy hC.hguard n).trans
    (threshold_le_pow _ _)

/-- `thm:cut`: `(n/s)^ρ ≤ D(n) ≤ n^ρ` for `n ≥ s`, with `s` the support size. -/
theorem cut_sandwich [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (n : ℕ)
    (hn : (tupleSupport outputs tests).card ≤ n) :
    (n / (tupleSupport outputs tests).card) ^ cutSize outputs tests ≤
        dispersionTuple (A := Fin n) outputs tests ∧
      dispersionTuple (A := Fin n) outputs tests ≤ n ^ cutSize outputs tests :=
  ⟨routing_lower_bound outputs tests distinct x n hn, dispersionTuple_le_pow hC n⟩

/-- Real lower bound `(n / (2s))^ρ ≤ D(n)` for `n ≥ 2s`. -/
theorem real_cut_lower [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (n : ℕ)
    (hn : 2 * (tupleSupport outputs tests).card ≤ n) :
    ((n : ℝ) / (2 * (tupleSupport outputs tests).card)) ^ cutSize outputs tests ≤
      (dispersionTuple (A := Fin n) outputs tests : ℝ) := by
  set s := (tupleSupport outputs tests).card with hs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (two_le_tupleSupport_card x y hC.hxy outputs tests)
  have h1 := half_le_div_cast n s hs0 hn
  have h2 : ((n / s) ^ cutSize outputs tests : ℕ) ≤ dispersionTuple (A := Fin n) outputs tests :=
    routing_lower_bound outputs tests distinct x n (by omega)
  calc ((n : ℝ) / (2 * s)) ^ cutSize outputs tests
      ≤ (((n / s : ℕ) : ℝ)) ^ cutSize outputs tests :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ = (((n / s) ^ cutSize outputs tests : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ _ := by exact_mod_cast h2

/-! ### The growth exponent -/

/-- `log D(n) / log n → ρ` (`thm:cut`, exponent form). -/
theorem log_ratio_tendsto [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) :
    Tendsto (fun n : ℕ => Real.log (dispersionTuple (A := Fin n) outputs tests) / Real.log n)
      atTop (𝓝 (cutSize outputs tests)) := by
  set s := (tupleSupport outputs tests).card with hs
  set ρ := cutSize outputs tests with hρ
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (two_le_tupleSupport_card x y hC.hxy outputs tests)
  have hs0' : (0 : ℝ) < 2 * s := by positivity
  -- lower envelope: ρ - ρ log(2s) / log n
  have hlow : Tendsto (fun n : ℕ => (ρ : ℝ) - ρ * Real.log (2 * s) / Real.log n) atTop (𝓝 ρ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have h' : Tendsto (fun n : ℕ => (ρ : ℝ) * Real.log (2 * s) * (Real.log n)⁻¹) atTop (𝓝 0) := by
      simpa using h.const_mul ((ρ : ℝ) * Real.log (2 * s))
    have := (tendsto_const_nhds (x := (ρ : ℝ))).sub h'
    simp only [sub_zero] at this
    refine this.congr (fun n => ?_)
    rw [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨2 * s + 2, fun n hn => ?_⟩
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hD := real_cut_lower hC distinct n (by omega)
    have hDpos : (0 : ℝ) < ((n : ℝ) / (2 * s)) ^ ρ := by
      apply pow_pos; positivity
    have hlogD : ρ * (Real.log n - Real.log (2 * s)) ≤
        Real.log (dispersionTuple (A := Fin n) outputs tests) := by
      have := Real.log_le_log hDpos hD
      rw [Real.log_pow, Real.log_div (by positivity) (ne_of_gt hs0')] at this
      exact this
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hlogn]
    linarith
  · rw [Filter.eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    rw [div_le_iff₀ hlogn]
    have hD := dispersionTuple_le_pow hC n
    rcases Nat.eq_zero_or_pos (dispersionTuple (A := Fin n) outputs tests) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      positivity
    · have := Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hD : (dispersionTuple (A := Fin n) outputs tests : ℝ) ≤ (n : ℝ) ^ ρ)
      rwa [Real.log_pow] at this

/-! ### Eventual thresholds (`cor:eventual`) -/

/-- The strict threshold at degree `k` holds for all large alphabets. -/
def EventualStrictT [Fintype V] [Fintype F] (k : ℕ) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ N, ∀ n, N ≤ n → threshold k n + 1 ≤ dispersionTuple (A := Fin n) outputs tests

/-- `(n/(2s))^(k+1) ≥ n^k` for `n ≥ (2s)^(k+1)` (naturals: `⌊n/s⌋^(k+1) ≥ n^k`). -/
theorem floor_pow_ge (n s k : ℕ) (hs : 0 < s) (hn : (2 * s) ^ (k + 1) ≤ n) :
    n ^ k ≤ (n / s) ^ (k + 1) := by
  have h2s : 2 * s ≤ n := by
    calc 2 * s ≤ (2 * s) ^ (k + 1) := Nat.le_self_pow (by omega) _
      _ ≤ n := hn
  have hq : n ≤ 2 * (n / s) * s := by
    have hmod := Nat.mod_lt n hs
    have hdiv := Nat.div_add_mod n s
    have hq2 : 2 ≤ n / s := by rw [Nat.le_div_iff_mul_le hs]; linarith
    nlinarith
  -- (2 (n/s) s)^(k+1) ≥ n^(k+1) and (2s)^(k+1) ≤ n give (n/s)^(k+1) ≥ n^k
  have h1 : n ^ (k + 1) ≤ (n / s) ^ (k + 1) * (2 * s) ^ (k + 1) := by
    rw [← mul_pow]
    apply Nat.pow_le_pow_left
    linarith
  have h2 : (n / s) ^ (k + 1) * (2 * s) ^ (k + 1) ≤ (n / s) ^ (k + 1) * n :=
    Nat.mul_le_mul_left _ hn
  have h3 : n ^ (k + 1) = n ^ k * n := pow_succ n k
  have hn0 : 0 < n := by omega
  have : n ^ k * n ≤ (n / s) ^ (k + 1) * n := by rw [← h3]; exact h1.trans h2
  exact Nat.le_of_mul_le_mul_right this hn0

/-- If `k + 1 ≤ ρ`, the strict threshold holds for every `n ≥ (2s)^(k+1)`. -/
theorem eventual_strict_of_cut [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (k : ℕ) (hk : 1 ≤ k)
    (hρ : k + 1 ≤ cutSize outputs tests) (n : ℕ)
    (hn : (2 * (tupleSupport outputs tests).card) ^ (k + 1) ≤ n) :
    threshold k n + 1 ≤ dispersionTuple (A := Fin n) outputs tests := by
  set s := (tupleSupport outputs tests).card with hs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (two_le_tupleSupport_card x y hC.hxy outputs tests)
  have h2s : 2 * s ≤ n := by
    calc 2 * s ≤ (2 * s) ^ (k + 1) := Nat.le_self_pow (by omega) _
      _ ≤ n := hn
  have hlow := routing_lower_bound outputs tests distinct x n (by omega)
  rw [← hs] at hlow
  have hq : 1 ≤ n / s := by rw [Nat.le_div_iff_mul_le hs0]; omega
  have hmono : (n / s) ^ (k + 1) ≤ (n / s) ^ cutSize outputs tests :=
    Nat.pow_le_pow_right hq hρ
  have hfloor := floor_pow_ge n s k hs0 hn
  -- b_k(n) + 1 ≤ n^k
  have hthr : threshold k n + 1 ≤ n ^ k := by
    rw [threshold_eq k n hk]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    have hn2 : 2 ≤ n := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have : m + 2 - 1 = m + 1 := by omega
    rw [this]
    have hp : 1 ≤ (m + 2) ^ j := Nat.one_le_pow _ _ (by omega)
    nlinarith
  omega

/-- **`cor:eventual` at every degree**: strict for one alphabet iff strict for all
large alphabets iff no identical-side test and `k + 1 ≤ ρ`. -/
theorem strictT_iff_eventual [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (k : ℕ) (hk : 2 ≤ k) :
    (StrictT k outputs tests ↔ EventualStrictT k outputs tests) ∧
      (StrictT k outputs tests ↔
        (∀ uv ∈ tests, uv.1 ≠ uv.2) ∧ k + 1 ≤ cutSize outputs tests) := by
  have hiff := strict_degree_iff' k hk x y hC.hxy outputs tests hC.hx hC.hy hC.hguard
  refine ⟨⟨fun h => ?_, fun ⟨N, hN⟩ => ?_⟩, hiff⟩
  · obtain ⟨distinct, hρ⟩ := hiff.mp h
    exact ⟨(2 * (tupleSupport outputs tests).card) ^ (k + 1),
      fun n hn => eventual_strict_of_cut hC distinct k (by omega) hρ n hn⟩
  · exact ⟨max N 2, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- `n^(k + 1/2) ≤ D(n)` for all `n ≥ (2s)^(2k+2)` when `k + 1 ≤ ρ`. -/
theorem eventual_power_lower [Fintype V] [Fintype F] {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (k : ℕ)
    (hρ : k + 1 ≤ cutSize outputs tests) (n : ℕ)
    (hn : (2 * (tupleSupport outputs tests).card) ^ (2 * k + 2) ≤ n) :
    (n : ℝ) ^ ((k : ℝ) + 1 / 2) ≤ (dispersionTuple (A := Fin n) outputs tests : ℝ) := by
  set s := (tupleSupport outputs tests).card with hs
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) (two_le_tupleSupport_card x y hC.hxy outputs tests)
  have h2s : 2 * s ≤ n := by
    calc 2 * s ≤ (2 * s) ^ (2 * k + 2) := Nat.le_self_pow (by omega) _
      _ ≤ n := hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow := real_cut_lower hC distinct n h2s
  have hbase : (1 : ℝ) ≤ (n : ℝ) / (2 * s) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast h2s
  have hmono : ((n : ℝ) / (2 * s)) ^ (k + 1) ≤ ((n : ℝ) / (2 * s)) ^ cutSize outputs tests :=
    pow_le_pow_right₀ hbase hρ
  -- n^(k+1/2) ≤ (n/(2s))^(k+1) ⟺ (2s)^(k+1) ≤ n^(1/2)
  have hsqrt : (2 * (s : ℝ)) ^ (k + 1) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) (by positivity), ← pow_mul]
    have : ((2 * s) ^ ((k + 1) * 2) : ℕ) ≤ n := by
      rw [show (k + 1) * 2 = 2 * k + 2 by ring]; exact hn
    exact_mod_cast this
  have hkey : (n : ℝ) ^ ((k : ℝ) + 1 / 2) ≤ ((n : ℝ) / (2 * s)) ^ (k + 1) := by
    have hsplit : (n : ℝ) ^ ((k : ℝ) + 1 / 2) = (n : ℝ) ^ (k + 1) / Real.sqrt n := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hn0]
      congr 1
      push_cast
      ring
    rw [hsplit, div_pow, div_le_div_iff₀ (Real.sqrt_pos.mpr hn0) (by positivity)]
    have := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (k + 1))
    linarith
  exact hkey.trans (hmono.trans hlow)

/-! ### The unrestricted tuple bound `D(n) ≤ n^ρ` (`thm:cut` without the retained pair) -/

open Classical in
theorem filteredImage_card_le_pow_cut [Fintype V] [Fintype A] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (K : Finset (Term V F arity))
    (hK : IsCut K outputs) (I : Interpretation F arity A) :
    (filteredImage outputs tests I).card ≤ Fintype.card A ^ K.card := by
  -- every output tuple is determined by the values at the cut
  let key : (V → A) → ({u // u ∈ K} → A) := fun a u => u.1.eval I a
  let g : ({u // u ∈ K} → A) → List A := fun kk =>
    if h : ∃ a ∈ validAssignments tests I, key a = kk then tupleEval outputs I (Classical.choose h)
    else []
  have hsurj : Set.SurjOn g ((validAssignments tests I).image key) (filteredImage outputs tests I) := by
    intro o ho
    simp only [filteredImage, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ho
    obtain ⟨a, ha, rfl⟩ := ho
    refine ⟨key a, by simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨a, ha, rfl⟩, ?_⟩
    have h : ∃ a' ∈ validAssignments tests I, key a' = key a := ⟨a, ha, rfl⟩
    simp only [g, dif_pos h]
    apply tupleEval_eq_of_agree_on_cut I _ _ K outputs hK
    intro u hu
    exact congrFun (Classical.choose_spec h).2 ⟨u, hu⟩
  calc (filteredImage outputs tests I).card
      ≤ ((validAssignments tests I).image key).card := Finset.card_le_card_of_surjOn g hsurj
    _ ≤ (Finset.univ : Finset ({u // u ∈ K} → A)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card A ^ K.card := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe]

/-- `D(n) ≤ n^ρ` for arbitrary output tuples. -/
theorem dispersionTuple_le_pow_cutSize [Fintype V] [Fintype F] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (n : ℕ) :
    dispersionTuple (A := Fin n) outputs tests ≤ n ^ cutSize outputs tests := by
  obtain ⟨K, _, hK, hc⟩ := exists_min_cut outputs tests
  rw [← hc]
  apply dispersionTuple_le_of_forall
  intro I
  simpa using filteredImage_card_le_pow_cut outputs tests K hK I

/-- `thm:cut` for arbitrary tuples: `(n/s)^ρ ≤ D(n) ≤ n^ρ` for `n ≥ s`. -/
theorem cut_sandwich' [Fintype V] [Fintype F] [Nonempty V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (n : ℕ)
    (hn : (tupleSupport outputs tests).card ≤ n) :
    (n / (tupleSupport outputs tests).card) ^ cutSize outputs tests ≤
        dispersionTuple (A := Fin n) outputs tests ∧
      dispersionTuple (A := Fin n) outputs tests ≤ n ^ cutSize outputs tests :=
  ⟨routing_lower_bound outputs tests distinct (Classical.arbitrary V) n hn,
    dispersionTuple_le_pow_cutSize outputs tests n⟩

theorem tupleSupport_card_pos [Fintype V] [Nonempty V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : 0 < (tupleSupport outputs tests).card :=
  Finset.card_pos.mpr ⟨_, source_mem_tupleSupport outputs tests (Classical.arbitrary V)⟩


/-- Real lower bound `(n / (2s))^ρ ≤ D(n)` for arbitrary tuples (`n ≥ 2s`). -/
theorem real_cut_lower' [Fintype V] [Fintype F] [Nonempty V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (n : ℕ)
    (hn : 2 * (tupleSupport outputs tests).card ≤ n) :
    ((n : ℝ) / (2 * (tupleSupport outputs tests).card)) ^ cutSize outputs tests ≤
      (dispersionTuple (A := Fin n) outputs tests : ℝ) := by
  set s := (tupleSupport outputs tests).card with hs
  have hs0 : 0 < s := tupleSupport_card_pos outputs tests
  have h1 := half_le_div_cast n s hs0 hn
  have h2 : ((n / s) ^ cutSize outputs tests : ℕ) ≤ dispersionTuple (A := Fin n) outputs tests :=
    routing_lower_bound outputs tests distinct (Classical.arbitrary V) n (by omega)
  calc ((n : ℝ) / (2 * s)) ^ cutSize outputs tests
      ≤ (((n / s : ℕ) : ℝ)) ^ cutSize outputs tests := pow_le_pow_left₀ (by positivity) h1 _
    _ = (((n / s) ^ cutSize outputs tests : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ _ := by exact_mod_cast h2

/-- `log D(n) / log n → ρ` for arbitrary tuples (with `ρ = 0` allowed). -/
theorem log_ratio_tendsto' [Fintype V] [Fintype F] [Nonempty V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) :
    Tendsto (fun n : ℕ => Real.log (dispersionTuple (A := Fin n) outputs tests) / Real.log n)
      atTop (𝓝 (cutSize outputs tests)) := by
  set s := (tupleSupport outputs tests).card with hs
  set ρ := cutSize outputs tests with hρ
  have hs0 : 0 < s := tupleSupport_card_pos outputs tests
  have hs0' : (0 : ℝ) < 2 * s := by positivity
  have hlow : Tendsto (fun n : ℕ => (ρ : ℝ) - ρ * Real.log (2 * s) / Real.log n) atTop (𝓝 ρ) := by
    have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have h' : Tendsto (fun n : ℕ => (ρ : ℝ) * Real.log (2 * s) * (Real.log n)⁻¹) atTop (𝓝 0) := by
      simpa using h.const_mul ((ρ : ℝ) * Real.log (2 * s))
    have := (tendsto_const_nhds (x := (ρ : ℝ))).sub h'
    simp only [sub_zero] at this
    refine this.congr (fun n => ?_)
    rw [div_eq_mul_inv]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨2 * s + 2, fun n hn => ?_⟩
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have h1 := half_le_div_cast n s hs0 (by omega)
    have h2 : ((n / s) ^ ρ : ℕ) ≤ dispersionTuple (A := Fin n) outputs tests :=
      routing_lower_bound outputs tests distinct (Classical.arbitrary V) n (by omega)
    have hD : ((n : ℝ) / (2 * s)) ^ ρ ≤ (dispersionTuple (A := Fin n) outputs tests : ℝ) := by
      calc ((n : ℝ) / (2 * s)) ^ ρ ≤ (((n / s : ℕ) : ℝ)) ^ ρ := pow_le_pow_left₀ (by positivity) h1 _
        _ = (((n / s) ^ ρ : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ _ := by exact_mod_cast h2
    have hDpos : (0 : ℝ) < ((n : ℝ) / (2 * s)) ^ ρ := by apply pow_pos; positivity
    have hlogD : ρ * (Real.log n - Real.log (2 * s)) ≤
        Real.log (dispersionTuple (A := Fin n) outputs tests) := by
      have := Real.log_le_log hDpos hD
      rw [Real.log_pow, Real.log_div (by positivity) (ne_of_gt hs0')] at this
      exact this
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hlogn]
    linarith
  · rw [Filter.eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    rw [div_le_iff₀ hlogn]
    have hD := dispersionTuple_le_pow_cutSize outputs tests n
    rcases Nat.eq_zero_or_pos (dispersionTuple (A := Fin n) outputs tests) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      positivity
    · have := Real.log_le_log (by exact_mod_cast hpos)
        (by exact_mod_cast hD : (dispersionTuple (A := Fin n) outputs tests : ℝ) ≤ (n : ℝ) ^ ρ)
      rwa [Real.log_pow] at this

/-! ### `cor:eventual` for an arbitrary function `h` with `n^d < h(n) = o(n^(d+1))` -/

/-- **`cor:eventual`, general form.**  For arbitrary tuples with pairwise distinct test sides
and any `h` with `n^d < h(n)` eventually and `h(n) = o(n^(d+1))`: `D(n) ≥ h(n)` for all large
`n` iff `d + 1 ≤ ρ`. -/
theorem eventual_h_iff [Fintype V] [Fintype F] [Nonempty V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2)
    (d : ℕ) (h : ℕ → ℝ) (hlow : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d < h n)
    (hsmall : Tendsto (fun n : ℕ => h n / (n : ℝ) ^ (d + 1)) atTop (𝓝 0)) :
    (∀ᶠ n : ℕ in atTop, h n ≤ (dispersionTuple (A := Fin n) outputs tests : ℝ)) ↔
      d + 1 ≤ cutSize outputs tests := by
  set s := (tupleSupport outputs tests).card with hs
  set ρ := cutSize outputs tests with hρ
  have hs0 : 0 < s := tupleSupport_card_pos outputs tests
  constructor
  · intro hev
    by_contra hlt
    push_neg at hlt
    -- `D(n) ≤ n^ρ ≤ n^d < h(n)` for large `n`
    have hup : ∀ᶠ n : ℕ in atTop,
        (dispersionTuple (A := Fin n) outputs tests : ℝ) ≤ (n : ℝ) ^ d := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      have h1 := dispersionTuple_le_pow_cutSize outputs tests n
      have h2 : n ^ ρ ≤ n ^ d := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast h1.trans h2
    have := (hev.and hlow).and hup
    rw [Filter.eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    have := hN N le_rfl
    linarith [this.1.1, this.1.2, this.2]
  · intro hρd
    -- `h(n) ≤ n^(d+1) / (2s)^(d+1) ≤ (n/(2s))^ρ ≤ D(n)` for large `n`
    have hc : (0 : ℝ) < 1 / (2 * s : ℝ) ^ (d + 1) := by positivity
    have hev := (hsmall.eventually (gt_mem_nhds hc))
    have hlarge : ∀ᶠ n : ℕ in atTop, 2 * s ≤ n := Filter.eventually_ge_atTop _
    refine ((hev.and hlarge).and hlow).mono ?_
    rintro n ⟨⟨hn1, hn2⟩, hn3⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpow : (0 : ℝ) < (n : ℝ) ^ (d + 1) := by positivity
    have h1 : h n ≤ (n : ℝ) ^ (d + 1) / (2 * s : ℝ) ^ (d + 1) := by
      have := (div_lt_iff₀ hpow).mp hn1
      rw [div_eq_mul_one_div]
      linarith
    have h2 : (n : ℝ) ^ (d + 1) / (2 * s : ℝ) ^ (d + 1) = ((n : ℝ) / (2 * s)) ^ (d + 1) := by
      rw [div_pow]
    have hbase : (1 : ℝ) ≤ (n : ℝ) / (2 * s) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast hn2
    have h3 : ((n : ℝ) / (2 * s)) ^ (d + 1) ≤ ((n : ℝ) / (2 * s)) ^ ρ :=
      pow_le_pow_right₀ hbase hρd
    have h4 := real_cut_lower' outputs tests distinct n hn2
    calc h n ≤ (n : ℝ) ^ (d + 1) / (2 * s : ℝ) ^ (d + 1) := h1
      _ = ((n : ℝ) / (2 * s)) ^ (d + 1) := h2
      _ ≤ ((n : ℝ) / (2 * s)) ^ ρ := h3
      _ ≤ _ := h4

end DisequalityDispersion
