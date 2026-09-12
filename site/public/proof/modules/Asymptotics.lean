import Transport
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Growth consequences for C3 (T7, C3 portion)

For the three-output class: the trivial upper bound `D(n) ≤ n³`; under the
strict criterion, the real lower bound `n³ / (8 s³) ≤ D(n)` for `n ≥ 2s`, the
explicit implication `n ≥ 64 s⁶ → n^(5/2) ≤ D(n)`, and the equivalence of
the existential strict predicate with the eventual strict threshold and with
eventual `n^(5/2)` growth.  Here `s = (instanceSupport t tests).card` is the
number of distinct subterms of the outputs and tests together with all
declared sources, exactly as in `cubic_lower_bound`. -/

namespace DisequalityDispersion

variable {V F : Type} {arity : F → ℕ} [Fintype V] [Fintype F]

/-- Trivial cubic upper bound: the image lives in `A × A × A`. -/
theorem dispersionOn_le_cube (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (n : ℕ) :
    dispersionOn (A := Fin n) x y t tests ≤ n ^ 3 := by
  apply SigEquiv.dispersionOn_le_of_forall
  intro I
  calc (filteredTriples x y t tests I).card ≤ Fintype.card (Fin n × Fin n × Fin n) :=
        Finset.card_le_univ _
    _ = n ^ 3 := by simp [Fintype.card_prod, Fintype.card_fin]; ring

/-- The syntactic strict criterion of `strict_threshold_iff`. -/
def StrictCriterion (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  (∀ uv ∈ tests, uv.1 ≠ uv.2) ∧ ∃ z, t.Uses z ∧ z ≠ x ∧ z ≠ y

/-- Natural-number cubic lower bound `(n / s)^3 ≤ D(n)` for `n ≥ s`. -/
theorem cubic_lower_of_criterion (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hc : StrictCriterion x y t tests)
    (n : ℕ) (hn : (instanceSupport t tests).card ≤ n) :
    (n / (instanceSupport t tests).card) ^ 3 ≤ dispersionOn (A := Fin n) x y t tests := by
  obtain ⟨hdist, z, hz, hzx, hzy⟩ := hc
  exact cubic_lower_bound x y z hxy (Ne.symm hzx) (Ne.symm hzy) t hz tests hdist n hn

omit [Fintype F] in
theorem support_pos (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) :
    0 < (instanceSupport t tests).card :=
  lt_of_lt_of_le (by norm_num) (instanceSupport_card_two x y hxy t tests)

/-- `n / (2s) ≤ ⌊n / s⌋` for `n ≥ 2s`, in the reals. -/
theorem half_le_div_cast (n s : ℕ) (hs : 0 < s) (hn : 2 * s ≤ n) :
    (n : ℝ) / (2 * s) ≤ ((n / s : ℕ) : ℝ) := by
  have hq : 2 ≤ n / s := by
    rw [Nat.le_div_iff_mul_le hs]
    linarith
  have hmod := Nat.mod_lt n hs
  have hdiv := Nat.div_add_mod n s
  have h1 : n ≤ 2 * (n / s) * s := by
    have : n % s < s := hmod
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have : (n : ℝ) ≤ 2 * ((n / s : ℕ) : ℝ) * s := by exact_mod_cast h1
  linarith

/-- Real cubic lower bound for `n ≥ 2s`. -/
theorem real_cubic_lower (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hc : StrictCriterion x y t tests)
    (n : ℕ) (hn : 2 * (instanceSupport t tests).card ≤ n) :
    (n : ℝ) ^ 3 / (8 * ((instanceSupport t tests).card : ℝ) ^ 3) ≤
      (dispersionOn (A := Fin n) x y t tests : ℝ) := by
  set s := (instanceSupport t tests).card with hs
  have hs0 : 0 < s := support_pos x y hxy t tests
  have hnat := cubic_lower_of_criterion x y hxy t tests hc n (by omega)
  have hcast : (((n / s : ℕ) : ℝ)) ^ 3 ≤ (dispersionOn (A := Fin n) x y t tests : ℝ) := by
    exact_mod_cast hnat
  have hhalf := half_le_div_cast n s hs0 hn
  have hpos : (0 : ℝ) ≤ (n : ℝ) / (2 * s) := by positivity
  have h3 : ((n : ℝ) / (2 * s)) ^ 3 ≤ (((n / s : ℕ) : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hpos hhalf 3
  have heq : ((n : ℝ) / (2 * s)) ^ 3 = (n : ℝ) ^ 3 / (8 * (s : ℝ) ^ 3) := by
    field_simp
    ring
  rw [← heq]
  exact h3.trans hcast

/-- `n ≥ 64 s⁶` gives `n^(5/2) ≤ n³ / (8 s³)`. -/
theorem five_halves_le_cubic (n s : ℕ) (hs : 0 < s) (hn : 64 * s ^ 6 ≤ n) :
    (n : ℝ) ^ (5 / 2 : ℝ) ≤ (n : ℝ) ^ 3 / (8 * (s : ℝ) ^ 3) := by
  have hn0 : (0 : ℝ) < n := by
    have : 64 ≤ n := le_trans (by nlinarith [Nat.one_le_pow 6 s hs]) hn
    exact_mod_cast (by omega : 0 < n)
  have hsqrt : 8 * (s : ℝ) ^ 3 ≤ Real.sqrt n := by
    have h1 : (8 * (s : ℝ) ^ 3) ^ 2 ≤ (n : ℝ) := by
      have : (64 * s ^ 6 : ℕ) ≤ n := hn
      have h' : ((64 * s ^ 6 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
      push_cast at h'
      nlinarith
    calc 8 * (s : ℝ) ^ 3 = Real.sqrt ((8 * (s : ℝ) ^ 3) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1
  have h52 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ 2 * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]
    norm_num
  rw [h52]
  have hs3 : (0 : ℝ) < 8 * (s : ℝ) ^ 3 := by positivity
  rw [le_div_iff₀ hs3]
  have : (n : ℝ) ^ 2 * Real.sqrt n * (8 * (s : ℝ) ^ 3) ≤ (n : ℝ) ^ 2 * Real.sqrt n * Real.sqrt n := by
    apply mul_le_mul_of_nonneg_left hsqrt
    positivity
  refine this.trans (le_of_eq ?_)
  rw [mul_assoc, Real.mul_self_sqrt hn0.le]
  ring

/-- Explicit non-sharp implication: `n ≥ 64 s⁶ → D(n) ≥ n^(5/2)`. -/
theorem five_halves_lower (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hc : StrictCriterion x y t tests)
    (n : ℕ) (hn : 64 * (instanceSupport t tests).card ^ 6 ≤ n) :
    (n : ℝ) ^ (5 / 2 : ℝ) ≤ (dispersionOn (A := Fin n) x y t tests : ℝ) := by
  have hs0 := support_pos x y hxy t tests
  have h2s : 2 * (instanceSupport t tests).card ≤ n := by
    have := Nat.one_le_pow 6 (instanceSupport t tests).card hs0
    have h6 : (instanceSupport t tests).card ≤ (instanceSupport t tests).card ^ 6 :=
      Nat.le_self_pow (by norm_num) _
    omega
  exact (five_halves_le_cubic n _ hs0 hn).trans (real_cubic_lower x y hxy t tests hc n h2s)

/-- Two-sided cubic growth (`Θ(n³)`) under the strict criterion, for `n ≥ 2s`. -/
theorem theta_cubic (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hc : StrictCriterion x y t tests)
    (n : ℕ) (hn : 2 * (instanceSupport t tests).card ≤ n) :
    (n : ℝ) ^ 3 / (8 * ((instanceSupport t tests).card : ℝ) ^ 3) ≤
        (dispersionOn (A := Fin n) x y t tests : ℝ) ∧
      (dispersionOn (A := Fin n) x y t tests : ℝ) ≤ (n : ℝ) ^ 3 :=
  ⟨real_cubic_lower x y hxy t tests hc n hn, by exact_mod_cast dispersionOn_le_cube x y t tests n⟩

theorem mul_pred_add_one_le_sq (n : ℕ) (hn : 1 ≤ n) : n * (n - 1) + 1 ≤ n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith

/-- The existential strict predicate. -/
def StrictExists (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ n, 2 ≤ n ∧ n * (n - 1) + 1 ≤ dispersionOn (A := Fin n) x y t tests

/-- The eventual strict threshold. -/
def EventualStrict (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ N, ∀ n, N ≤ n → n * (n - 1) + 1 ≤ dispersionOn (A := Fin n) x y t tests

/-- Eventual `n^(5/2)` growth. -/
def EventualFiveHalves (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) ^ (5 / 2 : ℝ) ≤ (dispersionOn (A := Fin n) x y t tests : ℝ)

theorem strictExists_iff_criterion (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hguard : (.var x, .var y) ∈ tests) :
    StrictExists x y t tests ↔ StrictCriterion x y t tests :=
  strict_threshold_iff x y hxy t tests hguard

theorem eventualStrict_of_criterion (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hc : StrictCriterion x y t tests) :
    EventualStrict x y t tests := by
  set s := (instanceSupport t tests).card with hs
  have hs0 : 0 < s := support_pos x y hxy t tests
  refine ⟨8 * s ^ 3, fun n hn => ?_⟩
  have h2s : 2 * s ≤ n := by
    have : s ≤ s ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hreal := real_cubic_lower x y hxy t tests hc n h2s
  have hn2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 / (8 * (s : ℝ) ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    have : (8 * s ^ 3 : ℕ) ≤ n := hn
    have h' : ((8 * s ^ 3 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at h'
    nlinarith [sq_nonneg (n : ℝ)]
  have hD : (n : ℝ) ^ 2 ≤ (dispersionOn (A := Fin n) x y t tests : ℝ) := hn2.trans hreal
  have hDn : n ^ 2 ≤ dispersionOn (A := Fin n) x y t tests := by exact_mod_cast hD
  have hn1 : 1 ≤ n := by
    have := Nat.one_le_pow 3 s hs0
    omega
  have := mul_pred_add_one_le_sq n hn1
  omega

theorem eventualFiveHalves_of_criterion (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hc : StrictCriterion x y t tests) :
    EventualFiveHalves x y t tests :=
  ⟨64 * (instanceSupport t tests).card ^ 6, fun n hn => five_halves_lower x y hxy t tests hc n hn⟩

theorem strictExists_of_eventualStrict (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (h : EventualStrict x y t tests) :
    StrictExists x y t tests := by
  obtain ⟨N, hN⟩ := h
  exact ⟨max N 2, le_max_right _ _, hN _ (le_max_left _ _)⟩

theorem strictExists_of_eventualFiveHalves (x y : V) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (h : EventualFiveHalves x y t tests) :
    StrictExists x y t tests := by
  obtain ⟨N, hN⟩ := h
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  set n := max N 2 with hn
  have hn2 : 2 ≤ n := le_max_right _ _
  have h1 := hN n (le_max_left _ _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hD : (n : ℝ) ^ 2 ≤ (dispersionOn (A := Fin n) x y t tests : ℝ) := h2.trans h1
  have hDn : n ^ 2 ≤ dispersionOn (A := Fin n) x y t tests := by exact_mod_cast hD
  have := mul_pred_add_one_le_sq n (by omega)
  omega

/-- **C3 equivalences**: the existential strict predicate, the eventual strict
threshold and eventual `n^(5/2)` growth coincide. -/
theorem c3_equivalences (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hguard : (.var x, .var y) ∈ tests) :
    (StrictExists x y t tests ↔ EventualStrict x y t tests) ∧
      (StrictExists x y t tests ↔ EventualFiveHalves x y t tests) := by
  constructor
  · constructor
    · intro h
      exact eventualStrict_of_criterion x y hxy t tests
        ((strictExists_iff_criterion x y hxy t tests hguard).mp h)
    · exact strictExists_of_eventualStrict x y t tests
  · constructor
    · intro h
      exact eventualFiveHalves_of_criterion x y hxy t tests
        ((strictExists_iff_criterion x y hxy t tests hguard).mp h)
    · exact strictExists_of_eventualFiveHalves x y t tests

end DisequalityDispersion
