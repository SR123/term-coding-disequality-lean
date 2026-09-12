import GeneralRouting

/-! # The all-degree existential thresholds and the exact strict criterion (R3)

For a degree `k ≥ 2`, `LowerT k` and `StrictT k` are the existential
attainment predicates of `b_k(n) = n^k - n^(k-1)` and `b_k(n) + 1` by the
tuple maximum on `Fin n`, `n ≥ 2`.  `strict_degree_iff` proves, relative to
the named Menger input, that `StrictT k` holds iff no test has identical
sides and `k + 1 ≤ ρ`; the positive direction produces the explicit witness
`n = s^(k+1)` (`strict_witness`), the negative direction uses the sharp
retained-pair bound and the monotonicity of `b_j(n)` in `j`. -/

namespace DisequalityDispersion

variable {V F : Type} {arity : F → ℕ}

/-- `∃ n ≥ 2, b_k(n) ≤ D(n)`. -/
def LowerT [Fintype V] [Fintype F] (k : ℕ) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ n, 2 ≤ n ∧ threshold k n ≤ dispersionTuple (A := Fin n) outputs tests

/-- `∃ n ≥ 2, b_k(n) + 1 ≤ D(n)`. -/
def StrictT [Fintype V] [Fintype F] (k : ℕ) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ n, 2 ≤ n ∧ threshold k n + 1 ≤ dispersionTuple (A := Fin n) outputs tests

theorem lowerT_of_strictT [Fintype V] [Fintype F] (k : ℕ) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (h : StrictT k outputs tests) :
    LowerT k outputs tests := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨n, hn, le_trans (Nat.le_succ _) h⟩

/-- Power/division arithmetic of the witness: `(s^(k+1) / s)^ρ ≥ n^k ≥ b_k(n) + 1`. -/
theorem witness_arithmetic (s k ρ : ℕ) (hs : 2 ≤ s) (hρ : k + 1 ≤ ρ) (hk : 1 ≤ k) :
    threshold k (s ^ (k + 1)) + 1 ≤ (s ^ (k + 1) / s) ^ ρ := by
  have hs0 : 0 < s := by omega
  have hdiv : s ^ (k + 1) / s = s ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ hs0]
  rw [hdiv]
  have h1 : (s ^ k) ^ (k + 1) ≤ (s ^ k) ^ ρ :=
    Nat.pow_le_pow_right (Nat.one_le_pow _ _ hs0) hρ
  have h2 : (s ^ k) ^ (k + 1) = (s ^ (k + 1)) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have h3 : threshold k (s ^ (k + 1)) + 1 ≤ (s ^ (k + 1)) ^ k := by
    unfold threshold
    have hpos : 1 ≤ (s ^ (k + 1)) ^ (k - 1) := Nat.one_le_pow _ _ (Nat.pow_pos hs0)
    have hle : (s ^ (k + 1)) ^ (k - 1) ≤ (s ^ (k + 1)) ^ k :=
      Nat.pow_le_pow_right (Nat.pow_pos hs0) (by omega)
    omega
  calc threshold k (s ^ (k + 1)) + 1 ≤ (s ^ (k + 1)) ^ k := h3
    _ = (s ^ k) ^ (k + 1) := h2.symm
    _ ≤ (s ^ k) ^ ρ := h1

/-- **Explicit witness**: at `n = s^(k+1)`, the strict threshold is attained. -/
theorem strict_witness [Fintype V] [Fintype F] (k : ℕ) (hk : 1 ≤ k) (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hM : MengerInput outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2)
    (hρ : k + 1 ≤ cutSize outputs tests) :
    2 ≤ (tupleSupport outputs tests).card ^ (k + 1) ∧
      threshold k ((tupleSupport outputs tests).card ^ (k + 1)) + 1 ≤
        dispersionTuple (A := Fin ((tupleSupport outputs tests).card ^ (k + 1))) outputs tests := by
  set s := (tupleSupport outputs tests).card with hs
  have hs2 : 2 ≤ s := two_le_tupleSupport_card x y hxy outputs tests
  have hsn : s ≤ s ^ (k + 1) := Nat.le_self_pow (by omega) s
  refine ⟨le_trans hs2 hsn, ?_⟩
  exact (witness_arithmetic s k _ hs2 hρ hk).trans
    (routing_lower_bound_of_menger outputs tests hM distinct x (s ^ (k + 1)) hsn)

/-- **Exact strict criterion at every degree** (`thm:main`, strict part), relative
to the named Menger input: `StrictT k` iff no test has identical sides and
`k + 1 ≤ ρ`. -/
theorem strict_degree_iff [Fintype V] [Fintype F] (k : ℕ) (hk : 2 ≤ k) (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) (hguard : (.var x, .var y) ∈ tests)
    (hM : MengerInput outputs tests) :
    StrictT k outputs tests ↔ (∀ uv ∈ tests, uv.1 ≠ uv.2) ∧ k + 1 ≤ cutSize outputs tests := by
  constructor
  · rintro ⟨n, hn, hD⟩
    constructor
    · intro uv huv he
      have hu : (uv.1, uv.1) ∈ tests := by
        have hp : uv = (uv.1, uv.1) := Prod.ext rfl he.symm
        rw [← hp]
        exact huv
      have hz := identical_test_dispersionTuple_zero (A := Fin n) outputs uv.1 tests hu
      omega
    · by_contra hlt
      push_neg at hlt
      have hρ2 := two_le_cutSize outputs tests x y hxy hx hy
      have h1 := dispersionTuple_le_threshold x y hxy outputs tests hx hy hguard n
      have h2 := threshold_mono (cutSize outputs tests) k n (by omega) (by omega) (by omega)
      omega
  · rintro ⟨distinct, hρ⟩
    obtain ⟨h2, hw⟩ := strict_witness k (by omega) x y hxy outputs tests hM distinct hρ
    exact ⟨_, h2, hw⟩

/-- The non-strict side never exceeds `b_ρ`: if `ρ ≤ k` then `b_k` bounds `D(n)`
for every `n ≥ 1`, and `LowerT k` fails when `ρ < k`. -/
theorem dispersionTuple_le_threshold_of_cut_le [Fintype V] [Fintype F] (k : ℕ) (x y : V)
    (hxy : x ≠ y) (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) (hguard : (.var x, .var y) ∈ tests)
    (hρ : cutSize outputs tests ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    dispersionTuple (A := Fin n) outputs tests ≤ threshold k n := by
  have hρ2 := two_le_cutSize outputs tests x y hxy hx hy
  exact (dispersionTuple_le_threshold x y hxy outputs tests hx hy hguard n).trans
    (threshold_mono _ k n (by omega) hρ hn)

theorem not_lowerT_of_cut_lt [Fintype V] [Fintype F] (k : ℕ) (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) (hguard : (.var x, .var y) ∈ tests)
    (hρ : cutSize outputs tests < k) : ¬ LowerT k outputs tests := by
  rintro ⟨n, hn, hD⟩
  have hρ2 := two_le_cutSize outputs tests x y hxy hx hy
  have h1 := dispersionTuple_le_threshold x y hxy outputs tests hx hy hguard n
  -- b_ρ(n) + 1 ≤ b_k(n) for ρ < k and n ≥ 2
  have h2 : threshold (cutSize outputs tests) n + 1 ≤ threshold k n := by
    have := threshold_mono (cutSize outputs tests + 1) k n (by omega) hρ (by omega)
    refine le_trans ?_ this
    rw [threshold_eq _ n (by omega), threshold_eq _ n (by omega)]
    simp only [Nat.add_sub_cancel]
    have hp : n ^ (cutSize outputs tests - 1) * (n - 1) + 1 ≤
        n ^ (cutSize outputs tests) * (n - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, cutSize outputs tests = j + 1 := ⟨cutSize outputs tests - 1, by omega⟩
      rw [hj, Nat.add_sub_cancel, pow_succ]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hm : m + 2 - 1 = m + 1 := by omega
      rw [hm]
      have hpos : 1 ≤ (m + 2) ^ j := Nat.one_le_pow _ _ (by omega)
      have h3 : 1 ≤ (m + 2) ^ j * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    exact hp
  omega

/-- Threshold interleaving: `b_k(n) < b_k(n) + 1 < b_(k+1)(n)` for `n ≥ 2`, `k ≥ 2`. -/
theorem threshold_interleave (k n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n) :
    threshold k n < threshold k n + 1 ∧ threshold k n + 1 < threshold (k + 1) n := by
  refine ⟨Nat.lt_succ_self _, ?_⟩
  rw [threshold_eq k n (by omega), threshold_eq (k + 1) n (by omega), Nat.add_sub_cancel]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hk1 : j + 2 - 1 = j + 1 := by omega
  rw [hk1, pow_succ (n) (j + 1)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m + 2 - 1 = m + 1 := by omega
  rw [hm]
  have hpos : 2 ≤ (m + 2) ^ (j + 1) := by
    calc 2 ≤ m + 2 := by omega
      _ = (m + 2) ^ 1 := (pow_one _).symm
      _ ≤ (m + 2) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  set P := (m + 2) ^ (j + 1) with hP
  have h1 : P * (m + 2) * (m + 1) = P * (m + 1) + P * (m + 1) * (m + 1) := by ring
  rw [h1]
  have h2 : 2 ≤ P * (m + 1) * (m + 1) := by
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ P * (m + 1) * (m + 1) := Nat.mul_le_mul (Nat.mul_le_mul hpos (by omega)) (by omega)
  omega

end DisequalityDispersion
