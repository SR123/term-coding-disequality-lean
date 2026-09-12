import Transport

/-! # The toy formula (Example 4.3): tests `x ≠ y`, `F(x) ≠ y`, `F(x) ≠ x`

With sources `x = false`, `y = true`, one unary symbol `F` and the repeated
output `(x, y, x)`, the actual maximum image size is `n (n - 2)` for every
`n ≥ 2`: each row `x` with `F x ≠ x` contributes `n - 2` values of `y`,
fixed rows contribute nothing, and a fixed-point-free cyclic shift attains
the bound. -/

namespace DisequalityDispersion

/-- The unary signature with one symbol. -/
abbrev ToyTerm := Term Bool Unit (fun _ => 1)

def toyTests : List (ToyTerm × ToyTerm) :=
  [(.var false, .var true), (.app () (fun _ => .var false), .var true),
    (.app () (fun _ => .var false), .var false)]

/-- The unary map carried by an interpretation of the toy signature. -/
def toyMap {A : Type} (I : Interpretation Unit (fun _ => 1) A) : A → A :=
  fun p => I () (fun _ => p)

theorem toy_valid_iff {A : Type} (I : Interpretation Unit (fun _ => 1) A) (a : Bool → A) :
    Valid toyTests I a ↔ Admissible (fun _ : Unit => toyMap I) (toyMap I) (a false) (a true) := by
  simp [Valid, toyTests, Admissible, Term.eval, toyMap]

theorem toy_image_eq {A : Type} [Fintype A] [DecidableEq A]
    (I : Interpretation Unit (fun _ => 1) A) :
    filteredTriples false true (.var false) toyTests I =
      (codePairs (fun _ : Unit => toyMap I) (toyMap I)).image (fun pq => (pq.1, pq.2, pq.1)) := by
  classical
  ext o
  simp only [filteredTriples, validAssignments, codePairs, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a false, a true), (toy_valid_iff I a).mp ha, rfl⟩
  · rintro ⟨pq, hpq, rfl⟩
    refine ⟨fun b => if b then pq.2 else pq.1, ?_, rfl⟩
    rw [toy_valid_iff]
    simpa using hpq

theorem toy_image_card {A : Type} [Fintype A] [DecidableEq A]
    (I : Interpretation Unit (fun _ => 1) A) :
    (filteredTriples false true (.var false) toyTests I).card =
      (codePairs (fun _ : Unit => toyMap I) (toyMap I)).card := by
  rw [toy_image_eq]
  exact card_append_determined _ Prod.fst

/-- Exact row count for one unary law equal to the target map. -/
theorem codePairs_unary_card {A : Type} [Fintype A] [DecidableEq A] (F : A → A) :
    (codePairs (fun _ : Unit => F) F).card =
      (Finset.univ.filter (fun x => F x ≠ x)).card * (Fintype.card A - 2) := by
  classical
  rw [code_card_rows]
  have hrow : ∀ x : A, (if F x = x then 0 else Fintype.card A - (forbiddenRow (fun _ : Unit => F) x).card) =
      if F x = x then 0 else Fintype.card A - 2 := by
    intro x
    by_cases hx : F x = x
    · simp [hx]
    · rw [if_neg hx, if_neg hx]
      have : (forbiddenRow (fun _ : Unit => F) x).card = 2 := by
        unfold forbiddenRow
        have himg : (Finset.univ.image (fun _ : Unit => F x)) = {F x} := by
          ext y; simp
        rw [himg, Finset.card_insert_of_notMem (by simpa using Ne.symm hx)]
        simp
      rw [this]
  simp only [hrow]
  rw [Finset.sum_ite]
  simp [Finset.sum_const, smul_eq_mul]

theorem toy_image_card_le {A : Type} [Fintype A] [DecidableEq A]
    (I : Interpretation Unit (fun _ => 1) A) :
    (filteredTriples false true (.var false) toyTests I).card ≤
      Fintype.card A * (Fintype.card A - 2) := by
  rw [toy_image_card, codePairs_unary_card]
  apply Nat.mul_le_mul_right
  exact Finset.card_filter_le _ _ |>.trans (by simp)

/-- The cyclic shift on `Fin n`. -/
def cyclicShift (n : ℕ) (hn : 0 < n) : Fin n → Fin n :=
  fun p => ⟨(p.1 + 1) % n, Nat.mod_lt _ hn⟩

theorem cyclicShift_ne (n : ℕ) (hn : 2 ≤ n) (p : Fin n) :
    cyclicShift n (by omega) p ≠ p := by
  intro h
  have h' : (p.1 + 1) % n = p.1 := congrArg Fin.val h
  rcases Nat.lt_or_ge (p.1 + 1) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h'
    omega
  · have : p.1 + 1 = n := by have := p.2; omega
    rw [this, Nat.mod_self] at h'
    omega

/-- **Toy formula**: the maximum is exactly `n (n - 2)` for every `n ≥ 2`. -/
theorem toy_dispersion (n : ℕ) (hn : 2 ≤ n) :
    dispersionOn (A := Fin n) false true (.var false) toyTests = n * (n - 2) := by
  classical
  apply le_antisymm
  · apply SigEquiv.dispersionOn_le_of_forall
    intro I
    simpa [Fintype.card_fin] using toy_image_card_le I
  · let I : Interpretation Unit (fun _ => 1) (Fin n) := fun _ args => cyclicShift n (by omega) (args 0)
    have hI : toyMap I = cyclicShift n (by omega) := by
      funext p; rfl
    refine le_trans ?_ (image_le_dispersion false true (.var false) toyTests I)
    rw [toy_image_card, codePairs_unary_card, hI]
    have hall : (Finset.univ.filter (fun x : Fin n => cyclicShift n (by omega) x ≠ x)) =
        Finset.univ := by
      ext x
      simp [cyclicShift_ne n hn x]
    rw [hall, Finset.card_univ, Fintype.card_fin]

end DisequalityDispersion
