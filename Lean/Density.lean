import Transport
import CompilerBridge
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Compiled density, exact defects and the limit (T5)

For the actual compiled maximum
`compiledMax rels w n = dispersionOn (A := Fin n) false true (var false) (compilerTests d rels w)`
with `M = 2d + rels.length` laws and a target word of syntactic length `L = w.length`:

* `n * (n - (M+1)) ≤ compiledMax n ≤ n * (n - 1)` for `0 < L < n` (all-shift tables);
* the integer form `n(n-1) - M n ≤ compiledMax n`;
* `compiledMax n / (n (n-1)) → 1`;
* `0 ≤ n² - compiledMax n ≤ (M+1) n` eventually;
* the exact all-shift defect `|C| = n (n - 1 - |R_n|)` with `|R_n| ≤ M`;
* an explicit computable alphabet size for any positive rational density defect. -/

namespace DisequalityDispersion

open Filter Topology

section family
variable {d : ℕ} {A : Type} (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))

/-- Concrete index type of the `M = 2d + rels.length` laws. -/
abbrev LawIndex (d : ℕ) (rels : List (List (Letter (Fin d)))) : Type :=
  (Fin d ⊕ Fin d) ⊕ Fin rels.length

theorem card_lawIndex : Fintype.card (LawIndex d rels) = 2 * d + rels.length := by
  simp [LawIndex, Fintype.card_sum, Fintype.card_fin]
  ring

/-- The law maps of the compiled instance: the two inverse composites per
generator and each relator word. -/
def lawFamily (p m : Fin d → A → A) : LawIndex d rels → A → A
  | .inl (.inl i) => fun x => p i (m i x)
  | .inl (.inr i) => fun x => m i (p i x)
  | .inr j => evalWord (signedTables p m) rels[j]

/-- The compiled pair set is the code pair set of this law family and the target map. -/
theorem compiledPairs_eq_codePairs [Fintype A] [DecidableEq A] (p m : Fin d → A → A) :
    compiledPairs rels w p m =
      codePairs (lawFamily rels p m) (evalWord (signedTables p m) w) := by
  ext xy
  simp only [compiledPairs, codePairs, Admissible, Finset.mem_filter, Finset.mem_univ, true_and,
    Sum.forall, lawFamily]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, ⟨⟨h2, h3⟩, ?_⟩, h5⟩
    intro j
    exact h4 _ (List.getElem_mem j.2)
  · rintro ⟨h1, ⟨⟨h2, h3⟩, h4⟩, h5⟩
    refine ⟨h1, h2, h3, ?_, h5⟩
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    exact h4 ⟨j, hj⟩

end family

section shift
variable {d : ℕ} (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))

/-- The all-shift table on `ZMod n`. -/
def shiftTable (n : ℕ) : Fin d → ZMod n → ZMod n := fun _ x => x + 1

theorem signedTables_shift (n : ℕ) :
    signedTables (shiftTable (d := d) n) (shiftTable n) = fun _ x => x + 1 := by
  funext l x
  simp [signedTables, shiftTable]

/-- Syntactic law lengths. -/
def lawLen : LawIndex d rels → ℕ
  | .inl _ => 2
  | .inr j => rels[j].length

theorem lawFamily_shift (n : ℕ) (i : LawIndex d rels) (x : ZMod n) :
    lawFamily rels (shiftTable n) (shiftTable n) i x = x + (lawLen rels i : ZMod n) := by
  rcases i with (i | i) | j
  · simp [lawFamily, shiftTable, lawLen, add_assoc, one_add_one_eq_two]
  · simp [lawFamily, shiftTable, lawLen, add_assoc, one_add_one_eq_two]
  · simp only [lawFamily, lawLen, signedTables_shift]
    exact evalWord_shift n _ x

/-- The compiled maximum on `Fin n`. -/
noncomputable def compiledMax (n : ℕ) : ℕ :=
  dispersionOn (A := Fin n) false true (.var false) (compilerTests d rels w)

theorem compiledMax_eq_hard (n : ℕ) :
    (2 ≤ n ∧ n * (n - 1) ≤ compiledMax rels w n) ↔
      (2 ≤ n ∧ n * (n - 1) ≤ dispersionOn (A := Fin n) false true (.var false)
        (compilerTests d rels w)) := Iff.rfl

/-- Upper bound: the output is the retained source `x`. -/
theorem compiledMax_le (n : ℕ) : compiledMax rels w n ≤ n * (n - 1) := by
  unfold compiledMax
  have := retained_term_dispersion_le (A := Fin n) false true (.var false) (compilerTests d rels w)
    (compiler_has_guard d rels w) (by
      intro z hz
      simp only [Term.Uses] at hz
      exact Or.inl hz.symm)
  simpa [Fintype.card_fin] using this

/-- All-shift lower bound on `ZMod n` for `0 < L < n`. -/
theorem compiledPairs_shift_card (n : ℕ) [NeZero n] (hL : 0 < w.length) (hLn : w.length < n) :
    n * (n - (2 * d + rels.length + 1)) ≤
      (compiledPairs rels w (shiftTable n) (shiftTable n)).card := by
  classical
  rw [compiledPairs_eq_codePairs]
  have hw : ∀ x : ZMod n, evalWord (signedTables (shiftTable n) (shiftTable n)) w x ≠ x := by
    rw [signedTables_shift]
    exact shift_word_fixedPointFree n w hL hLn
  have := code_card_lower (lawFamily rels (shiftTable n) (shiftTable n)) _ hw
  rwa [ZMod.card, card_lawIndex] at this

/-- Transfer of the compiled image from `ZMod n` to `Fin n`. -/
theorem dispersion_zmod_le_fin (n : ℕ) [NeZero n] :
    dispersionOn (A := ZMod n) false true (.var false) (compilerTests d rels w) ≤
      compiledMax rels w n := by
  unfold compiledMax
  haveI : Nonempty (ZMod n) := ⟨0⟩
  exact dispersion_embedding_le (ZMod.finEquiv n).symm.toEquiv.toEmbedding _ _ _ _

/-- Natural-number lower bound on the compiled maximum. -/
theorem compiledMax_lower (n : ℕ) (hL : 0 < w.length) (hLn : w.length < n) :
    n * (n - (2 * d + rels.length + 1)) ≤ compiledMax rels w n := by
  haveI : NeZero n := ⟨by omega⟩
  classical
  refine (compiledPairs_shift_card rels w n hL hLn).trans ?_
  refine le_trans ?_ (dispersion_zmod_le_fin rels w n)
  rw [← compiledTriple_card, ← compiler_image_eq]
  exact image_le_dispersion _ _ _ _ _

/-- The two-sided natural bound. -/
theorem compiledMax_bounds (n : ℕ) (hL : 0 < w.length) (hLn : w.length < n) :
    n * (n - (2 * d + rels.length + 1)) ≤ compiledMax rels w n ∧
      compiledMax rels w n ≤ n * (n - 1) :=
  ⟨compiledMax_lower rels w n hL hLn, compiledMax_le rels w n⟩

/-- Integer form: `n(n-1) - M n ≤ D(n) ≤ n(n-1)`. -/
theorem compiledMax_int_bounds (n : ℕ) (hL : 0 < w.length) (hLn : w.length < n) :
    (n : ℤ) * (n - 1) - (2 * d + rels.length) * n ≤ (compiledMax rels w n : ℤ) ∧
      (compiledMax rels w n : ℤ) ≤ (n : ℤ) * (n - 1) := by
  obtain ⟨h1, h2⟩ := compiledMax_bounds rels w n hL hLn
  constructor
  · rcases Nat.lt_or_ge n (2 * d + rels.length + 1) with h | h
    · have : (n : ℤ) * (n - 1) - (2 * d + rels.length) * n ≤ 0 := by
        have hn : (n : ℤ) ≤ 2 * d + rels.length := by exact_mod_cast (by omega : n ≤ 2 * d + rels.length)
        nlinarith
      exact this.trans (by positivity)
    · have h1' : ((n * (n - (2 * d + rels.length + 1)) : ℕ) : ℤ) ≤ (compiledMax rels w n : ℤ) := by
        exact_mod_cast h1
      push_cast [Nat.cast_sub h] at h1'
      linarith
  · have h2' : ((compiledMax rels w n : ℕ) : ℤ) ≤ ((n * (n - 1) : ℕ) : ℤ) := by exact_mod_cast h2
    have hn : 1 ≤ n := by omega
    push_cast [Nat.cast_sub hn] at h2'
    exact h2'

/-- `D(n) = n² - O(n)` with the uniform coefficient `M + 1`, for `n > L`. -/
theorem compiledMax_defect (n : ℕ) (hL : 0 < w.length) (hLn : w.length < n) :
    (0 : ℤ) ≤ (n : ℤ) ^ 2 - compiledMax rels w n ∧
      (n : ℤ) ^ 2 - compiledMax rels w n ≤ (2 * d + rels.length + 1) * n := by
  obtain ⟨h1, h2⟩ := compiledMax_int_bounds rels w n hL hLn
  constructor
  · nlinarith
  · nlinarith

/-! ### The real ratio and its limit -/

/-- The density ratio `D(n) / (n (n - 1))`. -/
noncomputable def compiledRatio (n : ℕ) : ℝ :=
  (compiledMax rels w n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))

theorem compiledRatio_bounds (n : ℕ) (hL : 0 < w.length) (hLn : w.length < n) (hn2 : 2 ≤ n) :
    1 - (2 * d + rels.length : ℝ) / ((n : ℝ) - 1) ≤ compiledRatio rels w n ∧
      compiledRatio rels w n ≤ 1 := by
  obtain ⟨h1, h2⟩ := compiledMax_int_bounds rels w n hL hLn
  have h1r : (n : ℝ) * ((n : ℝ) - 1) - (2 * d + rels.length : ℝ) * n ≤ (compiledMax rels w n : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    exact this
  have h2r : (compiledMax rels w n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have := (Int.cast_le (R := ℝ)).mpr h2
    push_cast at this
    exact this
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    apply mul_pos <;> linarith
  unfold compiledRatio
  constructor
  · rw [le_div_iff₀ hpos]
    have hn1' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have : (1 - (2 * d + rels.length : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * ((n : ℝ) - 1)) =
        (n : ℝ) * ((n : ℝ) - 1) - (2 * d + rels.length : ℝ) * n := by
      field_simp
    rw [this]
    exact h1r
  · rw [div_le_one hpos]
    exact h2r

/-- `D(n) / (n (n-1)) → 1` for a nonempty target word. -/
theorem compiledRatio_tendsto (hL : 0 < w.length) :
    Tendsto (fun n : ℕ => compiledRatio rels w n) atTop (𝓝 1) := by
  set M : ℝ := (2 * d + rels.length : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hlow : Tendsto (fun n : ℕ => 1 - (2 * M) / (n : ℝ)) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)).sub (tendsto_const_div_atTop_nhds_zero_nat (2 * M))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · rw [Filter.eventually_atTop]
    refine ⟨w.length + 2, fun n hn => ?_⟩
    have hb := (compiledRatio_bounds rels w n hL (by omega) (by omega)).1
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have : (2 * M) / (n : ℝ) ≥ M / ((n : ℝ) - 1) := by
      rw [ge_iff_le, div_le_div_iff₀ hn1 (by linarith)]
      nlinarith
    linarith
  · rw [Filter.eventually_atTop]
    exact ⟨w.length + 2, fun n hn => (compiledRatio_bounds rels w n hL (by omega) (by omega)).2⟩

/-! ### Exact defect for the all-shift tables -/

/-- The distinct nonzero residues of the law lengths modulo `n`. -/
def residues (n : ℕ) : Finset (ZMod n) :=
  (Finset.univ.image (fun i : LawIndex d rels => (lawLen rels i : ZMod n))).erase 0

theorem residues_card_le (n : ℕ) : (residues rels n).card ≤ 2 * d + rels.length := by
  unfold residues
  refine (Finset.card_erase_le).trans ?_
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, card_lawIndex]

theorem forbiddenRow_shift_card (n : ℕ) [NeZero n] (x : ZMod n) :
    (forbiddenRow (lawFamily rels (shiftTable n) (shiftTable n)) x).card =
      1 + (residues rels n).card := by
  classical
  unfold forbiddenRow
  have himg : Finset.univ.image (fun i => lawFamily rels (shiftTable n) (shiftTable n) i x) =
      (Finset.univ.image (fun i : LawIndex d rels => (lawLen rels i : ZMod n))).image
        (fun r => x + r) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i _
    simp [Function.comp, lawFamily_shift]
  rw [himg]
  set S := Finset.univ.image (fun i : LawIndex d rels => (lawLen rels i : ZMod n)) with hS
  have hins : insert x (S.image (fun r => x + r)) = (insert 0 S).image (fun r => x + r) := by
    rw [Finset.image_insert, add_zero]
  rw [hins, Finset.card_image_of_injective _ (add_right_injective x)]
  have h0 : insert (0 : ZMod n) S = insert 0 (S.erase 0) := by
    ext y
    simp only [Finset.mem_insert, Finset.mem_erase]
    tauto
  rw [h0, Finset.card_insert_of_notMem (Finset.notMem_erase 0 S)]
  unfold residues
  rw [← hS]
  omega

/-- The exact all-shift count `|C| = n (n - 1 - |R_n|)`. -/
theorem compiledPairs_shift_card_exact (n : ℕ) [NeZero n] (hL : 0 < w.length)
    (hLn : w.length < n) :
    (compiledPairs rels w (shiftTable n) (shiftTable n)).card =
      n * (n - 1 - (residues rels n).card) := by
  classical
  rw [compiledPairs_eq_codePairs, code_card_rows]
  have hw : ∀ x : ZMod n, evalWord (signedTables (shiftTable n) (shiftTable n)) w x ≠ x := by
    rw [signedTables_shift]
    exact shift_word_fixedPointFree n w hL hLn
  have key : ∀ x : ZMod n, (if evalWord (signedTables (shiftTable n) (shiftTable n)) w x = x then 0
      else n - (forbiddenRow (lawFamily rels (shiftTable n) (shiftTable n)) x).card) =
      n - 1 - (residues rels n).card := by
    intro x
    rw [if_neg (hw x), forbiddenRow_shift_card]
    omega
  simp only [ZMod.card]
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  simp [ZMod.card]

/-! ### A computable alphabet size for a prescribed density defect -/

/-- An alphabet size strictly larger than `max L (1 + M / ε)`. -/
def epsAlphabet (L M : ℕ) (ε : ℚ) : ℕ := max L ⌈1 + (M : ℚ) / ε⌉₊ + 1

theorem epsAlphabet_gt (L M : ℕ) (ε : ℚ) :
    L < epsAlphabet L M ε ∧ (1 + (M : ℚ) / ε) < epsAlphabet L M ε := by
  unfold epsAlphabet
  constructor
  · omega
  · have h1 := Nat.le_ceil (1 + (M : ℚ) / ε)
    have h2 : (⌈1 + (M : ℚ) / ε⌉₊ : ℚ) ≤ max (L : ℚ) (⌈1 + (M : ℚ) / ε⌉₊ : ℚ) :=
      le_max_right _ _
    push_cast
    linarith

/-- Density guarantee: at `n = epsAlphabet L M ε` the ratio is at least `1 - ε`. -/
theorem density_guarantee (ε : ℚ) (hε : 0 < ε) (hL : 0 < w.length) :
    1 - (ε : ℝ) ≤ compiledRatio rels w (epsAlphabet w.length (2 * d + rels.length) ε) := by
  obtain ⟨hL', hε'⟩ := epsAlphabet_gt w.length (2 * d + rels.length) ε
  set n := epsAlphabet w.length (2 * d + rels.length) ε with hn
  have hn2 : 2 ≤ n := by
    have : (1 : ℚ) < n := by
      have : (0 : ℚ) ≤ (2 * d + rels.length : ℕ) / ε := by positivity
      linarith
    exact_mod_cast (by exact_mod_cast this : (1 : ℚ) < n) |>.trans_le' (le_refl _) |> fun h =>
      (by omega : 2 ≤ n)
  have hb := (compiledRatio_bounds rels w n hL hL' hn2).1
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hgt : (1 + ((2 * d + rels.length : ℕ) : ℝ) / (ε : ℝ)) < n := by
    have := (Rat.cast_lt (K := ℝ)).mpr hε'
    push_cast at this ⊢
    exact this
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith [hgt, div_nonneg (by positivity : (0:ℝ) ≤ ((2 * d + rels.length : ℕ) : ℝ)) hεr.le]
  have hM : ((2 * d + rels.length : ℕ) : ℝ) / ((n : ℝ) - 1) < ε := by
    rw [div_lt_iff₀ hn1]
    have : ((2 * d + rels.length : ℕ) : ℝ) / ε < (n : ℝ) - 1 := by linarith
    rw [div_lt_iff₀ hεr] at this
    linarith
  push_cast at hb hM
  linarith

end shift

end DisequalityDispersion
