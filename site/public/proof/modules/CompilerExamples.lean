import EncodedCompiler

/-! # Checks for the encoded compiler (T3 acceptance items)

* the empty target word is a negative `Lower` instance (its target test is
  the identity `x ≠ x`);
* a target word consisting of a formal inverse pair is a negative instance
  (it is trivial in the presented group), while its raw syntax is retained
  as two chain nodes;
* the test count and node count are as stated. -/

namespace DisequalityDispersion.Encoded

/-- The empty word gives an identity target test, hence dispersion `0`. -/
theorem compileWord_nil_dispersion (d : ℕ) (rels : List (List (Letter (Fin d))))
    (hv : (compileWord d rels []).Valid) (n : ℕ) :
    (compileWord d rels []).dispersion hv n = 0 := by
  rw [compileWord_dispersion]
  apply identical_test_zero _ _ _ (.var false)
  simp [compilerTests, wordTerm]

theorem not_Lower_compileWord_nil (d : ℕ) (rels : List (List (Letter (Fin d)))) :
    ¬ (compileWord d rels []).Lower := by
  rintro ⟨hv, n, hn, h⟩
  rw [compileWord_nil_dispersion] at h
  have : 2 * 1 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  omega

/-- A formal inverse pair is trivial in every presented group. -/
theorem presentedWord_inverse_pair (d : ℕ) (rels : List (List (Letter (Fin d)))) (i : Fin d) :
    presentedWord rels [(i, true), (i, false)] = 1 := by
  rw [presentedWord_eq]
  simp [groupWord, groupLetter]

theorem not_Lower_compileWord_inverse_pair (d : ℕ) (rels : List (List (Letter (Fin d))))
    (i : Fin d) : ¬ (compileWord d rels [(i, true), (i, false)]).Lower := by
  rw [Lower_compileWord_iff_quotient]
  rintro ⟨Q, _, _, φ, _, hne⟩
  apply hne
  rw [presentedWord_inverse_pair, map_one]

/-- Raw syntax is retained: the inverse pair contributes two chain nodes. -/
example : (compileWord 1 [] [(0, true), (0, false)]).nodes.length = 8 := by decide
example : (compileWord 1 [] [(0, true), (0, false)]).tests.length = 4 := by decide
example : (compileWord 1 [] [(0, true), (0, false)]).nodes =
    [.src 0, .src 1, .app 0 [0], .app 1 [2], .app 1 [0], .app 0 [4], .app 0 [0], .app 1 [6]] := by
  decide
example : (compileWord 1 [] [(0, true), (0, false)]).tests = [(0, 1), (3, 1), (5, 1), (7, 0)] := by
  decide
example : (compileWord 1 [] []).tests = [(0, 1), (3, 1), (5, 1), (0, 0)] := by decide
example : (compileWord 1 [] []).isValid = true := by decide
example : (compileWord 2 [[(0, true), (1, true)]] [(1, false)]).isValid = true := by decide
example : (compileWord 2 [[(0, true), (1, true)]] [(1, false)]).tests.length = 2 * 2 + 1 + 2 := by
  decide

/-- Every compiled instance fails the strict test (it has `t = x`). -/
theorem compileWord_strictDecide (d : ℕ) (rels : List (List (Letter (Fin d))))
    (w : List (Letter (Fin d))) : (compileWord d rels w).strictDecide = false := by
  have h : ¬ (compileWord d rels w).Strict := by
    rintro ⟨hv, n, hn, hD⟩
    rw [compileWord_dispersion] at hD
    have := (strict_threshold_iff false true (by decide) (.var false) (compilerTests d rels w)
      (compiler_has_guard d rels w)).mp ⟨n, hn, hD⟩
    obtain ⟨_, z, hz, hzx, _⟩ := this
    simp only [Term.Uses] at hz
    exact hzx hz.symm
  rcases hb : (compileWord d rels w).strictDecide with _ | _
  · rfl
  · exact absurd ((compileWord d rels w).strictDecide_iff.mp hb) h

end DisequalityDispersion.Encoded
