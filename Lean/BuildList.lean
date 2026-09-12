import Mathlib

/-! # Index-driven list construction

`buildList n step` builds a list of length `n` whose `j`-th entry is
`step` applied to the list of the previous entries and `j`.  This is the
common shape of the executable evaluator, the canonical-identifier pass and
the occurrence-flag pass over a topologically ordered DAG. -/

namespace DisequalityDispersion
namespace Encoded

variable {α : Type}

def buildList (step : List α → ℕ → α) (n : ℕ) : List α :=
  (List.range n).foldl (fun acc j => acc ++ [step acc j]) []

theorem buildList_zero (step : List α → ℕ → α) : buildList step 0 = [] := rfl

theorem buildList_succ (step : List α → ℕ → α) (n : ℕ) :
    buildList step (n + 1) = buildList step n ++ [step (buildList step n) n] := by
  unfold buildList
  rw [List.range_succ, List.foldl_append]
  rfl

theorem buildList_length (step : List α → ℕ → α) (n : ℕ) :
    (buildList step n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [buildList_succ, List.length_append, ih]; rfl

theorem buildList_prefix (step : List α → ℕ → α) (n j : ℕ) (hj : j ≤ n) :
    buildList step j = (buildList step n).take j := by
  induction n with
  | zero =>
      have : j = 0 := by omega
      subst this; rfl
  | succ n ih =>
      rcases Nat.lt_or_ge j (n + 1) with h | h
      · rw [buildList_succ, List.take_append_of_le_length (by rw [buildList_length]; omega)]
        exact ih (by omega)
      · have : j = n + 1 := by omega
        subst this
        rw [List.take_of_length_le (by rw [buildList_length])]

theorem buildList_getD (step : List α → ℕ → α) (n j : ℕ) (hj : j < n) (d : α) :
    (buildList step n).getD j d = step (buildList step j) j := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [buildList_succ]
      rcases Nat.lt_or_ge j n with h | h
      · rw [List.getD_append _ _ _ _ (by rw [buildList_length]; exact h)]
        exact ih h
      · have hjn : j = n := by omega
        subst hjn
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [buildList_length])]
        simp [buildList_length]

theorem buildList_getElem (step : List α → ℕ → α) (n j : ℕ) (hj : j < n)
    (hj' : j < (buildList step n).length) :
    (buildList step n)[j] = step (buildList step j) j := by
  rw [← List.getD_eq_getElem _ (step (buildList step j) j) hj']
  exact buildList_getD step n j hj _

end Encoded
end DisequalityDispersion
