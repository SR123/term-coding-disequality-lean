import DegreeThreshold

/-! # Free-coordinate padding (R4, term level)

Adding `k - 2` fresh sources to a two-source instance and retaining them as
further output coordinates multiplies every filtered image by `n^(k-2)`:
the padded outputs are the identity tuple on `Fin k`, the tests are the old
tests with sources renamed along `Fin 2 → Fin k`, and

    D_padded(n) = n^(k-2) * D_pair(n)

for every alphabet (`padding_dispersion`).  The padded instance has all `k`
sources as outputs, so its cut size is exactly `k` (`cutSize_of_all_vars`). -/

namespace DisequalityDispersion

variable {V V' F A : Type} {arity : F → ℕ}

/-- Rename the sources of a term. -/
def Term.mapVar (g : V → V') : Term V F arity → Term V' F arity
  | .var v => .var (g v)
  | .app f ts => .app f (fun i => Term.mapVar g (ts i))

theorem Term.eval_mapVar (g : V → V') (I : Interpretation F arity A) (a : V' → A)
    (t : Term V F arity) : (t.mapVar g).eval I a = t.eval I (fun v => a (g v)) := by
  induction t with
  | var v => rfl
  | app f ts ih =>
      simp only [Term.mapVar, Term.eval]
      congr 1
      funext i
      exact ih i

/-- Rename the sources of a test list. -/
def mapVarTests (g : V → V') (tests : List (Term V F arity × Term V F arity)) :
    List (Term V' F arity × Term V' F arity) :=
  tests.map (fun uv => (uv.1.mapVar g, uv.2.mapVar g))

theorem Valid_mapVarTests (g : V → V') (tests : List (Term V F arity × Term V F arity))
    (I : Interpretation F arity A) (a : V' → A) :
    Valid (mapVarTests g tests) I a ↔ Valid tests I (fun v => a (g v)) := by
  unfold Valid mapVarTests
  simp only [List.forall_mem_map, Term.eval_mapVar]

theorem Term.mapVar_injective (g : V → V') (hg : Function.Injective g) :
    Function.Injective (Term.mapVar (F := F) (arity := arity) g) := by
  intro s t h
  induction s generalizing t with
  | var v =>
      cases t with
      | var w => simp only [Term.mapVar, Term.var.injEq] at h; rw [hg h]
      | app f ts => simp [Term.mapVar] at h
  | app f ts ih =>
      cases t with
      | var w => simp [Term.mapVar] at h
      | app f' ts' =>
          simp only [Term.mapVar, Term.app.injEq] at h
          obtain ⟨rfl, h2⟩ := h
          congr
          funext i
          exact ih i (congrFun (eq_of_heq h2) i)

theorem mapVarTests_distinct_iff (g : V → V') (hg : Function.Injective g)
    (tests : List (Term V F arity × Term V F arity)) :
    (∀ uv ∈ mapVarTests g tests, uv.1 ≠ uv.2) ↔ ∀ uv ∈ tests, uv.1 ≠ uv.2 := by
  unfold mapVarTests
  simp only [List.forall_mem_map]
  constructor
  · intro h uv huv he
    exact h uv huv (by rw [he])
  · intro h uv huv he
    exact h uv huv (Term.mapVar_injective g hg he)

/-! ### Padding by fresh sources -/

section padding
variable [Fintype F]

/-- The padding map `Fin 2 → Fin k`. -/
def padMap (k : ℕ) (hk : 2 ≤ k) : Fin 2 → Fin k := Fin.castLE hk

theorem padMap_injective (k : ℕ) (hk : 2 ≤ k) : Function.Injective (padMap k hk) :=
  Fin.castLE_injective hk

/-- The padded tests. -/
def padTests (k : ℕ) (hk : 2 ≤ k) (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity)) :
    List (Term (Fin k) F arity × Term (Fin k) F arity) :=
  mapVarTests (padMap k hk) tests

/-- The pair image of a two-source instance. -/
noncomputable def pairImage [Fintype A] (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity))
    (I : Interpretation F arity A) : Finset (A × A) := by
  classical
  exact (validAssignments tests I).image (fun a => (a 0, a 1))

open Classical in
omit [Fintype F] in
theorem pairImage_card [Fintype A] (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity))
    (I : Interpretation F arity A) :
    (filteredImage [.var 0, .var 1] tests I).card = (pairImage tests I).card :=
  filteredImage_pair_card 0 1 tests I

/-- An assignment on `Fin 2` is determined by its two values. -/
theorem fin2_ext (a b : Fin 2 → A) (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  funext i
  fin_cases i <;> assumption

omit [Fintype F] in
open Classical in
/-- The padded filtered image is the product of the pair image with all fresh tuples. -/
theorem padded_filteredImage [Fintype A] (k : ℕ) (hk : 2 ≤ k)
    (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity)) (I : Interpretation F arity A) :
    filteredImage (identityOutputs k) (padTests k hk tests) I =
      ((pairImage tests I) ×ˢ (Finset.univ : Finset (Fin (k - 2) → A))).image
        (fun c => List.ofFn (sharpAssign k hk c)) := by
  ext o
  simp only [filteredImage, Finset.mem_image, validAssignments, Finset.mem_filter, Finset.mem_univ,
    true_and, identityOutputs_tupleEval, Finset.mem_product, pairImage, padTests,
    Valid_mapVarTests]
  constructor
  · rintro ⟨a', ha', rfl⟩
    refine ⟨((a' (padMap k hk 0), a' (padMap k hk 1)), fun i => a' ⟨i.1 + 2, by omega⟩),
      ⟨⟨fun v => a' (padMap k hk v), ha', rfl⟩, trivial⟩, ?_⟩
    congr 1
    funext i
    simp only [sharpAssign]
    split_ifs with h0 h1
    · congr 1; ext; simp [padMap, h0]
    · congr 1; ext; simp [padMap, h1]
    · congr 1; ext; simp; omega
  · rintro ⟨c, ⟨⟨a, ha, hc⟩, _⟩, rfl⟩
    refine ⟨sharpAssign k hk c, ?_, rfl⟩
    have heq : (fun v => sharpAssign k hk c (padMap k hk v)) = a := by
      apply fin2_ext
      · simp [sharpAssign, padMap, ← hc]
      · simp [sharpAssign, padMap, ← hc]
    rw [heq]
    exact ha

omit [Fintype F] in
open Classical in
theorem padded_filteredImage_card [Fintype A] (k : ℕ) (hk : 2 ≤ k)
    (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity)) (I : Interpretation F arity A) :
    (filteredImage (identityOutputs k) (padTests k hk tests) I).card =
      (filteredImage [.var 0, .var 1] tests I).card * Fintype.card A ^ (k - 2) := by
  rw [padded_filteredImage, pairImage_card]
  rw [Finset.card_image_of_injective _ (fun c c' h =>
    sharpAssign_injective k hk (List.ofFn_injective h))]
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

theorem finset_sup_mul_const {ι : Type} (s : Finset ι) (c : ι → ℕ) (m : ℕ) :
    s.sup (fun i => c i * m) = s.sup c * m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
      rw [Finset.sup_insert, Finset.sup_insert, ih]
      exact Nat.mul_max_mul_right _ _ _

/-- **Padding identity**: `D_padded(n) = D_pair(n) * n^(k-2)`. -/
theorem padding_dispersion (k : ℕ) (hk : 2 ≤ k)
    (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity)) (n : ℕ) :
    dispersionTuple (A := Fin n) (identityOutputs k) (padTests k hk tests) =
      dispersionTuple (A := Fin n) [.var 0, .var 1] tests * n ^ (k - 2) := by
  classical
  unfold dispersionTuple
  rw [← finset_sup_mul_const]
  apply Finset.sup_congr rfl
  intro I _
  rw [padded_filteredImage_card, Fintype.card_fin]

/-! ### The cut size of an all-source output tuple -/

omit [Fintype F] in
open Classical in
/-- When every output is a source, the minimum cut is the set of output sources. -/
theorem cutSize_of_all_vars [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (hall : ∀ t ∈ outputs, ∃ v, t = Term.var v) :
    cutSize outputs tests = outputs.toFinset.card := by
  classical
  apply le_antisymm
  · have hcut : IsCut outputs.toFinset outputs := by
      intro t ht ha
      obtain ⟨v, rfl⟩ := hall t ht
      rw [avoids_var_iff] at ha
      exact ha (List.mem_toFinset.mpr ht)
    exact cutSize_le_card_of_isCut outputs tests _ hcut
  · obtain ⟨K, _, hK, hc⟩ := exists_min_cut outputs tests
    rw [← hc]
    apply Finset.card_le_card
    intro t ht
    have ht' := List.mem_toFinset.mp ht
    obtain ⟨v, rfl⟩ := hall t ht'
    exact source_output_mem_cut K outputs hK v ht'

omit [Fintype F] in
open Classical in
theorem identityOutputs_toFinset_card (k : ℕ) :
    (identityOutputs (F := F) (arity := arity) k).toFinset.card = k := by
  classical
  unfold identityOutputs
  rw [List.toFinset_card_of_nodup ((List.nodup_finRange k).map (fun a b h => Term.var.inj h))]
  simp

omit [Fintype F] in
open Classical in
/-- The padded instance has cut size exactly `k`. -/
theorem padded_cutSize (k : ℕ) (hk : 2 ≤ k)
    (tests : List (Term (Fin 2) F arity × Term (Fin 2) F arity)) :
    cutSize (identityOutputs (F := F) (arity := arity) k) (padTests k hk tests) = k := by
  rw [cutSize_of_all_vars, identityOutputs_toFinset_card]
  intro t ht
  simp only [identityOutputs, List.mem_map, List.mem_finRange, true_and] at ht
  obtain ⟨i, rfl⟩ := ht
  exact ⟨i, rfl⟩

end padding

/-! ### Pair outputs versus the retained triple -/

open Classical in
theorem filteredImage_pair_eq_triple_card [Fintype V] [Fintype A] (x y : V)
    (tests : List (Term V F arity × Term V F arity)) (I : Interpretation F arity A) :
    (filteredImage [.var x, .var y] tests I).card = (filteredTriples x y (.var x) tests I).card := by
  rw [filteredImage_pair_card]
  unfold filteredTriples
  have : (validAssignments tests I).image (fun a => (a x, a y, (Term.var x).eval I a)) =
      ((validAssignments tests I).image (fun a => (a x, a y))).image (fun p => (p.1, p.2, p.1)) := by
    rw [Finset.image_image]
    rfl
  rw [this, card_append_determined]

/-- The pair maximum is the baseline triple maximum with the repeated output `x`. -/
theorem dispersionTuple_pair_eq_dispersionOn [Fintype V] [Fintype F] [Fintype A] (x y : V)
    (tests : List (Term V F arity × Term V F arity)) :
    dispersionTuple (A := A) [.var x, .var y] tests = dispersionOn (A := A) x y (.var x) tests := by
  classical
  apply le_antisymm
  · apply dispersionTuple_le_of_forall
    intro I
    rw [filteredImage_pair_eq_triple_card]
    exact image_le_dispersion _ _ _ _ I
  · apply SigEquiv.dispersionOn_le_of_forall
    intro I
    rw [← filteredImage_pair_eq_triple_card]
    exact image_le_dispersionTuple _ _ I

end DisequalityDispersion
