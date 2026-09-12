import TermGraph

/-! # Cut factorisation and the sharp retained-pair bound (R2)

`eval_eq_of_agree_on_cut`: for a fixed interpretation, if two assignments
agree on the values of every term of a cut `K`, then every term cut by `K`
(in particular every output) evaluates equally.  With the retained pair
`x, y ∈ K` and the guard `x ≠ y`, the filtered image injects into
`guardPairs × (K' → A)` where `K' = K \ {x, y}`, giving

    D(n) ≤ n (n-1) n^(|K|-2) = n^|K| - n^(|K|-1)

for every cut and hence for the minimum cut (`dispersionTuple_le_threshold`).
Sharpness for `j ≥ 2` distinct source outputs is proved in
`sharp_example_dispersion`. -/

namespace DisequalityDispersion

variable {V F A : Type} {arity : F → ℕ}

/-- The numerical threshold `b_k(n) = n^k - n^(k-1)`. -/
def threshold (k n : ℕ) : ℕ := n ^ k - n ^ (k - 1)

theorem threshold_eq (k n : ℕ) (hk : 1 ≤ k) : threshold k n = n ^ (k - 1) * (n - 1) := by
  unfold threshold
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  rw [Nat.mul_sub, Nat.mul_one]

theorem threshold_two (n : ℕ) : threshold 2 n = n * (n - 1) := by
  rw [threshold_eq 2 n (by norm_num)]
  simp

/-- `n (n-1) n^(k-2) = b_k(n)` for `k ≥ 2`. -/
theorem guard_count_eq_threshold (k n : ℕ) (hk : 2 ≤ k) :
    n * (n - 1) * n ^ (k - 2) = threshold k n := by
  rw [threshold_eq k n (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega, pow_succ]
  ring

/-- Monotonicity of the threshold in the degree, for `n ≥ 1`. -/
theorem threshold_mono (j k n : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (hn : 1 ≤ n) :
    threshold j n ≤ threshold k n := by
  rw [threshold_eq j n hj, threshold_eq k n (le_trans hj hjk)]
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right hn (by omega)

/-! ### Factorisation through a cut -/

/-- Evaluation of a term cut by `K` depends only on the values at `K`. -/
theorem eval_eq_of_agree_on_cut (I : Interpretation F arity A) (a a' : V → A)
    (K : Finset (Term V F arity)) (hagree : ∀ u ∈ K, u.eval I a = u.eval I a') :
    ∀ t : Term V F arity, ¬ Avoids K t → t.eval I a = t.eval I a' := by
  intro t
  induction t with
  | var v =>
      intro h
      have hv : Term.var v ∈ K := by
        by_contra hv
        exact h (Avoids.var v hv)
      exact hagree _ hv
  | app f ts ih =>
      intro h
      by_cases hK : Term.app f ts ∈ K
      · exact hagree _ hK
      · simp only [Term.eval]
        congr 1
        funext i
        apply ih i
        intro hi
        exact h (Avoids.app f ts hK i hi)

theorem tupleEval_eq_of_agree_on_cut (I : Interpretation F arity A) (a a' : V → A)
    (K : Finset (Term V F arity)) (outputs : List (Term V F arity)) (hK : IsCut K outputs)
    (hagree : ∀ u ∈ K, u.eval I a = u.eval I a') :
    tupleEval outputs I a = tupleEval outputs I a' := by
  unfold tupleEval
  apply List.map_congr_left
  intro t ht
  exact eval_eq_of_agree_on_cut I a a' K hagree t (hK t ht)

/-! ### Counting through the retained pair -/

section counting
variable [Fintype V] [Fintype A]

/-- The cut without the retained pair. -/
noncomputable def cutRest (K : Finset (Term V F arity)) (x y : V) : Finset (Term V F arity) := by
  classical
  exact (K.erase (.var x)).erase (.var y)

omit [Fintype V] [Fintype A] in
open Classical in
theorem cutRest_card (K : Finset (Term V F arity)) (x y : V) (hxy : x ≠ y)
    (hx : Term.var x ∈ K) (hy : Term.var y ∈ K) : (cutRest K x y).card = K.card - 2 := by
  unfold cutRest
  have hy' : Term.var y ∈ K.erase (.var x) :=
    Finset.mem_erase.mpr ⟨fun h => hxy (Term.var.inj h).symm, hy⟩
  rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx]
  omega

/-- The key of an assignment: the retained pair and the values on the rest of the cut. -/
noncomputable def cutKey (K : Finset (Term V F arity)) (x y : V) (I : Interpretation F arity A)
    (a : V → A) : (A × A) × ({u // u ∈ cutRest K x y} → A) :=
  ((a x, a y), fun u => u.1.eval I a)

omit [Fintype V] [Fintype A] in
open Classical in
theorem agree_of_cutKey_eq (K : Finset (Term V F arity)) (x y : V) (I : Interpretation F arity A)
    (a a' : V → A) (h : cutKey K x y I a = cutKey K x y I a') :
    ∀ u ∈ K, u.eval I a = u.eval I a' := by
  intro u hu
  have h1 : a x = a' x := congrArg (fun c => c.1.1) h
  have h2 : a y = a' y := congrArg (fun c => c.1.2) h
  have h3 : ∀ u' : {u // u ∈ cutRest K x y}, u'.1.eval I a = u'.1.eval I a' :=
    fun u' => congrFun (congrArg Prod.snd h) u'
  by_cases hux : u = .var x
  · subst hux; exact h1
  · by_cases huy : u = .var y
    · subst huy; exact h2
    · have hmem : u ∈ cutRest K x y := by
        unfold cutRest
        exact Finset.mem_erase.mpr ⟨huy, Finset.mem_erase.mpr ⟨hux, hu⟩⟩
      exact h3 ⟨u, hmem⟩

open Classical in
/-- The filtered image is bounded by the number of guarded keys. -/
theorem filteredImage_card_le_cut (x y : V) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (hguard : (.var x, .var y) ∈ tests)
    (K : Finset (Term V F arity)) (hK : IsCut K outputs) (I : Interpretation F arity A) :
    (filteredImage outputs tests I).card ≤
      Fintype.card A * (Fintype.card A - 1) * Fintype.card A ^ (cutRest K x y).card := by
  -- reconstruct the tuple from a key
  let g : (A × A) × ({u // u ∈ cutRest K x y} → A) → List A := fun c =>
    if h : ∃ a ∈ validAssignments tests I, cutKey K x y I a = c then
      tupleEval outputs I (Classical.choose h) else []
  have hsub : filteredImage outputs tests I ⊆
      ((validAssignments tests I).image (cutKey K x y I)).image g := by
    intro o ho
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ho
    refine Finset.mem_image.mpr ⟨cutKey K x y I a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    have hex : ∃ a' ∈ validAssignments tests I, cutKey K x y I a' = cutKey K x y I a := ⟨a, ha, rfl⟩
    simp only [g, dif_pos hex]
    obtain ⟨_, hc⟩ := Classical.choose_spec hex
    exact tupleEval_eq_of_agree_on_cut I _ a K outputs hK (agree_of_cutKey_eq K x y I _ a hc)
  have hkey : (validAssignments tests I).image (cutKey K x y I) ⊆
      (guardPairs (A := A)) ×ˢ (Finset.univ : Finset ({u // u ∈ cutRest K x y} → A)) := by
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hne : a x ≠ a y := by
      have := ha (.var x, .var y) hguard
      simpa [Term.eval] using this
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  calc (filteredImage outputs tests I).card
      ≤ (((validAssignments tests I).image (cutKey K x y I)).image g).card :=
        Finset.card_le_card hsub
    _ ≤ ((validAssignments tests I).image (cutKey K x y I)).card := Finset.card_image_le
    _ ≤ ((guardPairs (A := A)) ×ˢ (Finset.univ : Finset ({u // u ∈ cutRest K x y} → A))).card :=
        Finset.card_le_card hkey
    _ = Fintype.card A * (Fintype.card A - 1) * Fintype.card A ^ (cutRest K x y).card := by
        rw [Finset.card_product, card_guardPairs, Finset.card_univ, Fintype.card_fun,
          Fintype.card_coe]

end counting

/-! ### The sharp bound -/

/-- **Sharp cut bound** (`prop:sharp-cut`): on `Fin n`, `D(n) ≤ n^|K| - n^(|K|-1)` for
every cut `K`, hence `D(n) ≤ b_ρ(n)`. -/
theorem dispersionTuple_le_cut [Fintype V] [Fintype F] (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) (hguard : (.var x, .var y) ∈ tests)
    (K : Finset (Term V F arity)) (hK : IsCut K outputs) (n : ℕ) :
    dispersionTuple (A := Fin n) outputs tests ≤ threshold K.card n := by
  classical
  obtain ⟨hxK, hyK⟩ := retained_pair_mem_cut K outputs hK x y hx hy
  have h2 : 2 ≤ K.card := two_le_card_of_isCut K outputs hK x y hxy hx hy
  apply dispersionTuple_le_of_forall
  intro I
  have := filteredImage_card_le_cut x y outputs tests hguard K hK I
  rw [Fintype.card_fin, cutRest_card K x y hxy hxK hyK, guard_count_eq_threshold _ _ h2] at this
  exact this

theorem dispersionTuple_le_threshold [Fintype V] [Fintype F] (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) (hguard : (.var x, .var y) ∈ tests)
    (n : ℕ) :
    dispersionTuple (A := Fin n) outputs tests ≤ threshold (cutSize outputs tests) n := by
  obtain ⟨K, _, hK, hc⟩ := exists_min_cut outputs tests
  rw [← hc]
  exact dispersionTuple_le_cut x y hxy outputs tests hx hy hguard K hK n

/-! ### Sharpness: `j` distinct source outputs -/

section sharpness
variable {F : Type} {arity : F → ℕ}

/-- The identity output tuple on `Fin j`. -/
def identityOutputs (j : ℕ) : List (Term (Fin j) F arity) := (List.finRange j).map Term.var

/-- The sole guard on the first two sources. -/
def firstGuard (j : ℕ) (hj : 2 ≤ j) : List (Term (Fin j) F arity × Term (Fin j) F arity) :=
  [(.var ⟨0, by omega⟩, .var ⟨1, by omega⟩)]

theorem identityOutputs_tupleEval (j : ℕ) (I : Interpretation F arity A) (a : Fin j → A) :
    tupleEval (identityOutputs (F := F) (arity := arity) j) I a = List.ofFn a := by
  simp [tupleEval, identityOutputs, List.map_map, Function.comp_def, Term.eval, List.ofFn_eq_map]

theorem var_mem_identityOutputs (j : ℕ) (i : Fin j) :
    Term.var i ∈ identityOutputs (F := F) (arity := arity) j := by
  simp [identityOutputs]

/-- Every cut of the identity tuple contains all `j` sources. -/
theorem identity_cut_card (j : ℕ) (K : Finset (Term (Fin j) F arity))
    (hK : IsCut K (identityOutputs j)) : j ≤ K.card := by
  classical
  have hsub : (Finset.univ : Finset (Fin j)).image (Term.var (F := F) (arity := arity)) ⊆ K := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact source_output_mem_cut K _ hK i (var_mem_identityOutputs j i)
  have hcard : ((Finset.univ : Finset (Fin j)).image (Term.var (F := F) (arity := arity))).card = j := by
    rw [Finset.card_image_of_injective _ (fun a b h => Term.var.inj h)]
    simp
  calc j = ((Finset.univ : Finset (Fin j)).image (Term.var (F := F) (arity := arity))).card :=
        hcard.symm
    _ ≤ K.card := Finset.card_le_card hsub

theorem identity_cutSize (j : ℕ) (hj : 2 ≤ j) :
    cutSize (identityOutputs (F := F) (arity := arity) j) (firstGuard j hj) = j := by
  classical
  apply le_antisymm
  · -- the set of all sources is a cut
    have hcut : IsCut ((Finset.univ : Finset (Fin j)).image (Term.var (F := F) (arity := arity)))
        (identityOutputs (F := F) (arity := arity) j) := by
      intro t ht ha
      simp only [identityOutputs, List.mem_map, List.mem_finRange, true_and] at ht
      obtain ⟨i, rfl⟩ := ht
      rw [avoids_var_iff] at ha
      exact ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    refine (cutSize_le_card_of_isCut _ _ _ hcut).trans ?_
    rw [Finset.card_image_of_injective _ (fun a b h => Term.var.inj h)]
    simp
  · obtain ⟨K, _, hK, hc⟩ := exists_min_cut (identityOutputs (F := F) (arity := arity) j)
      (firstGuard j hj)
    rw [← hc]
    exact identity_cut_card j K hK

/-- An assignment realising a guarded pair and free remaining coordinates. -/
def sharpAssign (j : ℕ) (hj : 2 ≤ j) (c : (A × A) × (Fin (j - 2) → A)) : Fin j → A :=
  fun i => if h0 : i.1 = 0 then c.1.1 else if h1 : i.1 = 1 then c.1.2
    else c.2 ⟨i.1 - 2, by omega⟩

theorem sharpAssign_injective (j : ℕ) (hj : 2 ≤ j) :
    Function.Injective (sharpAssign (A := A) j hj) := by
  intro c c' h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [sharpAssign, dif_pos] at h0
  simp only [sharpAssign, show (1 : ℕ) ≠ 0 by omega, dif_neg, not_false_eq_true, dif_pos] at h1
  have h2 : c.2 = c'.2 := by
    funext i
    have := congrFun h ⟨i.1 + 2, by omega⟩
    simp only [sharpAssign, show i.1 + 2 ≠ 0 by omega, show i.1 + 2 ≠ 1 by omega, dif_neg,
      not_false_eq_true, Nat.add_sub_cancel] at this
    exact this
  exact Prod.ext (Prod.ext h0 h1) h2

theorem sharpAssign_valid (j : ℕ) (hj : 2 ≤ j) [Fintype A] (I : Interpretation F arity A)
    (c : (A × A) × (Fin (j - 2) → A)) (hc : c.1.1 ≠ c.1.2) :
    sharpAssign j hj c ∈ validAssignments (firstGuard j hj) I := by
  classical
  simp only [validAssignments, Finset.mem_filter, Finset.mem_univ, true_and, Valid, firstGuard,
    List.mem_singleton, forall_eq, Term.eval]
  simpa [sharpAssign] using hc

/-- `D(n) = b_j(n)` for the identity tuple with the sole first-pair guard. -/
theorem sharp_example_dispersion [Fintype F] (j : ℕ) (hj : 2 ≤ j) (n : ℕ) :
    dispersionTuple (A := Fin n) (identityOutputs (F := F) (arity := arity) j)
      (firstGuard j hj) = threshold j n := by
  classical
  apply le_antisymm
  · have := dispersionTuple_le_threshold (F := F) (arity := arity) (⟨0, by omega⟩ : Fin j)
      ⟨1, by omega⟩ (by simp) (identityOutputs j) (firstGuard j hj)
      (var_mem_identityOutputs j _) (var_mem_identityOutputs j _) (by simp [firstGuard]) n
    rwa [identity_cutSize j hj] at this
  · -- any interpretation works; use an arbitrary one
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : threshold j 0 = 0 := by
        unfold threshold
        rw [zero_pow (by omega)]
        simp
      rw [this]
      exact Nat.zero_le _
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let I : Interpretation F arity (Fin n) := fun _ _ => ⟨0, hn⟩
    refine le_trans ?_ (image_le_dispersionTuple _ _ I)
    let f : (Fin n × Fin n) × (Fin (j - 2) → Fin n) → List (Fin n) :=
      fun c => List.ofFn (sharpAssign j hj c)
    have hinj : Function.Injective f := fun c c' h =>
      sharpAssign_injective j hj (List.ofFn_injective h)
    have hsub : ((guardPairs (A := Fin n)) ×ˢ (Finset.univ : Finset (Fin (j - 2) → Fin n))).image f
        ⊆ filteredImage (identityOutputs j) (firstGuard j hj) I := by
      intro o ho
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ho
      have hc' : c.1.1 ≠ c.1.2 := by
        have := (Finset.mem_product.mp hc).1
        simpa [guardPairs] using this
      simp only [filteredImage, Finset.mem_image]
      exact ⟨sharpAssign j hj c, sharpAssign_valid j hj I c hc', identityOutputs_tupleEval j I _⟩
    calc threshold j n = Fintype.card (Fin n) * (Fintype.card (Fin n) - 1) *
          Fintype.card (Fin n) ^ (j - 2) := by
          rw [Fintype.card_fin, guard_count_eq_threshold j n hj]
      _ = (((guardPairs (A := Fin n)) ×ˢ (Finset.univ : Finset (Fin (j - 2) → Fin n))).image f).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_product, card_guardPairs,
            Finset.card_univ, Fintype.card_fun]
          simp only [Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hsub

end sharpness

end DisequalityDispersion
