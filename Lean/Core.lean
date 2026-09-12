import Mathlib

/-!
Core of the disequality-dispersion reduction.
All operations are arbitrary total functions until exact saturation forces laws.
No undecidability assertion is installed as an axiom in this file.
-/
namespace DisequalityDispersion

variable {A I : Type*}

theorem avoidance_iff_identity (f : A → A) :
    (∀ x y, x ≠ y → f x ≠ y) ↔ ∀ x, f x = x := by
  constructor
  · intro h x
    by_contra hx
    exact h x (f x) (Ne.symm hx) rfl
  · intro h x y hxy
    simpa [h x] using hxy

def Admissible (laws : I → A → A) (w : A → A) (x y : A) : Prop :=
  x ≠ y ∧ (∀ i, laws i x ≠ y) ∧ w x ≠ x

theorem saturation_iff [Nontrivial A] (laws : I → A → A) (w : A → A) :
    (∀ x y, x ≠ y → Admissible laws w x y) ↔
      (∀ i x, laws i x = x) ∧ ∀ x, w x ≠ x := by
  constructor
  · intro h
    constructor
    · intro i
      exact (avoidance_iff_identity (laws i)).mp (fun x y hxy => (h x y hxy).2.1 i)
    · intro x
      obtain ⟨y, hy⟩ := exists_ne x
      exact (h x y (Ne.symm hy)).2.2
  · rintro ⟨hl, hw⟩ x y hxy
    exact ⟨hxy, fun i => by simpa [hl i x] using hxy, hw x⟩

section Counting
variable [Fintype A] [DecidableEq A]

noncomputable def codePairs (laws : I → A → A) (w : A → A) : Finset (A × A) := by
  classical
  exact Finset.univ.filter (fun p => Admissible laws w p.1 p.2)

def guardPairs : Finset (A × A) := Finset.univ.filter (fun p => p.1 ≠ p.2)

theorem card_guardPairs : (guardPairs (A := A)).card =
    Fintype.card A * (Fintype.card A - 1) := by
  have hrow (x : A) : (Finset.univ.filter (fun y : A => x ≠ y)).card =
      Fintype.card A - 1 := by
    have he : Finset.univ.filter (fun y : A => x ≠ y) = Finset.univ.erase x := by
      ext y
      simp [ne_comm]
    rw [he]
    simp
  calc
    (guardPairs (A := A)).card =
        ∑ x : A, (Finset.univ.filter (fun y : A => x ≠ y)).card := by
      simp [guardPairs, Finset.card_filter, Fintype.sum_prod_type]
    _ = Fintype.card A * (Fintype.card A - 1) := by simp [hrow]

theorem codePairs_subset (laws : I → A → A) (w : A → A) :
    codePairs laws w ⊆ guardPairs (A := A) := by
  classical
  intro p hp
  simp only [codePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩

theorem card_saturation_iff (laws : I → A → A) (w : A → A) :
    (codePairs laws w).card = (guardPairs (A := A)).card ↔
      ∀ x y, x ≠ y → Admissible laws w x y := by
  classical
  constructor
  · intro h
    have he := Finset.eq_of_subset_of_card_le (codePairs_subset laws w) h.ge
    intro x y hxy
    have hp : (x, y) ∈ codePairs laws w := by
      rw [he]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    exact (Finset.mem_filter.mp hp).2
  · intro h
    congr 1
    ext p
    simp only [codePairs, guardPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hp => hp.1, fun hp => h p.1 p.2 hp⟩

theorem card_saturation_iff_laws [Nontrivial A] (laws : I → A → A) (w : A → A) :
    (codePairs laws w).card = (guardPairs (A := A)).card ↔
      (∀ i x, laws i x = x) ∧ ∀ x, w x ≠ x :=
  (card_saturation_iff laws w).trans (saturation_iff laws w)

variable [Fintype I]

def forbiddenRow (laws : I → A → A) (x : A) : Finset A :=
  insert x (Finset.univ.image (fun i => laws i x))

omit [Fintype A] in
theorem card_forbiddenRow_le (laws : I → A → A) (x : A) :
    (forbiddenRow laws x).card ≤ Fintype.card I + 1 := by
  calc
    (forbiddenRow laws x).card ≤ (Finset.univ.image (fun i => laws i x)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ Fintype.card I + 1 := Nat.add_le_add_right (Finset.card_image_le.trans_eq (Finset.card_univ)) 1

theorem code_card_rows (laws : I → A → A) (w : A → A) :
    (codePairs laws w).card =
      ∑ x : A, if w x = x then 0 else Fintype.card A - (forbiddenRow laws x).card := by
  classical
  have hrow (x : A) : (Finset.univ.filter (fun y => Admissible laws w x y)).card =
      if w x = x then 0 else Fintype.card A - (forbiddenRow laws x).card := by
    by_cases hx : w x = x
    · simp [hx, Admissible]
    · have he : Finset.univ.filter (fun y => Admissible laws w x y) =
          (forbiddenRow laws x)ᶜ := by
        ext y
        simp [forbiddenRow, Admissible, hx, ne_comm]
      rw [he, Finset.card_compl]
      simp [hx]
  calc
    (codePairs laws w).card = ∑ x : A, (Finset.univ.filter (fun y => Admissible laws w x y)).card := by
      simp [codePairs, Finset.card_filter, Fintype.sum_prod_type, -Finset.sum_boole]
    _ = _ := by simp [hrow]

theorem code_card_lower (laws : I → A → A) (w : A → A) (hw : ∀ x, w x ≠ x) :
    Fintype.card A * (Fintype.card A - (Fintype.card I + 1)) ≤ (codePairs laws w).card := by
  classical
  rw [code_card_rows]
  calc
    Fintype.card A * (Fintype.card A - (Fintype.card I + 1)) =
        ∑ _x : A, (Fintype.card A - (Fintype.card I + 1)) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun x _ => by
      simp only [if_neg (hw x)]
      exact Nat.sub_le_sub_left (card_forbiddenRow_le laws x) _)

end Counting

section Words
variable {S : Type*}

/-- The list is in outermost-to-innermost order. -/
def evalWord (f : S → A → A) : List S → A → A
  | [], x => x
  | a :: w, x => f a (evalWord f w x)

theorem evalWord_shift (n : ℕ) (v : List S) (x : ZMod n) :
    evalWord (fun (_ : S) x => x + 1) v x = x + (v.length : ZMod n) := by
  induction v with
  | nil => simp [evalWord]
  | cons a v ih => simp [evalWord, ih, Nat.cast_add, add_assoc]

theorem shift_word_fixedPointFree (n : ℕ) (v : List S)
    (hpos : 0 < v.length) (hlt : v.length < n) :
    ∀ x : ZMod n, evalWord (fun (_ : S) x => x + 1) v x ≠ x := by
  intro x hx
  rw [evalWord_shift] at hx
  have hz : (v.length : ZMod n) = 0 := add_left_cancel (hx.trans (add_zero x).symm)
  have hd : n ∣ v.length := (ZMod.natCast_eq_zero_iff v.length n).mp hz
  exact Nat.not_dvd_of_pos_of_lt hpos hlt hd

/-- Positive and negative letters have separate unary tables. -/
abbrev Letter (S : Type*) := S × Bool

def signedTables (p m : S → A → A) : Letter S → A → A :=
  fun l => if l.2 then p l.1 else m l.1

def groupLetter {Q : Type*} [Group Q] (g : S → Q) (l : Letter S) : Q :=
  if l.2 then g l.1 else (g l.1)⁻¹

def groupWord {Q : Type*} [Group Q] (g : S → Q) (w : List (Letter S)) : Q :=
  (w.map (groupLetter g)).prod

theorem evalWord_mul_left {Q : Type*} [Group Q] (f : S → Q) (w : List S) (x : Q) :
    evalWord (fun s x => f s * x) w x = (w.map f).prod * x := by
  induction w with
  | nil => simp [evalWord]
  | cons a w ih => simp [evalWord, ih, mul_assoc]

theorem evalWord_perm (f : S → Equiv.Perm A) (w : List S) (x : A) :
    evalWord (fun s => f s) w x = (w.map f).prod x := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [evalWord, List.map_cons, List.prod_cons] using congrArg (f a) ih

/-- This is the actual list of inverse and relator disequality tests. -/
def CompiledPerfect (rels : List (List (Letter S))) (w : List (Letter S))
    (p m : S → A → A) : Prop :=
  ∀ x y, x ≠ y →
    (∀ i, p i (m i x) ≠ y) ∧
    (∀ i, m i (p i x) ≠ y) ∧
    (∀ r ∈ rels, evalWord (signedTables p m) r x ≠ y) ∧
    evalWord (signedTables p m) w x ≠ x

noncomputable def compiledPairs [Fintype A]
    (rels : List (List (Letter S))) (w : List (Letter S))
    (p m : S → A → A) : Finset (A × A) := by
  classical
  exact Finset.univ.filter (fun xy =>
    xy.1 ≠ xy.2 ∧
    (∀ i, p i (m i xy.1) ≠ xy.2) ∧
    (∀ i, m i (p i xy.1) ≠ xy.2) ∧
    (∀ r ∈ rels, evalWord (signedTables p m) r xy.1 ≠ xy.2) ∧
    evalWord (signedTables p m) w xy.1 ≠ xy.1)

theorem compiled_card_saturation_iff [Fintype A]
    (rels : List (List (Letter S))) (w : List (Letter S)) (p m : S → A → A) :
    (compiledPairs rels w p m).card = Fintype.card A * (Fintype.card A - 1) ↔
      CompiledPerfect rels w p m := by
  classical
  have hsub : compiledPairs rels w p m ⊆ guardPairs (A := A) := by
    intro xy hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2.1⟩
  rw [← card_guardPairs]
  constructor
  · intro hc x y hxy
    have he := Finset.eq_of_subset_of_card_le hsub hc.ge
    have hp : (x, y) ∈ compiledPairs rels w p m := by
      rw [he]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    exact (Finset.mem_filter.mp hp).2.2
  · intro h
    have he : compiledPairs rels w p m = guardPairs (A := A) := by
      apply Finset.Subset.antisymm hsub
      intro xy hxy
      have hn := (Finset.mem_filter.mp hxy).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn, h xy.1 xy.2 hn⟩
    rw [he]

theorem compiledPerfect_iff [Nontrivial A]
    (rels : List (List (Letter S))) (w : List (Letter S)) (p m : S → A → A) :
    CompiledPerfect rels w p m ↔
      (∀ i x, p i (m i x) = x) ∧
      (∀ i x, m i (p i x) = x) ∧
      (∀ r ∈ rels, ∀ x, evalWord (signedTables p m) r x = x) ∧
      ∀ x, evalWord (signedTables p m) w x ≠ x := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact (avoidance_iff_identity _).mp (fun x y hxy => (h x y hxy).1 i)
    · intro i
      exact (avoidance_iff_identity _).mp (fun x y hxy => (h x y hxy).2.1 i)
    · intro r hr
      exact (avoidance_iff_identity _).mp (fun x y hxy => (h x y hxy).2.2.1 r hr)
    · intro x
      obtain ⟨y, hy⟩ := exists_ne x
      exact (h x y (Ne.symm hy)).2.2.2
  · rintro ⟨hpm, hmp, hr, hw⟩ x y hxy
    refine ⟨?_, ?_, ?_, hw x⟩
    · intro i
      simpa [hpm i x] using hxy
    · intro i
      simpa [hmp i x] using hxy
    · intro r hrel
      simpa [hr r hrel x] using hxy

def generatorPerms (p m : S → A → A)
    (hpm : ∀ i x, p i (m i x) = x) (hmp : ∀ i x, m i (p i x) = x) :
    S → Equiv.Perm A := fun i =>
  { toFun := p i, invFun := m i, left_inv := hmp i, right_inv := hpm i }

theorem signedTables_perm (p m : S → A → A)
    (hpm : ∀ i x, p i (m i x) = x) (hmp : ∀ i x, m i (p i x) = x)
    (l : Letter S) :
    signedTables p m l = ⇑(groupLetter (generatorPerms p m hpm hmp) l) := by
  rcases l with ⟨i, b⟩
  cases b <;> rfl

theorem compiledPerfect_to_group [Nontrivial A]
    (rels : List (List (Letter S))) (w : List (Letter S)) (p m : S → A → A)
    (h : CompiledPerfect rels w p m) :
    ∃ g : S → Equiv.Perm A,
      (∀ r ∈ rels, groupWord g r = 1) ∧ groupWord g w ≠ 1 := by
  obtain ⟨hpm, hmp, hr, hw⟩ := (compiledPerfect_iff rels w p m).mp h
  let g := generatorPerms p m hpm hmp
  have he (v : List (Letter S)) (x : A) :
      evalWord (signedTables p m) v x = groupWord g v x := by
    have ht : signedTables p m = fun l => ⇑(groupLetter g l) := by
      funext l
      exact signedTables_perm p m hpm hmp l
    rw [ht]
    exact evalWord_perm (groupLetter g) v x
  refine ⟨g, ?_, ?_⟩
  · intro r hrel
    ext x
    exact (he r x).symm.trans (hr r hrel x)
  · intro hgw
    obtain ⟨x⟩ := (inferInstance : Nonempty A)
    apply hw x
    rw [he, hgw]
    rfl

theorem group_to_compiledPerfect {Q : Type*} [Group Q]
    (rels : List (List (Letter S))) (w : List (Letter S)) (g : S → Q)
    (hr : ∀ r ∈ rels, groupWord g r = 1) (hw : groupWord g w ≠ 1) :
    CompiledPerfect rels w (fun i x => g i * x) (fun i x => (g i)⁻¹ * x) := by
  have he (v : List (Letter S)) (x : Q) :
      evalWord (signedTables (fun i x => g i * x) (fun i x => (g i)⁻¹ * x)) v x =
        groupWord g v * x := by
    have ht : signedTables (fun i x => g i * x) (fun i x => (g i)⁻¹ * x) =
        fun l x => groupLetter g l * x := by
      funext l x
      rcases l with ⟨i, b⟩
      cases b <;> rfl
    rw [ht]
    exact evalWord_mul_left (groupLetter g) v x
  intro x y hxy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa [← mul_assoc] using hxy
  · intro i
    simpa [← mul_assoc] using hxy
  · intro r hrel
    simpa [he, hr r hrel] using hxy
  · rw [he]
    intro hc
    apply hw
    exact mul_right_cancel (hc.trans (one_mul x).symm)

/-- Existential finite semantics, before computability/encoding is imposed. -/
def HasFinitePerfectCode (rels : List (List (Letter S))) (w : List (Letter S)) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : Nontrivial A) (p m : S → A → A),
    CompiledPerfect rels w p m

def HasFiniteGroupWitness (rels : List (List (Letter S))) (w : List (Letter S)) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Fintype Q) (g : S → Q),
    (∀ r ∈ rels, groupWord g r = 1) ∧ groupWord g w ≠ 1

theorem finite_semantic_reduction (rels : List (List (Letter S))) (w : List (Letter S)) :
    HasFinitePerfectCode rels w ↔ HasFiniteGroupWitness rels w := by
  classical
  constructor
  · rintro ⟨A, hfin, hnt, p, m, h⟩
    letI := hfin
    letI := hnt
    obtain ⟨g, hr, hw⟩ := compiledPerfect_to_group rels w p m h
    exact ⟨Equiv.Perm A, inferInstance, inferInstance, g, hr, hw⟩
  · rintro ⟨Q, hgroup, hfin, g, hr, hw⟩
    letI := hgroup
    letI := hfin
    have hnt : Nontrivial Q := ⟨⟨groupWord g w, 1, hw⟩⟩
    exact ⟨Q, hfin, hnt, (fun i x => g i * x), (fun i x => (g i)⁻¹ * x),
      group_to_compiledPerfect rels w g hr hw⟩

def HasFinitePerfectCardinality
    (rels : List (List (Letter S))) (w : List (Letter S)) : Prop :=
  ∃ (A : Type) (hfin : Fintype A) (_ : Nontrivial A) (p m : S → A → A),
    letI := hfin
    (compiledPairs rels w p m).card = Fintype.card A * (Fintype.card A - 1)

theorem finite_cardinality_iff_perfect
    (rels : List (List (Letter S))) (w : List (Letter S)) :
    HasFinitePerfectCardinality rels w ↔ HasFinitePerfectCode rels w := by
  classical
  constructor
  · rintro ⟨A, hfin, hnt, p, m, hc⟩
    letI := hfin
    exact ⟨A, hfin, hnt, p, m, (compiled_card_saturation_iff rels w p m).mp hc⟩
  · rintro ⟨A, hfin, hnt, p, m, h⟩
    letI := hfin
    exact ⟨A, hfin, hnt, p, m, (compiled_card_saturation_iff rels w p m).mpr h⟩

theorem finite_cardinality_reduction
    (rels : List (List (Letter S))) (w : List (Letter S)) :
    HasFinitePerfectCardinality rels w ↔ HasFiniteGroupWitness rels w :=
  (finite_cardinality_iff_perfect rels w).trans (finite_semantic_reduction rels w)

end Words

/-- The only external input needed here is the classical finite-group
separation theorem, stated on this concrete finite signed-word encoding.
It is an explicit hypothesis, not a new axiom or an assumed coding conclusion. -/
theorem undecidable_perfection_of_group_separation (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (classicalInput : ¬ ComputablePred (HasFiniteGroupWitness rels)) :
    ¬ ComputablePred (HasFinitePerfectCardinality rels) := by
  intro h
  exact classicalInput (h.of_eq (fun w => finite_cardinality_reduction rels w))

end DisequalityDispersion
