import Core

/-! Actual term semantics and the retained-source half of the one-unit theorem.
Operation arities are arbitrary, including zero, and each symbol has one table.
The routing lower bound is not assumed or asserted in this module. -/
namespace DisequalityDispersion

inductive Term (V F : Type) (arity : F → ℕ) where
  | var : V → Term V F arity
  | app (f : F) : (Fin (arity f) → Term V F arity) → Term V F arity

namespace Term
variable {V F A : Type} {arity : F → ℕ}

def eval (I : (f : F) → (Fin (arity f) → A) → A) (a : V → A) :
    Term V F arity → A
  | .var v => a v
  | .app f ts => I f (fun i => eval I a (ts i))

def Uses : Term V F arity → V → Prop
  | .var v, z => v = z
  | .app _ ts, z => ∃ i, Uses (ts i) z

theorem eval_congr_on_uses (t : Term V F arity)
    (I : (f : F) → (Fin (arity f) → A) → A) (a b : V → A)
    (h : ∀ v, t.Uses v → a v = b v) : t.eval I a = t.eval I b := by
  induction t with
  | var v => exact h v rfl
  | app f ts ih =>
      simp only [eval]
      congr 1
      funext i
      exact ih i (fun v hv => h v ⟨i, hv⟩)

end Term

section Images
variable {A V B : Type} [Fintype A] [DecidableEq A]

omit [Fintype A] in
/-- Any extra coordinate determined by the retained pair preserves its image count. -/
theorem card_append_determined (C : Finset (A × A)) (t : A × A → B)
    [DecidableEq B] :
    (C.image (fun p => (p.1, p.2, t p))).card = C.card := by
  apply Finset.card_image_of_injective
  intro p q h
  have h1 := congrArg (fun z : A × A × B => z.1) h
  have h2 := congrArg (fun z : A × A × B => z.2.1) h
  exact Prod.ext h1 h2

theorem card_retained_pair_le [Fintype V] (C : Finset (V → A))
    (x y : V) (t : (V → A) → A)
    (guard : ∀ a ∈ C, a x ≠ a y)
    (determined : ∀ a b, a x = b x → a y = b y → t a = t b) :
    (C.image (fun a => (a x, a y, t a))).card ≤
      Fintype.card A * (Fintype.card A - 1) := by
  classical
  let O := C.image (fun a => (a x, a y, t a))
  let π : A × A × A → A × A := fun o => (o.1, o.2.1)
  have hinj : Set.InjOn π O := by
    intro p hp q hq he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    have hx : a x = b x := congrArg Prod.fst he
    have hy : a y = b y := congrArg Prod.snd he
    exact Prod.ext hx (Prod.ext hy (determined a b hx hy))
  have hsub : O.image π ⊆ guardPairs (A := A) := by
    intro p hp
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ho
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, guard a ha⟩
  calc
    O.card = (O.image π).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (guardPairs (A := A)).card := Finset.card_le_card hsub
    _ = _ := card_guardPairs

theorem card_retained_term_le {F : Type} {arity : F → ℕ} [Fintype V]
    (C : Finset (V → A)) (x y : V) (t : Term V F arity)
    (I : (f : F) → (Fin (arity f) → A) → A)
    (guard : ∀ a ∈ C, a x ≠ a y)
    (uses : ∀ z, t.Uses z → z = x ∨ z = y) :
    (C.image (fun a => (a x, a y, t.eval I a))).card ≤
      Fintype.card A * (Fintype.card A - 1) := by
  apply card_retained_pair_le C x y _ guard
  intro a b hx hy
  apply Term.eval_congr_on_uses
  intro z hz
  rcases uses z hz with rfl | rfl
  · exact hx
  · exact hy

end Images

section CompilerMaximum
variable {S : Type} [Fintype S]

noncomputable def compiledTripleImage {A : Type} [Fintype A]
    (rels : List (List (Letter S))) (w : List (Letter S))
    (p m : S → A → A) : Finset (A × A × A) := by
  classical
  exact (compiledPairs rels w p m).image (fun xy => (xy.1, xy.2, xy.1))

omit [Fintype S] in
theorem compiledTriple_card {A : Type} [Fintype A]
    (rels : List (List (Letter S))) (w : List (Letter S))
    (p m : S → A → A) :
    (compiledTripleImage rels w p m).card = (compiledPairs rels w p m).card := by
  classical
  exact card_append_determined _ Prod.fst

/-- A genuine finite maximum over the two shared tables for each generator. -/
noncomputable def tripleMax (n : ℕ) (rels : List (List (Letter S)))
    (w : List (Letter S)) : ℕ := by
  classical
  exact Finset.univ.sup (fun pm : (S → Fin n → Fin n) × (S → Fin n → Fin n) =>
    (compiledTripleImage rels w pm.1 pm.2).card)

theorem tripleMax_ge_iff (n : ℕ) (rels : List (List (Letter S)))
    (w : List (Letter S)) (k : ℕ) (hk : 0 < k) :
    k ≤ tripleMax n rels w ↔
      ∃ p m : S → Fin n → Fin n, k ≤ (compiledPairs rels w p m).card := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [tripleMax, Nat.succ_le_iff, Finset.lt_sup_iff,
    Finset.mem_univ, true_and, Prod.exists, compiledTriple_card]


end CompilerMaximum

theorem cubic_witness_arithmetic (s : ℕ) (hs : 2 ≤ s) :
    (s ^ 3) * (s ^ 3 - 1) + 1 ≤ ((s ^ 3) / s) ^ 3 := by
  have hpos : 0 < s := by omega
  have hdiv : s ^ 3 / s = s ^ 2 := by
    rw [pow_succ, Nat.mul_div_cancel _ hpos]
  rw [hdiv]
  have hn : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ hpos
  have hmul : s ^ 3 * (s ^ 3 - 1) = s ^ 3 * s ^ 3 - s ^ 3 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hmul]
  have he : (s ^ 2) ^ 3 = s ^ 3 * s ^ 3 := by ring
  rw [he]
  have hle : s ^ 3 ≤ s ^ 3 * s ^ 3 := by nlinarith
  omega

end DisequalityDispersion
