import MParseList
import MLib

/-! # The parser on the machine, part 3: records and the full input

Parsers for pairs, nodes, instances, `GInstance`s and the whole input are built from the
natural-number and list parsers by *sequencing* (`seqP`: run a parser, save its result in a
variable, continue) and *record allocation* (`recM`: copy saved variables into fresh heap
cells).  The contract `ParserSpecP` is `ParserSpec` with a precondition, used to carry the
saved fields through the sequence. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Parser contracts with a precondition and a base address

`ParserSpecL Pre c f rep W S d`: like `ParserSpec`, but the representation of the result is
placed in `[lo, m' HP)` for any base address `lo ≤ m HP` supplied by the caller, and the
precondition `Pre lo m` may refer to it (it is used to say that previously parsed fields are
held in variables, with their data in `[lo, m HP)`). -/

def PResultL {α : Type} (rep : Rep α) (lo : ℕ) (m' : Mem) (bs : List Bool)
    (r : Option (α × List Bool)) : Prop :=
  match r with
  | none => m' OK = 0
  | some (a, rest) => m' OK = 1 ∧ rep m' lo (m' HP) (m' VAL) a ∧ m' POS = bs.length - rest.length

def ParserSpecL {α : Type} (Pre : ℕ → Mem → Prop) (c : Cmd) (f : List Bool → Option (α × List Bool))
    (rep : Rep α) (W : List ℕ) (S d : ℕ) : Prop :=
  ∀ (m : Mem) (bs : List Bool) (p lo : ℕ), PState m bs → IN ≤ lo → lo ≤ m HP → Pre lo m →
    m POS = p → p ≤ bs.length →
    ∃ m' k, Cmd.Exec c m m' k ∧ k ≤ S * (bs.length - p + 1) ^ d ∧ Pres m m' (m HP) (HP :: W) ∧
      PState m' bs ∧ m HP ≤ m' HP ∧ PResultL rep lo m' bs (f (bs.drop p))

theorem ParserSpec.toL {α : Type} {c : Cmd} {f : List Bool → Option (α × List Bool)} {rep : Rep α}
    (hgr : GoodRep rep) {W : List ℕ} {S d : ℕ} (h : ParserSpec c f rep W S d)
    (Pre : ℕ → Mem → Prop) : ParserSpecL Pre c f rep W S d := by
  intro m bs p lo hs _ hlo _ hp hpN
  obtain ⟨m', k, e, hk, pres, hs', hhp, res⟩ := h m bs p hs hp hpN
  refine ⟨m', k, e, hk, pres, hs', hhp, ?_⟩
  unfold PResult at res
  unfold PResultL
  revert res
  cases f (bs.drop p) with
  | none => exact id
  | some q =>
      obtain ⟨a, rest⟩ := q
      rintro ⟨r1, r2, r3⟩
      exact ⟨r1, hgr.mono m' _ _ _ _ _ _ r2 hlo le_rfl, r3⟩

theorem ParserSpecL.mono {α : Type} {Pre Pre' : ℕ → Mem → Prop} {c : Cmd}
    {f : List Bool → Option (α × List Bool)} {rep : Rep α} {W W' : List ℕ} {S d S' d' : ℕ}
    (h : ParserSpecL Pre c f rep W S d) (hPre : ∀ lo m, Pre' lo m → Pre lo m)
    (hW : ∀ x, x ∈ W → x ∈ W') (hS : S ≤ S') (hd : d ≤ d') :
    ParserSpecL Pre' c f rep W' S' d' := by
  intro m bs p lo hs hlo1 hlo2 hpre hp hpN
  obtain ⟨m', k, e, hk, pres, hs', hhp, res⟩ := h m bs p lo hs hlo1 hlo2 (hPre lo m hpre) hp hpN
  refine ⟨m', k, e, ?_, pres.mono le_rfl (fun x hx => by
    simp only [List.mem_cons] at hx ⊢; rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (hW x h)), hs', hhp, res⟩
  have h1 : (bs.length - p + 1) ^ d ≤ (bs.length - p + 1) ^ d' := Nat.pow_le_pow_right (by omega) hd
  calc k ≤ S * (bs.length - p + 1) ^ d := hk
    _ ≤ S' * (bs.length - p + 1) ^ d' := Nat.mul_le_mul hS h1

/-- Cost bounds of the shape `S * X ^ d` are monotone in `S` and `d` (`X ≥ 1`). -/
theorem cost_le {S d S' d' X k : ℕ} (hk : k ≤ S * X ^ d) (hX : 1 ≤ X) (hS : S ≤ S') (hd : d ≤ d') :
    k ≤ S' * X ^ d' :=
  le_trans hk (Nat.mul_le_mul hS (Nat.pow_le_pow_right hX hd))

/-! ### Sequencing -/

/-- Run `c₁`; on success save its result (`VAL`) in `T` and run `c₂`. -/
def seqP (T : ℕ) (c₁ c₂ : Cmd) : Cmd := .seq c₁ (.ite (.eq OK ONE) (.seq (mov T VAL) c₂) nop)

/-- The precondition of the continuation: the previous result `a` is held in `T`, with its
data in `[lo, m HP)`. -/
def Holds {α : Type} (rep : Rep α) (T : ℕ) (a : α) (lo : ℕ) (m : Mem) : Prop :=
  IN ≤ lo ∧ ∃ hi, lo ≤ hi ∧ hi ≤ m HP ∧ rep m lo hi (m T) a

theorem Holds.of_pres {α : Type} {rep : Rep α} (hr : GoodRep rep) {T : ℕ} {a : α} {lo : ℕ}
    {m m' : Mem} (h : Holds rep T a lo m) {W : List ℕ} (hp : Pres m m' (m HP) (HP :: W))
    (hhp : m HP ≤ m' HP) (hW : ∀ x, x ∈ W → x < IN) (hT : T ∉ W) (hTIN : T < IN) (hT0 : T ≠ HP) :
    Holds rep T a lo m' := by
  obtain ⟨hlo, hi, h1, h2, h3⟩ := h
  refine ⟨hlo, hi, h1, le_trans h2 hhp, ?_⟩
  rw [hp T (by omega) (by simp only [List.mem_cons, not_or]; exact ⟨hT0, hT⟩)]
  exact hr.frame m m' lo hi _ _ h3 (fun x hx1 hx2 => hp x (by omega) (by
    simp only [List.mem_cons, not_or]
    exact ⟨by unfold HP IN at *; omega, fun hxW => by have := hW x hxW; omega⟩))

theorem Holds.of_pres_good {α : Type} {rep : Rep α} (hr : GoodRep rep) {T : ℕ} {a : α} {lo : ℕ}
    {m m' : Mem} (h : Holds rep T a lo m) {W : List ℕ} (hp : Pres m m' (m HP) (HP :: W))
    (hhp : m HP ≤ m' HP) (hW : GoodVars W) (hT : T ∉ W) (hTIN : T < IN) (hT0 : T ≠ HP) :
    Holds rep T a lo m' :=
  h.of_pres hr hp hhp (fun x hx => (hW x hx).2) hT hTIN hT0

theorem Holds.write {α : Type} {rep : Rep α} (hr : GoodRep rep) {T : ℕ} {a : α} {lo : ℕ} {m : Mem}
    (h : Holds rep T a lo m) (x v : ℕ) (hx : x < IN) (hxT : x ≠ T) (hx0 : x ≠ HP) :
    Holds rep T a lo (m.write x v) := by
  obtain ⟨hlo, hi, h1, h2, h3⟩ := h
  refine ⟨hlo, hi, h1, by rw [Mem.write_ne _ _ (Ne.symm hx0)]; exact h2, ?_⟩
  rw [Mem.write_ne _ _ (Ne.symm hxT)]
  exact hr.frame m _ lo hi _ _ h3 (fun y hy1 hy2 => Mem.write_ne _ _ (by omega))

/-- A `PState` survives a step that writes only variables `≥ 5` and grows the heap. -/
theorem PState.of_agree {m m' : Mem} {bs : List Bool} (h : PState m bs) {W : List ℕ}
    (hp : Pres m m' (m HP) (HP :: W)) (hW : GoodVars W) (hhp : m HP ≤ m' HP) : PState m' bs := by
  have hlt : ∀ x, x ∈ HP :: W → x < IN := by
    intro x hx; simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · addr'
    · exact (hW x hx).2
  have hn : ∀ x, x ∈ W → x ≤ 4 → False := fun x hx h4 => by have := (hW x hx).1; omega
  refine ⟨h.input.of_pres hp h.hp hlt, ?_, ?_, ?_, ?_, le_trans h.hp hhp⟩
  · rw [hp N (h.var_lt N (by decide)) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, fun hm => hn N hm (by decide)⟩), h.n]
  · rw [hp INB (h.var_lt INB (by decide)) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, fun hm => hn INB hm (by decide)⟩), h.inb]
  · rw [hp ONE (h.var_lt ONE (by decide)) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, fun hm => hn ONE hm (by decide)⟩), h.one]
  · rw [hp ZERO (h.var_lt ZERO (by decide)) (by simp only [List.mem_cons, not_or]; exact ⟨by decide, fun hm => hn ZERO hm (by decide)⟩), h.zero]

/-- Sequencing two parsers: `bindP`. -/
theorem seqP_pspec {α β : Type} {f₁ : List Bool → Option (α × List Bool)}
    {g : α → List Bool → Option (β × List Bool)} {rep₁ : Rep α} {rep₂ : Rep β}
    (hgr₁ : GoodRep rep₁) (hsuf₁ : SuffixP f₁)
    {c₁ c₂ : Cmd} {W₁ W₂ : List ℕ} {S₁ d₁ S₂ d₂ : ℕ} (T : ℕ) (hT : 5 ≤ T ∧ T < IN) (hTP : T ≠ POS)
    (hT₁ : T ∉ W₁) (hW₁ : GoodVars W₁)
    {Pre : ℕ → Mem → Prop}
    (hPre : ∀ lo m m', Pre lo m → Pres m m' (m HP) (HP :: W₁) → m HP ≤ m' HP → Pre lo m')
    (hPre' : ∀ lo m v, Pre lo m → Pre lo (m.write T v))
    (h₁ : ParserSpecL Pre c₁ f₁ rep₁ W₁ S₁ d₁)
    (h₂ : ∀ a, ParserSpecL (fun lo m => Pre lo m ∧ Holds rep₁ T a lo m) c₂ (g a) rep₂ W₂ S₂ d₂) :
    ParserSpecL Pre (seqP T c₁ c₂) (bindP f₁ g) rep₂ (T :: (W₁ ++ W₂)) (S₁ + S₂ + 5) (max d₁ d₂) := by
  intro m bs p lo hs hlo1 hlo2 hpre hp hpN
  obtain ⟨X, hX⟩ : ∃ X, X = bs.length - p + 1 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  obtain ⟨m₁, k₁, e₁, hk₁, pres₁, hs₁, hhp₁, res₁⟩ := h₁ m bs p lo hs hlo1 hlo2 hpre hp hpN
  rw [← hX] at hk₁
  have hhp0 := hs.hp
  unfold PResultL at res₁
  cases hf : f₁ (bs.drop p) with
  | none =>
      rw [hf] at res₁
      have hok : (Cond.eq OK ONE).eval m₁ = false := by simp [Cond.eval, res₁, hs₁.one]
      refine ⟨m₁, _, Cmd.Exec.seq e₁ (Cmd.Exec.ite_false hok (Exec.nop m₁)), ?_, ?_, hs₁, hhp₁, ?_⟩
      · rw [← hX]
        have := cost_le hk₁ hX1 (le_refl S₁) (le_max_left d₁ d₂)
        have h2 : 1 ≤ X ^ max d₁ d₂ := Nat.one_le_pow _ _ hX1
        have h3 : (S₁ + S₂ + 5) * X ^ max d₁ d₂ = S₁ * X ^ max d₁ d₂ + (S₂ + 5) * X ^ max d₁ d₂ := by ring
        have h4 : 5 ≤ (S₂ + 5) * X ^ max d₁ d₂ := by nlinarith
        omega
      · exact pres₁.mono le_rfl (fun x hx => by
          simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto)
      · unfold PResultL; rw [bindP_none hf]; exact res₁
  | some q =>
      obtain ⟨a, rest⟩ := q
      rw [hf] at res₁
      obtain ⟨hok₁, hrep₁, hpos₁⟩ := res₁
      have hrest : rest = bs.drop (bs.length - rest.length) := suffix_drop hsuf₁ bs p hpN hf
      obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ = bs.length - rest.length := ⟨_, rfl⟩
      rw [← hp₁] at hpos₁ hrest
      have hp₁N : p₁ ≤ bs.length := by omega
      have hpp₁ : p ≤ p₁ := by
        have : (bs.drop p).length = bs.length - p := List.length_drop
        have h2 : rest.length ≤ (bs.drop p).length := by
          obtain ⟨pre, hpre⟩ := hsuf₁ _ _ _ hf
          rw [hpre, List.length_append]; omega
        omega
      have hok : (Cond.eq OK ONE).eval m₁ = true := by simp [Cond.eval, hok₁, hs₁.one]
      -- save the result
      obtain ⟨m₂, hm₂⟩ : ∃ m₂, m₂ = m₁.write T (m₁ VAL) := ⟨_, rfl⟩
      have e₂ : Cmd.Exec (mov T VAL) m₁ m₂ 1 := by rw [hm₂]; exact Exec.mov _ _ _
      have q₂ : ∀ x, x ≠ T → m₂ x = m₁ x := fun x hx => by rw [hm₂, Mem.write_ne _ _ hx]
      have hs₂ : PState m₂ bs := hs₁.of_pres' (by rw [hm₂]; exact pres_write _ _ _ _)
        (by intro x hx; simp at hx; subst hx; exact hT)
      have hpre₂ : Pre lo m₂ := by rw [hm₂]; exact hPre' lo m₁ _ (hPre lo m m₁ hpre pres₁ hhp₁)
      have hm₂HP : m₂ HP = m₁ HP := q₂ HP (by addr')
      have hholds : Holds rep₁ T a lo m₂ := by
        refine ⟨hlo1, m₁ HP, by omega, by rw [hm₂HP], ?_⟩
        rw [hm₂, Mem.write_same]
        exact hgr₁.frame m₁ _ lo (m₁ HP) _ _ hrep₁ (fun x hx1 hx2 => Mem.write_ne _ _ (by addr'))
      have hpos₂ : m₂ POS = p₁ := by rw [q₂ POS (Ne.symm hTP), hpos₁]
      -- the continuation
      obtain ⟨m₃, k₃, e₃, hk₃, pres₃, hs₃, hhp₃, res₃⟩ := h₂ a m₂ bs p₁ lo hs₂ hlo1
        (by rw [hm₂HP]; omega) ⟨hpre₂, hholds⟩ hpos₂ hp₁N
      refine ⟨m₃, _, Cmd.Exec.seq e₁ (Cmd.Exec.ite_true hok (Cmd.Exec.seq e₂ e₃)), ?_, ?_, hs₃, ?_, ?_⟩
      · -- cost
        rw [← hX]
        have c₁ := cost_le hk₁ hX1 (le_refl S₁) (le_max_left d₁ d₂)
        have c₂ : k₃ ≤ S₂ * X ^ max d₁ d₂ := by
          have h1 : bs.length - p₁ + 1 ≤ X := by omega
          have h2 : (bs.length - p₁ + 1) ^ d₂ ≤ X ^ max d₁ d₂ :=
            le_trans (Nat.pow_le_pow_left h1 d₂) (Nat.pow_le_pow_right hX1 (le_max_right d₁ d₂))
          exact le_trans hk₃ (Nat.mul_le_mul_left _ h2)
        have h2 : 1 ≤ X ^ max d₁ d₂ := Nat.one_le_pow _ _ hX1
        have h3 : (S₁ + S₂ + 5) * X ^ max d₁ d₂ = S₁ * X ^ max d₁ d₂ + S₂ * X ^ max d₁ d₂ + 5 * X ^ max d₁ d₂ := by ring
        omega
      · -- frame
        intro x hx hxV
        simp only [List.mem_cons, List.mem_append, not_or] at hxV
        rw [pres₃ x (by omega) (by simp only [List.mem_cons, not_or]; exact ⟨hxV.1, hxV.2.2.2⟩),
          q₂ x hxV.2.1, pres₁ x hx (by simp only [List.mem_cons, not_or]; exact ⟨hxV.1, hxV.2.2.1⟩)]
      · rw [hm₂HP] at hhp₃; exact le_trans hhp₁ hhp₃
      · unfold PResultL at res₃ ⊢
        rw [bindP_of_eq hf, hrest]
        exact res₃


/-! ### Record allocation -/

/-- Copy the variables `Ts` into fresh heap cells (advancing `HP`), then `OK := 1`. -/
def allocM : List ℕ → Cmd
  | [] => setc OK 1
  | T :: Ts => .seq (store HP T) (.seq (add HP HP ONE) (allocM Ts))

/-- `VAL := HP`, then allocate the record `Ts`. -/
def recM (Ts : List ℕ) : Cmd := .seq (mov VAL HP) (allocM Ts)

theorem allocM_spec (Ts : List ℕ) (hTs : ∀ T, T ∈ Ts → T < IN ∧ T ≠ HP ∧ T ≠ OK) :
    ∀ m, m ONE = 1 → IN ≤ m HP →
      ∃ m', Cmd.Exec (allocM Ts) m m' (2 * Ts.length + 1) ∧ m' HP = m HP + Ts.length ∧
        (∀ x, x ≠ HP → x ≠ OK → ¬ (m HP ≤ x ∧ x < m HP + Ts.length) → m' x = m x) ∧
        (∀ i, (h : i < Ts.length) → m' (m HP + i) = m Ts[i]) ∧ m' OK = 1 := by
  induction Ts with
  | nil =>
      intro m hone hhp
      refine ⟨m.write OK 1, Exec.setc _ _ _, by rw [Mem.write_ne _ _ (by addr')]; simp,
        fun x _ h2 _ => Mem.write_ne _ _ h2, fun i h => absurd h (Nat.not_lt_zero _), Mem.write_same _ _ _⟩
  | cons T Ts ih =>
      intro m hone hhp
      have hT := hTs T (List.mem_cons_self)
      obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write (m HP) (m T) := ⟨_, rfl⟩
      have e1 : Cmd.Exec (store HP T) m m1 1 := by rw [hm1]; exact Exec.store _ _ _
      obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write HP (m HP + 1) := ⟨_, rfl⟩
      have e2 : Cmd.Exec (add HP HP ONE) m1 m2 1 := by
        have := Exec.add HP HP ONE m1
        rw [hm1, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hone] at this
        rw [hm2, hm1]; exact this
      have q2 : ∀ x, x ≠ HP → x ≠ m HP → m2 x = m x := fun x h1 h2 => by
        rw [hm2, Mem.write_ne _ _ h1, hm1, Mem.write_ne _ _ h2]
      have m2HP : m2 HP = m HP + 1 := by rw [hm2, Mem.write_same]
      have m2cell : m2 (m HP) = m T := by rw [hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
      obtain ⟨m3, e3, hp3, fr3, cells3, ok3⟩ := ih (fun T' hT' => hTs T' (List.mem_cons_of_mem _ hT')) m2
        (by rw [q2 ONE (by addr') (by addr'), hone]) (by rw [m2HP]; omega)
      rw [m2HP] at hp3 fr3 cells3
      refine ⟨m3, ?_, by rw [hp3, List.length_cons]; omega, ?_, ?_, ok3⟩
      · have := Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3)
        rw [show 1 + (1 + (2 * Ts.length + 1)) = 2 * (T :: Ts).length + 1 by simp; omega] at this
        exact this
      · intro x h1 h2 h3
        rw [fr3 x h1 h2 (by simp only [List.length_cons] at h3; omega), q2 x h1 (by
          simp only [List.length_cons] at h3; omega)]
      · intro i hi
        cases i with
        | zero =>
            simp only [Nat.add_zero, List.getElem_cons_zero]
            rw [fr3 _ (by addr') (by addr') (by omega), m2cell]
        | succ i =>
            simp only [List.length_cons] at hi
            simp only [List.getElem_cons_succ]
            have hTi := hTs Ts[i] (List.mem_cons_of_mem _ (List.getElem_mem (by omega)))
            rw [show m HP + (i + 1) = m HP + 1 + i by omega, cells3 i (by omega),
              q2 _ hTi.2.1 (by have := hTi.1; omega)]

theorem recM_spec (Ts : List ℕ) (hTs : ∀ T, T ∈ Ts → T < IN ∧ T ≠ HP ∧ T ≠ OK ∧ T ≠ VAL) :
    ∀ m, m ONE = 1 → IN ≤ m HP →
      ∃ m', Cmd.Exec (recM Ts) m m' (2 * Ts.length + 2) ∧ m' HP = m HP + Ts.length ∧
        (∀ x, x ≠ HP → x ≠ OK → x ≠ VAL → ¬ (m HP ≤ x ∧ x < m HP + Ts.length) → m' x = m x) ∧
        (∀ i, (h : i < Ts.length) → m' (m HP + i) = m Ts[i]) ∧ m' OK = 1 ∧ m' VAL = m HP := by
  intro m hone hhp
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write VAL (m HP) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov VAL HP) m m1 1 := by rw [hm1]; exact Exec.mov _ _ _
  have q1 : ∀ x, x ≠ VAL → m1 x = m x := fun x h => by rw [hm1, Mem.write_ne _ _ h]
  obtain ⟨m2, e2, hp2, fr2, cells2, ok2⟩ := allocM_spec Ts (fun T hT => ⟨(hTs T hT).1, (hTs T hT).2.1, (hTs T hT).2.2.1⟩)
    m1 (by rw [q1 ONE (by addr'), hone]) (by rw [q1 HP (by addr')]; exact hhp)
  rw [q1 HP (by addr')] at hp2 fr2 cells2
  refine ⟨m2, ?_, hp2, ?_, ?_, ok2, ?_⟩
  · have := Cmd.Exec.seq e1 e2
    rw [show 1 + (2 * Ts.length + 1) = 2 * Ts.length + 2 by omega] at this
    exact this
  · intro x h1 h2 h3 h4; rw [fr2 x h1 h2 h4, q1 x h3]
  · intro i hi; rw [cells2 i hi, q1 _ (hTs _ (List.getElem_mem hi)).2.2.2]
  · rw [fr2 VAL (by addr') (by addr') (by addr'), hm1, Mem.write_same]

/-! ### The tag parser -/

/-- `tagP`: read one bit and dispatch. -/
def tagM (c₀ c₁ : Cmd) : Cmd :=
  .ite (.lt POS N) (.seq readBitM (.seq (add POS POS ONE) (.ite (.eq BIT ZERO) c₀ c₁))) (setc OK 0)

theorem tagM_pspec {α : Type} {f₀ f₁ : List Bool → Option (α × List Bool)} {rep : Rep α}
    {c₀ c₁ : Cmd} {W₀ W₁ : List ℕ} {S₀ d₀ S₁ d₁ : ℕ} {Pre : ℕ → Mem → Prop}
    (hPre : ∀ lo m v w u, Pre lo m → Pre lo (((m.write PTR v).write BIT w).write POS u))
    (h₀ : ParserSpecL Pre c₀ f₀ rep W₀ S₀ d₀) (h₁ : ParserSpecL Pre c₁ f₁ rep W₁ S₁ d₁) :
    ParserSpecL Pre (tagM c₀ c₁) (tagP f₀ f₁) rep (PTR :: BIT :: POS :: OK :: (W₀ ++ W₁))
      (S₀ + S₁ + 10) (max d₀ d₁) := by
  intro m bs p lo hs hlo1 hlo2 hpre hp hpN
  obtain ⟨X, hX⟩ : ∃ X, X = bs.length - p + 1 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  have h10 : 10 ≤ (S₀ + S₁ + 10) * X ^ max d₀ d₁ := by
    have h2 : 1 ≤ X ^ max d₀ d₁ := Nat.one_le_pow _ _ hX1
    nlinarith
  by_cases hlt : p < bs.length
  · have hc : (Cond.lt POS N).eval m = true := by simp [Cond.eval, hp, hs.n, hlt]
    have e1 := readBitM_spec hs hp hlt
    obtain ⟨m1, hm1⟩ : ∃ m1, m1 = (m.write PTR (IN + 1 + p)).write BIT (bitv bs[p]) := ⟨_, rfl⟩
    rw [← hm1] at e1
    have q1 : ∀ x, x ≠ PTR → x ≠ BIT → m1 x = m x := fun x h1 h2 => by
      rw [hm1, Mem.write_ne _ _ h2, Mem.write_ne _ _ h1]
    obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write POS (p + 1) := ⟨_, rfl⟩
    have e2 : Cmd.Exec (add POS POS ONE) m1 m2 1 := by
      have := Exec.add POS POS ONE m1
      rw [q1 POS (by addr') (by addr'), q1 ONE (by addr') (by addr'), hp, hs.one] at this
      rw [hm2]; exact this
    have q2 : ∀ x, x ≠ PTR → x ≠ BIT → x ≠ POS → m2 x = m x := fun x h1 h2 h3 => by
      rw [hm2, Mem.write_ne _ _ h3, q1 x h1 h2]
    have hs2 : PState m2 bs := hs.of_pres (W := [PTR, BIT, POS]) (fun x _ hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        exact q2 x hx.1 hx.2.1 hx.2.2) (by decide)
    have hpre2 : Pre lo m2 := by rw [hm2, hm1]; exact hPre lo m _ _ _ hpre
    have hpos2 : m2 POS = p + 1 := by rw [hm2, Mem.write_same]
    have hhp2 : m2 HP = m HP := q2 HP (by addr') (by addr') (by addr')
    have m2BIT : m2 BIT = bitv bs[p] := by rw [hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
    have m2ZERO : m2 ZERO = 0 := by rw [q2 ZERO (by addr') (by addr') (by addr'), hs.zero]
    have hdrop : bs.drop p = bs[p] :: bs.drop (p + 1) := List.drop_eq_getElem_cons hlt
    have hX' : bs.length - (p + 1) + 1 ≤ X := by omega
    cases hb : bs[p] with
    | false =>
        rw [hb] at m2BIT
        have hc2 : (Cond.eq BIT ZERO).eval m2 = true := by simp [Cond.eval, m2BIT, m2ZERO]
        obtain ⟨m3, k3, e3, hk3, pres3, hs3, hhp3, res3⟩ := h₀ m2 bs (p + 1) lo hs2 hlo1
          (by rw [hhp2]; exact hlo2) hpre2 hpos2 (by omega)
        refine ⟨m3, _, Cmd.Exec.ite_true hc (Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc2 e3))),
          ?_, ?_, hs3, by rw [hhp2] at hhp3; exact hhp3, ?_⟩
        · rw [← hX]
          have c3 : k3 ≤ S₀ * X ^ max d₀ d₁ := le_trans hk3 (Nat.mul_le_mul_left _
            (le_trans (Nat.pow_le_pow_left hX' d₀) (Nat.pow_le_pow_right hX1 (le_max_left _ _))))
          have h3 : (S₀ + S₁ + 10) * X ^ max d₀ d₁ = S₀ * X ^ max d₀ d₁ + (S₁ + 10) * X ^ max d₀ d₁ := by ring
          have h4 : 10 ≤ (S₁ + 10) * X ^ max d₀ d₁ := by
            have h2 : 1 ≤ X ^ max d₀ d₁ := Nat.one_le_pow _ _ hX1
            nlinarith
          omega
        · intro x hx hxV
          simp only [List.mem_cons, List.mem_append, not_or] at hxV
          rw [pres3 x (by rw [hhp2]; exact hx) (by
            simp only [List.mem_cons, List.mem_append, not_or]; exact ⟨hxV.1, hxV.2.2.2.2.2.1⟩),
            q2 x hxV.2.1 hxV.2.2.1 hxV.2.2.2.1]
        · unfold PResultL at res3 ⊢
          rw [hdrop, hb]
          exact res3
    | true =>
        rw [hb] at m2BIT
        have hc2 : (Cond.eq BIT ZERO).eval m2 = false := by simp [Cond.eval, m2BIT, m2ZERO]
        obtain ⟨m3, k3, e3, hk3, pres3, hs3, hhp3, res3⟩ := h₁ m2 bs (p + 1) lo hs2 hlo1
          (by rw [hhp2]; exact hlo2) hpre2 hpos2 (by omega)
        refine ⟨m3, _, Cmd.Exec.ite_true hc (Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_false hc2 e3))),
          ?_, ?_, hs3, by rw [hhp2] at hhp3; exact hhp3, ?_⟩
        · rw [← hX]
          have c3 : k3 ≤ S₁ * X ^ max d₀ d₁ := le_trans hk3 (Nat.mul_le_mul_left _
            (le_trans (Nat.pow_le_pow_left hX' d₁) (Nat.pow_le_pow_right hX1 (le_max_right _ _))))
          have h3 : (S₀ + S₁ + 10) * X ^ max d₀ d₁ = S₁ * X ^ max d₀ d₁ + (S₀ + 10) * X ^ max d₀ d₁ := by ring
          have h4 : 10 ≤ (S₀ + 10) * X ^ max d₀ d₁ := by
            have h2 : 1 ≤ X ^ max d₀ d₁ := Nat.one_le_pow _ _ hX1
            nlinarith
          omega
        · intro x hx hxV
          simp only [List.mem_cons, List.mem_append, not_or] at hxV
          rw [pres3 x (by rw [hhp2]; exact hx) (by
            simp only [List.mem_cons, List.mem_append, not_or]; exact ⟨hxV.1, hxV.2.2.2.2.2.2⟩),
            q2 x hxV.2.1 hxV.2.2.1 hxV.2.2.2.1]
        · unfold PResultL at res3 ⊢
          rw [hdrop, hb]
          exact res3
  · have hc : (Cond.lt POS N).eval m = false := by simp [Cond.eval, hp, hs.n, hlt]
    have hp' : p = bs.length := by omega
    refine ⟨m.write OK 0, _, Cmd.Exec.ite_false hc (Exec.setc _ _ _), by rw [← hX]; omega, ?_, ?_,
      by rw [Mem.write_ne _ _ (by addr')], ?_⟩
    · intro x _ hx
      simp only [List.mem_cons, not_or] at hx
      exact Mem.write_ne _ _ hx.2.2.2.2.1
    · exact hs.of_pres' (pres_write _ _ _ _) (by intro x hx; simp at hx; subst hx; constructor <;> addr')
    · unfold PResultL
      rw [hp', List.drop_length]
      simp only [tagP, Mem.write_same]


/-! ### Representations of instances -/

/-- Instance record: `[sources, symbols, nodes, x, y, t, tests]` (lists as pointers). -/
def RepInstance : Rep Instance := fun m lo hi v γ =>
  lo ≤ v ∧ v + 7 ≤ hi ∧ RepListOf RepNat m lo hi (m v) γ.sources ∧
  RepListOf RepPair m lo hi (m (v + 1)) γ.symbols ∧ RepListOf RepNode m lo hi (m (v + 2)) γ.nodes ∧
  m (v + 3) = γ.x ∧ m (v + 4) = γ.y ∧ m (v + 5) = γ.t ∧ RepListOf RepPair m lo hi (m (v + 6)) γ.tests

/-- `GInstance` record: `[base, outs]`. -/
def RepG : Rep GInstance := fun m lo hi v g =>
  lo ≤ v ∧ v + 2 ≤ hi ∧ RepInstance m lo hi (m v) g.base ∧ RepListOf RepNat m lo hi (m (v + 1)) g.outs

/-- The parsed input `(k, g)`: `[k, g]`. -/
def RepKG : Rep (ℕ × GInstance) := fun m lo hi v kg =>
  lo ≤ v ∧ v + 2 ≤ hi ∧ m v = kg.1 ∧ RepG m lo hi (m (v + 1)) kg.2

theorem goodRep_instance : GoodRep RepInstance := by
  have hn := goodRep_listOf goodRep_nat
  have hp := goodRep_listOf goodRep_pair
  have hd := goodRep_listOf goodRep_node
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v γ h hf
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf v h1 (by omega)]; exact hn.frame m m' lo hi _ _ h3 hf
    · rw [hf (v + 1) (by omega) (by omega)]; exact hp.frame m m' lo hi _ _ h4 hf
    · rw [hf (v + 2) (by omega) (by omega)]; exact hd.frame m m' lo hi _ _ h5 hf
    · rw [hf (v + 3) (by omega) (by omega)]; exact h6
    · rw [hf (v + 4) (by omega) (by omega)]; exact h7
    · rw [hf (v + 5) (by omega) (by omega)]; exact h8
    · rw [hf (v + 6) (by omega) (by omega)]; exact hp.frame m m' lo hi _ _ h9 hf
  · intro m lo hi lo' hi' v γ h h1 h2
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
    exact ⟨by omega, by omega, hn.mono m lo hi lo' hi' _ _ g3 h1 h2, hp.mono m lo hi lo' hi' _ _ g4 h1 h2,
      hd.mono m lo hi lo' hi' _ _ g5 h1 h2, g6, g7, g8, hp.mono m lo hi lo' hi' _ _ g9 h1 h2⟩

theorem goodRep_G : GoodRep RepG := by
  have hn := goodRep_listOf goodRep_nat
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v g h hf
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [hf v h1 (by omega)]; exact goodRep_instance.frame m m' lo hi _ _ h3 hf
    · rw [hf (v + 1) (by omega) (by omega)]; exact hn.frame m m' lo hi _ _ h4 hf
  · intro m lo hi lo' hi' v g h h1 h2
    obtain ⟨g1, g2, g3, g4⟩ := h
    exact ⟨by omega, by omega, goodRep_instance.mono m lo hi lo' hi' _ _ g3 h1 h2,
      hn.mono m lo hi lo' hi' _ _ g4 h1 h2⟩

theorem goodRep_KG : GoodRep RepKG := by
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v kg h hf
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, by rw [hf v h1 (by omega)]; exact h3, ?_⟩
    rw [hf (v + 1) (by omega) (by omega)]; exact goodRep_G.frame m m' lo hi _ _ h4 hf
  · intro m lo hi lo' hi' v kg h h1 h2
    obtain ⟨g1, g2, g3, g4⟩ := h
    exact ⟨by omega, by omega, g3, goodRep_G.mono m lo hi lo' hi' _ _ g4 h1 h2⟩

/-! ### Temporaries -/

def T1 : ℕ := 30
def T2 : ℕ := 31
def T3 : ℕ := 32
def T4 : ℕ := 33
def T5 : ℕ := 34
def T6 : ℕ := 35
def T7 : ℕ := 36
/-- Temporaries of the pair and node parsers. -/
def TP1 : ℕ := 37
def TP2 : ℕ := 38
/-- Temporaries of the `GInstance` parser. -/
def TG1 : ℕ := 18
def TG2 : ℕ := 19
/-- Temporaries of the input parser. -/
def TK1 : ℕ := 28
def TK2 : ℕ := 29

/-! ### Record allocation as a parser step -/

theorem PState.hp' {m : Mem} {bs : List Bool} (h : PState m bs) : IN ≤ m HP := by
  have := h.hp; omega

theorem goodVars_of_decide (W : List ℕ) (h : W.all (fun x => decide (5 ≤ x ∧ x < IN)) = true) :
    GoodVars W := by
  intro x hx
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h x hx)

theorem goodVars_cons {x : ℕ} {W : List ℕ} (hx : 5 ≤ x ∧ x < IN) (hW : GoodVars W) :
    GoodVars (x :: W) := by
  intro y hy; simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hW y hy

theorem goodVars_append {W₁ W₂ : List ℕ} (h₁ : GoodVars W₁) (h₂ : GoodVars W₂) :
    GoodVars (W₁ ++ W₂) := by
  intro y hy; simp only [List.mem_append] at hy
  rcases hy with hy | hy
  · exact h₁ y hy
  · exact h₂ y hy

/-- The generic shape of a record allocation step, as a `ParserSpecL` for `pureP v`: from a
state in which `Pre lo m` holds, `recM Ts` produces `rep` of `v` at `[lo, m' HP)`. -/
theorem recM_pspec {α : Type} (Ts : List ℕ) (hTs : ∀ T, T ∈ Ts → T < IN ∧ T ≠ HP ∧ T ≠ OK ∧ T ≠ VAL)
    (Pre : ℕ → Mem → Prop) (rep : Rep α) (v : α)
    (hrep : ∀ lo m m' bs, PState m bs → Pre lo m → IN ≤ lo → lo ≤ m HP →
      m' HP = m HP + Ts.length →
      (∀ x, x ≠ HP → x ≠ OK → x ≠ VAL → ¬ (m HP ≤ x ∧ x < m HP + Ts.length) → m' x = m x) →
      (∀ i, (h : i < Ts.length) → m' (m HP + i) = m Ts[i]) → rep m' lo (m' HP) (m HP) v) :
    ParserSpecL Pre (recM Ts) (pureP v) rep [VAL, OK] (2 * Ts.length + 2) 0 := by
  intro m bs p lo hs hlo1 hlo2 hpre hp hpN
  obtain ⟨m', e, hhp, fr, cells, hok, hval⟩ := recM_spec Ts hTs m hs.one hs.hp'
  have pres : Pres m m' (m HP) (HP :: [VAL, OK]) := by
    intro x hx hxV
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
    exact fr x hxV.1 hxV.2.2 hxV.2.1 (by omega)
  refine ⟨m', _, e, by simp, pres, hs.of_agree pres (goodVars_of_decide _ (by decide)) (by omega), by omega, ?_⟩
  unfold PResultL
  simp only [pureP]
  refine ⟨hok, by rw [hval]; exact hrep lo m m' bs hs hpre hlo1 hlo2 hhp fr cells, ?_⟩
  rw [fr POS (by addr') (by addr') (by addr') (by have := hs.hp; addr'), hp, List.length_drop]
  omega


/-- A held value survives a record allocation and is then represented in `[lo, m' HP)`. -/
theorem Holds.after {α : Type} {rep : Rep α} (hr : GoodRep rep) {T : ℕ} {a : α} {lo : ℕ} {m m' : Mem}
    (h : Holds rep T a lo m) (hhp : m HP ≤ m' HP) (fr : ∀ x, lo ≤ x → x < m HP → m' x = m x) :
    rep m' lo (m' HP) (m T) a := by
  obtain ⟨hlo, hi, h1, h2, h3⟩ := h
  exact hr.mono m' lo hi lo (m' HP) _ _
    (hr.frame m m' lo hi _ _ h3 (fun x hx1 hx2 => fr x hx1 (by omega))) le_rfl (le_trans h2 hhp)

theorem ParserSpecL.toSpec {α : Type} {c : Cmd} {f : List Bool → Option (α × List Bool)}
    {rep : Rep α} {W : List ℕ} {S d : ℕ} (h : ParserSpecL (fun _ _ => True) c f rep W S d) :
    ParserSpec c f rep W S d := by
  intro m bs p hs hp hpN
  obtain ⟨m', k, e, hk, pres, hs', hhp, res⟩ := h m bs p (m HP) hs hs.hp' le_rfl trivial hp hpN
  exact ⟨m', k, e, hk, pres, hs', hhp, res⟩

theorem repArr_of_listOf_nat {m : Mem} {lo hi v : ℕ} {l : List ℕ}
    (h : RepListOf RepNat m lo hi v l) : RepArr m lo hi v l := h

/-! ### Suffix facts -/

theorem suffix_decodePair : SuffixP decodePair :=
  suffix_bind suffix_decodeNat (fun _ => suffix_bind suffix_decodeNat (fun _ => suffix_pure _))

theorem suffix_decodeNode : SuffixP decodeNode :=
  suffix_tagP (suffix_bind suffix_decodeNat (fun _ => suffix_pure _))
    (suffix_bind suffix_decodeNat (fun _ => suffix_bind (suffix_decodeList suffix_decodeNat)
      (fun _ => suffix_pure _)))

/-! ### The pair parser -/

def decodePairM : Cmd := seqP TP1 decodeNatM (seqP TP2 decodeNatM (recM [TP1, TP2]))

theorem recPair_pspec (a b : ℕ) :
    ParserSpecL (fun lo m => (True ∧ Holds RepNat TP1 a lo m) ∧ Holds RepNat TP2 b lo m)
      (recM [TP1, TP2]) (pureP (a, b)) RepPair [VAL, OK] (2 * [TP1, TP2].length + 2) 0 :=
  recM_pspec [TP1, TP2] (by decide) _ RepPair (a, b) (by
    intro lo m m' bs _ ⟨⟨_, ha⟩, hb⟩ hlo1 hlo2 hhp fr cells
    obtain ⟨_, _, _, _, ha'⟩ := ha
    obtain ⟨_, _, _, _, hb'⟩ := hb
    refine ⟨hlo2, by rw [hhp]; simp, ?_, ?_⟩
    · have := cells 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at this
      rw [this]; exact ha'
    · have := cells 1 (by simp); simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this
      rw [this]; exact hb')

theorem decodePairM_pspec :
    ParserSpecL (fun _ _ => True) decodePairM decodePair RepPair
      (TP1 :: (natVars ++ TP2 :: (natVars ++ [VAL, OK])))
      (50 + (50 + (2 * [TP1, TP2].length + 2) + 5) + 5) (max 1 (max 1 0)) := by
  unfold decodePairM decodePair
  apply seqP_pspec goodRep_nat suffix_decodeNat TP1 (by decide) (by decide) (by decide) natVars_good
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (decodeNatM_pspec.toL goodRep_nat _)
  intro a
  apply seqP_pspec goodRep_nat suffix_decodeNat TP2 (by decide) (by decide) (by decide) natVars_good
    ?_ ?_ (decodeNatM_pspec.toL goodRep_nat _)
  · intro b; exact recPair_pspec a b
  · intro lo m m' ⟨_, h⟩ hp hhp
    exact ⟨trivial, h.of_pres_good goodRep_nat hp hhp natVars_good (by decide) (by decide) (by decide)⟩
  · intro lo m v ⟨_, h⟩
    exact ⟨trivial, h.write goodRep_nat _ _ (by decide) (by decide) (by decide)⟩

/-- The variables of the pair parser. -/
def Wpair : List ℕ := TP1 :: (natVars ++ TP2 :: (natVars ++ [VAL, OK]))

theorem decodePairM_spec : ParserSpec decodePairM decodePair RepPair Wpair 120 1 :=
  (decodePairM_pspec.mono (fun _ _ h => h) (fun x hx => hx) (by decide) (by decide)).toSpec

theorem Wpair_good : GoodVars Wpair := goodVars_of_decide _ (by decide)

/-! ### The node parser -/

def decodeSrcM : Cmd := seqP TP1 decodeNatM (recM [ZERO, TP1])
def decodeAppM : Cmd :=
  seqP TP1 decodeNatM (seqP TP2 (decodeListM 0 decodeNatM) (recM [ONE, TP1, TP2]))
def decodeNodeM : Cmd := tagM decodeSrcM decodeAppM

/-- The variables of the natural-number list parser (level `l`). -/
def WlistNat (l : ℕ) : List ℕ := natVars ++ natVars ++ [A_ l, NEL l, JJ l, CC l]

theorem decodeListNatM_spec (l : ℕ) (hl : l ≤ 1) :
    ParserSpec (decodeListM l decodeNatM) (decodeList decodeNat) (RepListOf RepNat) (WlistNat l)
      250 2 :=
  decodeListM_pspec goodRep_nat decodeNatM_pspec progress_decodeNat suffix_decodeNat natVars_good l hl
    (by simp [natVars, A_, NEL, JJ, CC, POS, OK, VAL, TMP, CNT, POW, PTR, LAST, BIT, J, CONT]; omega)

theorem WlistNat_good (l : ℕ) (hl : l ≤ 1) : GoodVars (WlistNat l) := by
  intro x hx
  simp only [WlistNat, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (h | h) | rfl | rfl | rfl | rfl
  · exact natVars_good x h
  · exact natVars_good x h
  all_goals constructor <;> addr'

theorem recSrc_pspec (i : ℕ) :
    ParserSpecL (fun lo m => True ∧ Holds RepNat TP1 i lo m) (recM [ZERO, TP1])
      (pureP (Node.src i)) RepNode [VAL, OK] (2 * [ZERO, TP1].length + 2) 0 :=
  recM_pspec [ZERO, TP1] (by decide) _ RepNode (Node.src i) (by
    intro lo m m' bs hs ⟨_, ha⟩ hlo1 hlo2 hhp fr cells
    obtain ⟨_, _, _, _, ha'⟩ := ha
    refine ⟨hlo2, by rw [hhp]; simp, ?_, ?_⟩
    · have := cells 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at this
      rw [this]; exact hs.zero
    · have := cells 1 (by simp); simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this
      rw [this]; exact ha')

theorem recApp_pspec (f : ℕ) (args : List ℕ) :
    ParserSpecL (fun lo m => (True ∧ Holds RepNat TP1 f lo m) ∧ Holds (RepListOf RepNat) TP2 args lo m)
      (recM [ONE, TP1, TP2]) (pureP (Node.app f args)) RepNode [VAL, OK] (2 * [ONE, TP1, TP2].length + 2) 0 :=
  recM_pspec [ONE, TP1, TP2] (by decide) _ RepNode (Node.app f args) (by
    intro lo m m' bs hs ⟨⟨_, ha⟩, hb⟩ hlo1 hlo2 hhp fr cells
    obtain ⟨_, _, _, _, ha'⟩ := ha
    refine ⟨hlo2, by rw [hhp]; simp, ?_, ?_, ?_⟩
    · have := cells 0 (by simp); simp only [Nat.add_zero, List.getElem_cons_zero] at this
      rw [this]; exact hs.one
    · have := cells 1 (by simp); simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this
      rw [this]; exact ha'
    · have := cells 2 (by simp); simp only [List.getElem_cons_succ, List.getElem_cons_zero] at this
      rw [this]
      exact repArr_of_listOf_nat (hb.after (goodRep_listOf goodRep_nat) (by omega)
        (fun x hx1 hx2 => fr x (by addr') (by addr') (by addr') (by omega))))

theorem decodeSrcM_pspec :
    ParserSpecL (fun _ _ => True) decodeSrcM (bindP decodeNat (fun i => pureP (Node.src i))) RepNode
      (TP1 :: (natVars ++ [VAL, OK])) (50 + (2 * [ZERO, TP1].length + 2) + 5) (max 1 0) := by
  unfold decodeSrcM
  apply seqP_pspec goodRep_nat suffix_decodeNat TP1 (by decide) (by decide) (by decide) natVars_good
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (decodeNatM_pspec.toL goodRep_nat _)
  intro i; exact recSrc_pspec i

theorem decodeAppM_pspec :
    ParserSpecL (fun _ _ => True) decodeAppM
      (bindP decodeNat (fun f => bindP (decodeList decodeNat) (fun args => pureP (Node.app f args))))
      RepNode (TP1 :: (natVars ++ TP2 :: (WlistNat 0 ++ [VAL, OK])))
      (50 + (250 + (2 * [ONE, TP1, TP2].length + 2) + 5) + 5) (max 1 (max 2 0)) := by
  unfold decodeAppM
  apply seqP_pspec goodRep_nat suffix_decodeNat TP1 (by decide) (by decide) (by decide) natVars_good
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (decodeNatM_pspec.toL goodRep_nat _)
  intro f
  apply seqP_pspec (goodRep_listOf goodRep_nat) (suffix_decodeList suffix_decodeNat) TP2 (by decide)
    (by decide) (by decide) (WlistNat_good 0 (by norm_num)) ?_ ?_
    ((decodeListNatM_spec 0 (by norm_num)).toL (goodRep_listOf goodRep_nat) _)
  · intro args; exact recApp_pspec f args
  · intro lo m m' ⟨_, h⟩ hp hhp
    exact ⟨trivial, h.of_pres_good goodRep_nat hp hhp (WlistNat_good 0 (by norm_num)) (by decide)
      (by decide) (by decide)⟩
  · intro lo m v ⟨_, h⟩
    exact ⟨trivial, h.write goodRep_nat _ _ (by decide) (by decide) (by decide)⟩

/-- The variables of the node parser. -/
def Wnode : List ℕ :=
  PTR :: BIT :: POS :: OK :: ((TP1 :: (natVars ++ [VAL, OK])) ++ (TP1 :: (natVars ++ TP2 :: (WlistNat 0 ++ [VAL, OK]))))

theorem decodeNodeM_pspec :
    ParserSpecL (fun _ _ => True) decodeNodeM decodeNode RepNode Wnode
      ((50 + (2 * [ZERO, TP1].length + 2) + 5) + (50 + (250 + (2 * [ONE, TP1, TP2].length + 2) + 5) + 5) + 10)
      (max (max 1 0) (max 1 (max 2 0))) := by
  unfold decodeNodeM decodeNode
  exact tagM_pspec (fun _ _ _ _ _ _ => trivial) decodeSrcM_pspec decodeAppM_pspec

theorem decodeNodeM_spec : ParserSpec decodeNodeM decodeNode RepNode Wnode 400 2 :=
  (decodeNodeM_pspec.mono (fun _ _ h => h) (fun x hx => hx) (by decide) (by decide)).toSpec

theorem Wnode_good : GoodVars Wnode := goodVars_of_decide _ (by decide)


/-! ### Stability of the accumulated preconditions -/

theorem PreH.stable {Pre : ℕ → Mem → Prop} {W : List ℕ}
    (hPre : ∀ lo m m', Pre lo m → Pres m m' (m HP) (HP :: W) → m HP ≤ m' HP → Pre lo m')
    {α : Type} {rep : Rep α} (hr : GoodRep rep) {T : ℕ} {a : α} (hW : GoodVars W) (hT : T ∉ W)
    (hTIN : T < IN) (hT0 : T ≠ HP) :
    ∀ lo m m', (Pre lo m ∧ Holds rep T a lo m) → Pres m m' (m HP) (HP :: W) → m HP ≤ m' HP →
      (Pre lo m' ∧ Holds rep T a lo m') :=
  fun lo m m' ⟨h1, h2⟩ hp hhp => ⟨hPre lo m m' h1 hp hhp, h2.of_pres_good hr hp hhp hW hT hTIN hT0⟩

theorem PreH.write {Pre : ℕ → Mem → Prop} {T' : ℕ}
    (hPre : ∀ lo m v, Pre lo m → Pre lo (m.write T' v))
    {α : Type} {rep : Rep α} (hr : GoodRep rep) {T : ℕ} {a : α} (hT' : T' < IN) (hTT : T' ≠ T)
    (hT'0 : T' ≠ HP) :
    ∀ lo m v, (Pre lo m ∧ Holds rep T a lo m) → (Pre lo (m.write T' v) ∧ Holds rep T a lo (m.write T' v)) :=
  fun lo m v ⟨h1, h2⟩ => ⟨hPre lo m v h1, h2.write hr _ _ hT' hTT hT'0⟩

theorem PreT.stable (W : List ℕ) : ∀ (lo : ℕ) (m m' : Mem), True → Pres m m' (m HP) (HP :: W) → m HP ≤ m' HP → True :=
  fun _ _ _ _ _ _ => trivial

theorem PreT.write (T' : ℕ) : ∀ (lo : ℕ) (m : Mem) (v : ℕ), True → True := fun _ _ _ _ => trivial

/-! ### List parsers for pairs and nodes -/

def WlistPair (l : ℕ) : List ℕ := Wpair ++ natVars ++ [A_ l, NEL l, JJ l, CC l]
def WlistNode (l : ℕ) : List ℕ := Wnode ++ natVars ++ [A_ l, NEL l, JJ l, CC l]

theorem decodeListPairM_spec :
    ParserSpec (decodeListM 0 decodePairM) (decodeList decodePair) (RepListOf RepPair) (WlistPair 0)
      320 2 :=
  decodeListM_pspec goodRep_pair decodePairM_spec progress_decodePair suffix_decodePair Wpair_good 0
    (by norm_num) (by decide)

theorem decodeListNodeM_spec :
    ParserSpec (decodeListM 1 decodeNodeM) (decodeList decodeNode) (RepListOf RepNode) (WlistNode 1)
      600 3 :=
  decodeListM_pspec goodRep_node decodeNodeM_spec progress_decodeNode suffix_decodeNode Wnode_good 1
    le_rfl (by decide)

theorem WlistPair_good : GoodVars (WlistPair 0) := goodVars_of_decide _ (by decide)
theorem WlistNode_good : GoodVars (WlistNode 1) := goodVars_of_decide _ (by decide)

/-! ### The instance parser -/

def decodeInstanceM : Cmd :=
  seqP T1 (decodeListM 0 decodeNatM) (seqP T2 (decodeListM 0 decodePairM)
    (seqP T3 (decodeListM 1 decodeNodeM) (seqP T4 decodeNatM (seqP T5 decodeNatM
      (seqP T6 decodeNatM (seqP T7 (decodeListM 0 decodePairM)
        (recM [T1, T2, T3, T4, T5, T6, T7])))))))

/-- The accumulated precondition before the instance record is built. -/
def PreInst (sources : List ℕ) (symbols : List (ℕ × ℕ)) (nodes : List Node) (x y t : ℕ)
    (tests : List (ℕ × ℕ)) (lo : ℕ) (m : Mem) : Prop :=
  ((((((True ∧ Holds (RepListOf RepNat) T1 sources lo m) ∧ Holds (RepListOf RepPair) T2 symbols lo m) ∧
    Holds (RepListOf RepNode) T3 nodes lo m) ∧ Holds RepNat T4 x lo m) ∧ Holds RepNat T5 y lo m) ∧
    Holds RepNat T6 t lo m) ∧ Holds (RepListOf RepPair) T7 tests lo m

theorem recInst_pspec (sources : List ℕ) (symbols : List (ℕ × ℕ)) (nodes : List Node) (x y t : ℕ)
    (tests : List (ℕ × ℕ)) :
    ParserSpecL (PreInst sources symbols nodes x y t tests) (recM [T1, T2, T3, T4, T5, T6, T7])
      (pureP (⟨sources, symbols, nodes, x, y, t, tests⟩ : Instance)) RepInstance [VAL, OK]
      (2 * [T1, T2, T3, T4, T5, T6, T7].length + 2) 0 :=
  recM_pspec [T1, T2, T3, T4, T5, T6, T7] (by decide) _ RepInstance _ (by
    intro lo m m' bs hs hpre hlo1 hlo2 hhp fr cells
    unfold PreInst at hpre
    obtain ⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hpre
    have hfr : ∀ x, lo ≤ x → x < m HP → m' x = m x := fun x hx1 hx2 =>
      fr x (by addr') (by addr') (by addr') (by omega)
    have c0 := cells 0 (by simp); have c1 := cells 1 (by simp); have c2 := cells 2 (by simp)
    have c3 := cells 3 (by simp); have c4 := cells 4 (by simp); have c5 := cells 5 (by simp)
    have c6 := cells 6 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at c0 c1 c2 c3 c4 c5 c6
    obtain ⟨_, _, _, _, h4'⟩ := h4
    obtain ⟨_, _, _, _, h5'⟩ := h5
    obtain ⟨_, _, _, _, h6'⟩ := h6
    refine ⟨hlo2, by rw [hhp]; simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [c0]; exact h1.after (goodRep_listOf goodRep_nat) (by omega) hfr
    · rw [c1]; exact h2.after (goodRep_listOf goodRep_pair) (by omega) hfr
    · rw [c2]; exact h3.after (goodRep_listOf goodRep_node) (by omega) hfr
    · rw [c3]; exact h4'
    · rw [c4]; exact h5'
    · rw [c5]; exact h6'
    · rw [c6]; exact h7.after (goodRep_listOf goodRep_pair) (by omega) hfr)

/-- The variables of the instance parser. -/
def Winst : List ℕ :=
  T1 :: (WlistNat 0 ++ T2 :: (WlistPair 0 ++ T3 :: (WlistNode 1 ++ T4 :: (natVars ++ T5 :: (natVars ++
    T6 :: (natVars ++ T7 :: (WlistPair 0 ++ [VAL, OK])))))))

theorem decodeInstanceM_pspec :
    ParserSpecL (fun _ _ => True) decodeInstanceM decodeInstance RepInstance Winst
      (250 + (320 + (600 + (50 + (50 + (50 + (320 + (2 * [T1, T2, T3, T4, T5, T6, T7].length + 2) + 5) + 5) + 5) + 5) + 5) + 5) + 5)
      (max 2 (max 2 (max 3 (max 1 (max 1 (max 1 (max 2 0))))))) := by
  unfold decodeInstanceM decodeInstance
  have gn := goodRep_listOf goodRep_nat
  have gp := goodRep_listOf goodRep_pair
  have gd := goodRep_listOf goodRep_node
  have sn := suffix_decodeList suffix_decodeNat
  have sp := suffix_decodeList suffix_decodePair
  have sd := suffix_decodeList suffix_decodeNode
  have wn := WlistNat_good 0 (by norm_num)
  apply seqP_pspec gn sn T1 (by decide) (by decide) (by decide) wn (PreT.stable (WlistNat 0)) (PreT.write T1)
    ((decodeListNatM_spec 0 (by norm_num)).toL gn _)
  intro sources
  apply seqP_pspec gp sp T2 (by decide) (by decide) (by decide) WlistPair_good
    (PreH.stable (PreT.stable (WlistPair 0)) gn WlistPair_good (by decide) (by decide) (by decide))
    (PreH.write (PreT.write T2) gn (by decide) (by decide) (by decide))
    (decodeListPairM_spec.toL gp _)
  intro symbols
  apply seqP_pspec gd sd T3 (by decide) (by decide) (by decide) WlistNode_good
    (PreH.stable (PreH.stable (PreT.stable (WlistNode 1)) gn WlistNode_good (by decide) (by decide) (by decide))
      gp WlistNode_good (by decide) (by decide) (by decide))
    (PreH.write (PreH.write (PreT.write T3) gn (by decide) (by decide) (by decide)) gp (by decide)
      (by decide) (by decide))
    (decodeListNodeM_spec.toL gd _)
  intro nodes
  apply seqP_pspec goodRep_nat suffix_decodeNat T4 (by decide) (by decide) (by decide) natVars_good
    (PreH.stable (PreH.stable (PreH.stable (PreT.stable (natVars)) gn natVars_good (by decide) (by decide)
      (by decide)) gp natVars_good (by decide) (by decide) (by decide)) gd natVars_good (by decide)
      (by decide) (by decide))
    (PreH.write (PreH.write (PreH.write (PreT.write T4) gn (by decide) (by decide) (by decide)) gp
      (by decide) (by decide) (by decide)) gd (by decide) (by decide) (by decide))
    (decodeNatM_pspec.toL goodRep_nat _)
  intro x
  apply seqP_pspec goodRep_nat suffix_decodeNat T5 (by decide) (by decide) (by decide) natVars_good
    (PreH.stable (PreH.stable (PreH.stable (PreH.stable (PreT.stable (natVars)) gn natVars_good (by decide)
      (by decide) (by decide)) gp natVars_good (by decide) (by decide) (by decide)) gd natVars_good
      (by decide) (by decide) (by decide)) goodRep_nat natVars_good (by decide) (by decide) (by decide))
    (PreH.write (PreH.write (PreH.write (PreH.write (PreT.write T5) gn (by decide) (by decide)
      (by decide)) gp (by decide) (by decide) (by decide)) gd (by decide) (by decide) (by decide))
      goodRep_nat (by decide) (by decide) (by decide))
    (decodeNatM_pspec.toL goodRep_nat _)
  intro y
  apply seqP_pspec goodRep_nat suffix_decodeNat T6 (by decide) (by decide) (by decide) natVars_good
    (PreH.stable (PreH.stable (PreH.stable (PreH.stable (PreH.stable (PreT.stable (natVars)) gn natVars_good
      (by decide) (by decide) (by decide)) gp natVars_good (by decide) (by decide) (by decide)) gd
      natVars_good (by decide) (by decide) (by decide)) goodRep_nat natVars_good (by decide) (by decide)
      (by decide)) goodRep_nat natVars_good (by decide) (by decide) (by decide))
    (PreH.write (PreH.write (PreH.write (PreH.write (PreH.write (PreT.write T6) gn (by decide)
      (by decide) (by decide)) gp (by decide) (by decide) (by decide)) gd (by decide) (by decide)
      (by decide)) goodRep_nat (by decide) (by decide) (by decide)) goodRep_nat (by decide) (by decide)
      (by decide))
    (decodeNatM_pspec.toL goodRep_nat _)
  intro t
  apply seqP_pspec gp sp T7 (by decide) (by decide) (by decide) WlistPair_good
    (PreH.stable (PreH.stable (PreH.stable (PreH.stable (PreH.stable (PreH.stable (PreT.stable (WlistPair 0)) gn
      WlistPair_good (by decide) (by decide) (by decide)) gp WlistPair_good (by decide) (by decide)
      (by decide)) gd WlistPair_good (by decide) (by decide) (by decide)) goodRep_nat WlistPair_good
      (by decide) (by decide) (by decide)) goodRep_nat WlistPair_good (by decide) (by decide)
      (by decide)) goodRep_nat WlistPair_good (by decide) (by decide) (by decide))
    (PreH.write (PreH.write (PreH.write (PreH.write (PreH.write (PreH.write (PreT.write T7) gn
      (by decide) (by decide) (by decide)) gp (by decide) (by decide) (by decide)) gd (by decide)
      (by decide) (by decide)) goodRep_nat (by decide) (by decide) (by decide)) goodRep_nat (by decide)
      (by decide) (by decide)) goodRep_nat (by decide) (by decide) (by decide))
    (decodeListPairM_spec.toL gp _)
  intro tests
  exact recInst_pspec sources symbols nodes x y t tests

theorem decodeInstanceM_spec : ParserSpec decodeInstanceM decodeInstance RepInstance Winst 1700 3 :=
  (decodeInstanceM_pspec.mono (fun _ _ h => h) (fun x hx => hx) (by decide) (by decide)).toSpec

theorem Winst_good : GoodVars Winst := goodVars_of_decide _ (by decide)


/-! ### The `GInstance` parser -/

def decodeGM : Cmd := seqP TG1 decodeInstanceM (seqP TG2 (decodeListM 0 decodeNatM) (recM [TG1, TG2]))

theorem recG_pspec (base : Instance) (outs : List ℕ) :
    ParserSpecL (fun lo m => (True ∧ Holds RepInstance TG1 base lo m) ∧ Holds (RepListOf RepNat) TG2 outs lo m)
      (recM [TG1, TG2]) (pureP (⟨base, outs⟩ : GInstance)) RepG [VAL, OK] (2 * [TG1, TG2].length + 2) 0 :=
  recM_pspec [TG1, TG2] (by decide) _ RepG _ (by
    intro lo m m' bs hs hpre hlo1 hlo2 hhp fr cells
    obtain ⟨⟨_, h1⟩, h2⟩ := hpre
    have hfr : ∀ x, lo ≤ x → x < m HP → m' x = m x := fun x hx1 hx2 =>
      fr x (by addr') (by addr') (by addr') (by omega)
    have c0 := cells 0 (by simp); have c1 := cells 1 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at c0 c1
    refine ⟨hlo2, by rw [hhp]; simp, ?_, ?_⟩
    · rw [c0]; exact h1.after goodRep_instance (by omega) hfr
    · rw [c1]; exact h2.after (goodRep_listOf goodRep_nat) (by omega) hfr)

def WG : List ℕ := TG1 :: (Winst ++ TG2 :: (WlistNat 0 ++ [VAL, OK]))

theorem decodeGM_pspec :
    ParserSpecL (fun _ _ => True) decodeGM decodeG RepG WG
      (1700 + (250 + (2 * [TG1, TG2].length + 2) + 5) + 5) (max 3 (max 2 0)) := by
  unfold decodeGM decodeG
  have gn := goodRep_listOf goodRep_nat
  have sn := suffix_decodeList suffix_decodeNat
  have wn := WlistNat_good 0 (by norm_num)
  have si : SuffixP decodeInstance := by
    unfold decodeInstance
    exact suffix_bind sn (fun _ => suffix_bind (suffix_decodeList suffix_decodePair) (fun _ =>
      suffix_bind (suffix_decodeList suffix_decodeNode) (fun _ => suffix_bind suffix_decodeNat (fun _ =>
        suffix_bind suffix_decodeNat (fun _ => suffix_bind suffix_decodeNat (fun _ =>
          suffix_bind (suffix_decodeList suffix_decodePair) (fun _ => suffix_pure _)))))))
  apply seqP_pspec goodRep_instance si TG1 (by decide) (by decide) (by decide) Winst_good
    (PreT.stable Winst) (PreT.write TG1) (decodeInstanceM_spec.toL goodRep_instance _)
  intro base
  apply seqP_pspec gn sn TG2 (by decide) (by decide) (by decide) wn
    (PreH.stable (PreT.stable (WlistNat 0)) goodRep_instance wn (by decide) (by decide) (by decide))
    (PreH.write (PreT.write TG2) goodRep_instance (by decide) (by decide) (by decide))
    ((decodeListNatM_spec 0 (by norm_num)).toL gn _)
  intro outs
  exact recG_pspec base outs

theorem suffix_decodeInstance : SuffixP decodeInstance := by
  unfold decodeInstance
  exact suffix_bind (suffix_decodeList suffix_decodeNat) (fun _ =>
    suffix_bind (suffix_decodeList suffix_decodePair) (fun _ =>
      suffix_bind (suffix_decodeList suffix_decodeNode) (fun _ => suffix_bind suffix_decodeNat (fun _ =>
        suffix_bind suffix_decodeNat (fun _ => suffix_bind suffix_decodeNat (fun _ =>
          suffix_bind (suffix_decodeList suffix_decodePair) (fun _ => suffix_pure _)))))))

theorem suffix_decodeG : SuffixP decodeG := by
  unfold decodeG
  exact suffix_bind suffix_decodeInstance (fun _ =>
    suffix_bind (suffix_decodeList suffix_decodeNat) (fun _ => suffix_pure _))

theorem decodeGM_spec : ParserSpec decodeGM decodeG RepG WG 2000 3 :=
  (decodeGM_pspec.mono (fun _ _ h => h) (fun x hx => hx) (by decide) (by decide)).toSpec

theorem WG_good : GoodVars WG :=
  goodVars_cons (by decide) (goodVars_append Winst_good (goodVars_cons (by decide)
    (goodVars_append (WlistNat_good 0 (by norm_num)) (goodVars_of_decide _ (by decide)))))

/-! ### The input parser -/

def decodePair'M : Cmd := seqP TK1 decodeNatM (seqP TK2 decodeGM (recM [TK1, TK2]))

theorem recKG_pspec (k : ℕ) (g : GInstance) :
    ParserSpecL (fun lo m => (True ∧ Holds RepNat TK1 k lo m) ∧ Holds RepG TK2 g lo m)
      (recM [TK1, TK2]) (pureP (k, g)) RepKG [VAL, OK] (2 * [TK1, TK2].length + 2) 0 :=
  recM_pspec [TK1, TK2] (by decide) _ RepKG _ (by
    intro lo m m' bs hs hpre hlo1 hlo2 hhp fr cells
    obtain ⟨⟨_, h1⟩, h2⟩ := hpre
    obtain ⟨_, _, _, _, h1'⟩ := h1
    have hfr : ∀ x, lo ≤ x → x < m HP → m' x = m x := fun x hx1 hx2 =>
      fr x (by addr') (by addr') (by addr') (by omega)
    have c0 := cells 0 (by simp); have c1 := cells 1 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at c0 c1
    refine ⟨hlo2, by rw [hhp]; simp, by rw [c0]; exact h1', ?_⟩
    rw [c1]; exact h2.after goodRep_G (by omega) hfr)

def WKG : List ℕ := TK1 :: (natVars ++ TK2 :: (WG ++ [VAL, OK]))

theorem decodePair'M_pspec :
    ParserSpecL (fun _ _ => True) decodePair'M decodePair' RepKG WKG
      (50 + (2000 + (2 * [TK1, TK2].length + 2) + 5) + 5) (max 1 (max 3 0)) := by
  unfold decodePair'M decodePair'
  apply seqP_pspec goodRep_nat suffix_decodeNat TK1 (by decide) (by decide) (by decide) natVars_good
    (PreT.stable natVars) (PreT.write TK1) (decodeNatM_pspec.toL goodRep_nat _)
  intro k
  apply seqP_pspec goodRep_G suffix_decodeG TK2 (by decide) (by decide) (by decide) WG_good
    (PreH.stable (PreT.stable WG) goodRep_nat WG_good (by decide) (by decide) (by decide))
    (PreH.write (PreT.write TK2) goodRep_nat (by decide) (by decide) (by decide))
    (decodeGM_spec.toL goodRep_G _)
  intro g
  exact recKG_pspec k g

theorem suffix_decodePair' : SuffixP decodePair' := by
  unfold decodePair'
  exact suffix_bind suffix_decodeNat (fun _ => suffix_bind suffix_decodeG (fun _ => suffix_pure _))

theorem decodePair'M_spec : ParserSpec decodePair'M decodePair' RepKG WKG 2100 3 :=
  (decodePair'M_pspec.mono (fun _ _ h => h) (fun x hx => hx) (by decide) (by decide)).toSpec

theorem WKG_good : GoodVars WKG :=
  goodVars_cons (by decide) (goodVars_append natVars_good (goodVars_cons (by decide)
    (goodVars_append WG_good (goodVars_of_decide _ (by decide)))))

/-- Parse the whole input: `decodePair'`, then require that every bit was consumed. -/
def decodeInputM : Cmd :=
  .seq decodePair'M (.ite (.eq OK ONE) (.ite (.eq POS N) nop (setc OK 0)) nop)

/-- The result of the input parser. -/
def InputResult (m m' : Mem) (bs : List Bool) : Prop :=
  match decodeInput bs with
  | none => m' OK = 0
  | some kg => m' OK = 1 ∧ RepKG m' (m HP) (m' HP) (m' VAL) kg

theorem decodeInputM_spec (m : Mem) (bs : List Bool) (hs : PState m bs) (hp : m POS = 0) :
    ∃ m' k, Cmd.Exec decodeInputM m m' k ∧ k ≤ 2100 * (bs.length + 1) ^ 3 + 5 ∧
      Pres m m' (m HP) (HP :: (OK :: WKG)) ∧ PState m' bs ∧ m HP ≤ m' HP ∧ InputResult m m' bs := by
  obtain ⟨m₁, k₁, e₁, hk₁, pres₁, hs₁, hhp₁, res₁⟩ := decodePair'M_spec m bs 0 hs hp (Nat.zero_le _)
  rw [Nat.sub_zero] at hk₁
  unfold PResult at res₁
  unfold InputResult decodeInput
  simp only [List.drop_zero] at res₁
  cases hd : decodePair' bs with
  | none =>
      rw [hd] at res₁
      have hok : (Cond.eq OK ONE).eval m₁ = false := by simp [Cond.eval, res₁, hs₁.one]
      refine ⟨m₁, _, Cmd.Exec.seq e₁ (Cmd.Exec.ite_false hok (Exec.nop m₁)), by omega,
        pres₁.mono le_rfl (fun x hx => by simp only [List.mem_cons] at hx ⊢; tauto), hs₁, hhp₁, res₁⟩
  | some q =>
      obtain ⟨kg, rest⟩ := q
      rw [hd] at res₁
      obtain ⟨hok₁, hrep₁, hpos₁⟩ := res₁
      have hok : (Cond.eq OK ONE).eval m₁ = true := by simp [Cond.eval, hok₁, hs₁.one]
      cases rest with
      | nil =>
          have hc : (Cond.eq POS N).eval m₁ = true := by
            simp [Cond.eval, hpos₁, hs₁.n]
          refine ⟨m₁, _, Cmd.Exec.seq e₁ (Cmd.Exec.ite_true hok (Cmd.Exec.ite_true hc (Exec.nop m₁))),
            by omega, pres₁.mono le_rfl (fun x hx => by simp only [List.mem_cons] at hx ⊢; tauto),
            hs₁, hhp₁, hok₁, hrep₁⟩
      | cons b rest =>
          have hlen : (b :: rest).length ≤ bs.length := by
            obtain ⟨pre, hpre⟩ := suffix_decodePair' bs kg (b :: rest) hd
            rw [hpre, List.length_append]; omega
          have hc : (Cond.eq POS N).eval m₁ = false := by
            simp only [Cond.eval, hpos₁, hs₁.n, decide_eq_false_iff_not]
            simp only [List.length_cons] at hlen ⊢
            omega
          refine ⟨m₁.write OK 0, _, Cmd.Exec.seq e₁ (Cmd.Exec.ite_true hok (Cmd.Exec.ite_false hc
            (Exec.setc _ _ _))), by omega, ?_, ?_, ?_, ?_⟩
          · intro x hx hxV
            simp only [List.mem_cons, not_or] at hxV
            rw [Mem.write_ne _ _ hxV.2.1]
            exact pres₁ x hx (by simp only [List.mem_cons, not_or]; exact ⟨hxV.1, hxV.2.2⟩)
          · exact hs₁.of_pres' (pres_write _ _ _ _) (by intro x hx; simp at hx; subst hx; constructor <;> addr')
          · rw [Mem.write_ne _ _ (by addr')]; exact hhp₁
          · simp only [Mem.write_same]

end DisequalityDispersion.Machine
