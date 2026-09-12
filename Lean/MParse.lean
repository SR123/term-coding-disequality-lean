import MachineLib
import Parsing

/-! # The parser on the machine, part 1: naturals

`decodeNatM` reads the self-delimiting code of a natural number from the input array at the
cursor `POS` exactly as `decodeNat` does (`Parsing.lean`): it counts the leading ones, skips
the zero, reads that many digits (least significant first, accumulating `VAL` with a running
power of two), and insists on canonicity (last digit set).  `decodeNatM_spec` proves that on
every input and cursor position it succeeds exactly when `decodeNat (bs.drop p)` succeeds,
returns the same value, advances the cursor to the same rest, and takes `O(|bs| - p + 1)`
steps. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Parser variables -/

def N : ℕ := 4
def INB : ℕ := 3
def ZERO : ℕ := 2
def POS : ℕ := 5
def OK : ℕ := 6
def VAL : ℕ := 7
def TMP : ℕ := 8
def CNT : ℕ := 10
def POW : ℕ := 11
def PTR : ℕ := 12
def LAST : ℕ := 13
def BIT : ℕ := 14
def J : ℕ := 15
def CONT : ℕ := 16

theorem N_eq : N = 4 := rfl
theorem INB_eq : INB = 3 := rfl
theorem ZERO_eq : ZERO = 2 := rfl
theorem POS_eq : POS = 5 := rfl
theorem OK_eq : OK = 6 := rfl
theorem VAL_eq : VAL = 7 := rfl
theorem TMP_eq : TMP = 8 := rfl
theorem CNT_eq : CNT = 10 := rfl
theorem POW_eq : POW = 11 := rfl
theorem PTR_eq : PTR = 12 := rfl
theorem LAST_eq : LAST = 13 := rfl
theorem BIT_eq : BIT = 14 := rfl
theorem J_eq : J = 15 := rfl
theorem CONT_eq : CONT = 16 := rfl
theorem HP_eq' : HP = 0 := rfl
theorem ONE_eq' : ONE = 1 := rfl
theorem IN_eq' : IN = 200 := rfl

/-- The value of a bit as stored in memory. -/
def bitv (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitv_true : bitv true = 1 := rfl
@[simp] theorem bitv_false : bitv false = 0 := rfl

theorem bitv_le_one (b : Bool) : bitv b ≤ 1 := by cases b <;> simp [bitv]

/-- The standing invariant of the parser: the input array, the parser constants, and a heap
pointer above the input. -/
structure PState (m : Mem) (bs : List Bool) : Prop where
  input : Input m bs
  n : m N = bs.length
  inb : m INB = IN + 1
  one : m ONE = 1
  zero : m ZERO = 0
  hp : IN + 1 + bs.length ≤ m HP

theorem PState.bit {m : Mem} {bs : List Bool} (h : PState m bs) (i : ℕ) (hi : i < bs.length) :
    m (IN + 1 + i) = bitv bs[i] := h.input.2 i hi

/-- The parser variables. -/
def natVars : List ℕ := [POS, OK, VAL, TMP, CNT, POW, PTR, LAST, BIT, J, CONT]

theorem natVars_lt (x : ℕ) (h : x ∈ natVars) : x < IN := by
  simp [natVars, IN, POS, OK, VAL, TMP, CNT, POW, PTR, LAST, BIT, J, CONT] at h ⊢
  omega

theorem PState.var_lt {m : Mem} {bs : List Bool} (h : PState m bs) (x : ℕ) (hx : x < IN) :
    x < m HP := by
  have := h.hp
  omega

theorem PState.of_pres {m m' : Mem} {bs : List Bool} (h : PState m bs) {W : List ℕ}
    (hp : Pres m m' (m HP) W) (hW : ∀ x, x ∈ W → x ∈ natVars) : PState m' bs := by
  have hlt : ∀ x, x ∈ W → x < IN := fun x hx => natVars_lt x (hW x hx)
  have hn : ∀ x, x ∈ W → x ≤ 4 → False := by
    intro x hx h4; have := hW x hx
    simp [natVars, POS, OK, VAL, TMP, CNT, POW, PTR, LAST, BIT, J, CONT] at this; omega
  refine ⟨h.input.of_pres hp h.hp hlt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp N (h.var_lt N (by decide)) (fun hm => hn N hm (by decide)), h.n]
  · rw [hp INB (h.var_lt INB (by decide)) (fun hm => hn INB hm (by decide)), h.inb]
  · rw [hp ONE (h.var_lt ONE (by decide)) (fun hm => hn ONE hm (by decide)), h.one]
  · rw [hp ZERO (h.var_lt ZERO (by decide)) (fun hm => hn ZERO hm (by decide)), h.zero]
  · rw [hp HP (h.var_lt HP (by decide)) (fun hm => hn HP hm (by decide))]
    exact h.hp

/-! ### Pure facts about the decoders -/

theorem readBits_of_le (c : ℕ) (l : List Bool) (h : c ≤ l.length) :
    readBits c l = some (l.take c, l.drop c) := by
  have := readBits_append (l.take c) (l.drop c)
  rw [List.take_append_drop] at this
  rwa [List.length_take, Nat.min_eq_left h] at this

theorem readBits_none : ∀ (c : ℕ) (l : List Bool), l.length < c → readBits c l = none
  | 0, l, h => absurd h (Nat.not_lt_zero _)
  | c + 1, [], _ => by simp [readBits]
  | c + 1, b :: l, h => by
      simp only [readBits]
      rw [readBits_none c l (by simp at h; omega)]

/-- Little-endian accumulation of a prefix. -/
theorem fromBits_take_succ : ∀ (j : ℕ) (l : List Bool) (h : j < l.length),
    fromBits (l.take (j + 1)) = fromBits (l.take j) + 2 ^ j * bitv (l[j]'h)
  | 0, [], h => absurd h (Nat.not_lt_zero _)
  | 0, a :: l, _ => by
      simp [fromBits, Nat.bit_val, bitv]
      cases a <;> simp
  | j + 1, [], h => absurd h (Nat.not_lt_zero _)
  | j + 1, a :: l, h => by
      have hj : j < l.length := by simp at h; omega
      have ih := fromBits_take_succ j l hj
      simp only [List.take_succ_cons, fromBits_cons, Nat.bit_val, List.getElem_cons_succ]
      rw [ih, pow_succ]
      cases a <;> cases hl : l[j]'hj <;> simp [bitv] <;> ring

theorem canon_take (c : ℕ) (l : List Bool) (hc : c ≤ l.length) :
    Canon (l.take c) = (if h : 0 < c then l[c - 1] else true) := by
  cases c with
  | zero => simp [Canon]
  | succ c =>
      simp only [Canon]
      rw [List.getLast?_eq_getElem?]
      simp only [List.length_take, Nat.min_eq_left hc, Nat.add_sub_cancel]
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem (by omega)]
      simp

theorem decodeNatAux_drop_true (bs : List Bool) (c q : ℕ) (hq : q < bs.length)
    (hb : bs[q] = true) : decodeNatAux c (bs.drop q) = decodeNatAux (c + 1) (bs.drop (q + 1)) := by
  rw [List.drop_eq_getElem_cons hq, hb]
  rfl

theorem decodeNatAux_drop_false (bs : List Bool) (c q : ℕ) (hq : q < bs.length)
    (hb : bs[q] = false) : decodeNatAux c (bs.drop q) =
      (if q + 1 + c ≤ bs.length then
        (if Canon ((bs.drop (q + 1)).take c) then
          some (fromBits ((bs.drop (q + 1)).take c), bs.drop (q + 1 + c)) else none)
       else none) := by
  rw [List.drop_eq_getElem_cons hq, hb]
  simp only [decodeNatAux]
  split_ifs with h1 h2
  · rw [readBits_of_le c _ (by simp; omega), List.drop_drop]
    simp [h2]
  · rw [readBits_of_le c _ (by simp; omega)]
    simp [h2]
  · rw [readBits_none c _ (by simp; omega)]

theorem decodeNatAux_drop_end (bs : List Bool) (c : ℕ) : decodeNatAux c (bs.drop bs.length) = none := by
  rw [List.drop_length]; rfl

end DisequalityDispersion.Machine

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Smart constructors -/

def setc (a c : ℕ) : Cmd := .prim (.const a c)
def mov (a b : ℕ) : Cmd := .prim (.mov a b)
def add (a b c : ℕ) : Cmd := .prim (.add a b c)
def sub (a b c : ℕ) : Cmd := .prim (.sub a b c)
def load (a b : ℕ) : Cmd := .prim (.load a b)
def store (a b : ℕ) : Cmd := .prim (.store a b)
/-- A no-op (`ONE := ONE`). -/
def nop : Cmd := .prim (.mov ONE ONE)

theorem Exec.setc (a c : ℕ) (m : Mem) : Cmd.Exec (setc a c) m (m.write a c) 1 := Cmd.Exec.prim _ m
theorem Exec.mov (a b : ℕ) (m : Mem) : Cmd.Exec (mov a b) m (m.write a (m b)) 1 := Cmd.Exec.prim _ m
theorem Exec.add (a b c : ℕ) (m : Mem) : Cmd.Exec (add a b c) m (m.write a (m b + m c)) 1 :=
  Cmd.Exec.prim _ m
theorem Exec.sub (a b c : ℕ) (m : Mem) : Cmd.Exec (sub a b c) m (m.write a (m b - m c)) 1 :=
  Cmd.Exec.prim _ m
theorem Exec.load (a b : ℕ) (m : Mem) : Cmd.Exec (load a b) m (m.write a (m (m b))) 1 :=
  Cmd.Exec.prim _ m
theorem Exec.store (a b : ℕ) (m : Mem) : Cmd.Exec (store a b) m (m.write (m a) (m b)) 1 :=
  Cmd.Exec.prim _ m
theorem Exec.nop (m : Mem) : Cmd.Exec nop m m 1 := by
  have := Cmd.Exec.prim (.mov ONE ONE) m
  have e : (Prim.mov ONE ONE).exec m = m := by
    funext x; simp [Prim.exec, Mem.write_apply]; intro h; rw [h]
  rwa [e] at this

theorem Exec.ite_spec {b : Cond} {c₁ c₂ : Cmd} {m : Mem} {B : ℕ} {P : Mem → Prop}
    (h₁ : b.eval m = true → ∃ m' k, Cmd.Exec c₁ m m' k ∧ P m' ∧ k ≤ B)
    (h₂ : b.eval m = false → ∃ m' k, Cmd.Exec c₂ m m' k ∧ P m' ∧ k ≤ B) :
    ∃ m' k, Cmd.Exec (.ite b c₁ c₂) m m' k ∧ P m' ∧ k ≤ B + 2 := by
  cases hb : b.eval m with
  | true =>
      obtain ⟨m', k, e, hP, hk⟩ := h₁ hb
      exact ⟨m', 1 + k + 1, Cmd.Exec.ite_true hb e, hP, by omega⟩
  | false =>
      obtain ⟨m', k, e, hP, hk⟩ := h₂ hb
      exact ⟨m', 1 + 1 + k, Cmd.Exec.ite_false hb e, hP, by omega⟩

/-! ### Reading the current input bit -/

/-- `BIT := input[POS]` (via `PTR := INB + POS`). -/
def readBitM : Cmd := .seq (add PTR INB POS) (load BIT PTR)

theorem readBitM_spec {m : Mem} {bs : List Bool} (hs : PState m bs) {q : ℕ} (hq : m POS = q)
    (hqN : q < bs.length) :
    Cmd.Exec readBitM m ((m.write PTR (IN + 1 + q)).write BIT (bitv bs[q])) 2 := by
  have e1 := Exec.add PTR INB POS m
  have e2 := Exec.load BIT PTR (m.write PTR (m INB + m POS))
  rw [hs.inb, hq] at e1 e2
  have hb : (m.write PTR (IN + 1 + q)) ((m.write PTR (IN + 1 + q)) PTR) = bitv bs[q] := by
    rw [Mem.write_same]
    rw [Mem.write_ne _ _ (by simp [IN, PTR]; omega)]
    exact hs.bit q hqN
  rw [hb] at e2
  exact Cmd.Exec.seq e1 e2

/-- `CONT := if POS < N then input[POS] else 0`. -/
def contM : Cmd := .ite (.lt POS N) (.seq readBitM (mov CONT BIT)) (setc CONT 0)

def contVars : List ℕ := [PTR, BIT, CONT]

theorem contM_spec {m : Mem} {bs : List Bool} (hs : PState m bs) {q : ℕ} (hq : m POS = q) :
    ∃ m' k, Cmd.Exec contM m m' k ∧ k ≤ 5 ∧
      m' CONT = (if h : q < bs.length then bitv (bs[q]'h) else 0) ∧ Pres m m' (m HP) contVars := by
  unfold contM
  by_cases hlt : q < bs.length
  · have hb : (Cond.lt POS N).eval m = true := by simp [Cond.eval, hq, hs.n, hlt]
    have e1 := readBitM_spec hs hq hlt
    have e2 := Exec.mov CONT BIT ((m.write PTR (IN + 1 + q)).write BIT (bitv bs[q]))
    refine ⟨_, 1 + (2 + 1) + 1, Cmd.Exec.ite_true hb (Cmd.Exec.seq e1 e2), by omega, ?_, ?_⟩
    · rw [dif_pos hlt]
      simp +decide [BIT, CONT, PTR]
    · intro x _ hW
      simp [contVars] at hW
      simp [Mem.write_apply, hW]
  · have hb : (Cond.lt POS N).eval m = false := by simp [Cond.eval, hq, hs.n, hlt]
    refine ⟨_, 1 + 1 + 1, Cmd.Exec.ite_false hb (Exec.setc CONT 0 m), by omega, ?_, ?_⟩
    · rw [dif_neg hlt]
      simp
    · intro x _ hW
      simp [contVars] at hW
      simp [Mem.write_apply, hW]

end DisequalityDispersion.Machine

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Counting the leading ones -/

def countVars : List ℕ := [POS, CNT, PTR, BIT, CONT]

/-- `while CONT = 1 do CNT := CNT + 1; POS := POS + 1; CONT := …`. -/
def countLoop : Cmd :=
  .loop (.eq CONT ONE) (.seq (add CNT CNT ONE) (.seq (add POS POS ONE) contM))

/-- Invariant of the counting loop relative to the initial memory `m₀` (cursor `p`). -/
structure CountInv (m₀ : Mem) (bs : List Bool) (p : ℕ) (m : Mem) : Prop where
  st : PState m bs
  hp_le : p ≤ m POS
  pos_le : m POS ≤ bs.length
  cnt : m CNT = m POS - p
  cont : m CONT = if h : m POS < bs.length then bitv (bs[m POS]'h) else 0
  dec : decodeNatAux 0 (bs.drop p) = decodeNatAux (m CNT) (bs.drop (m POS))
  pres : Pres m₀ m (m₀ HP) countVars
  hp : m HP = m₀ HP

/-- One iteration of the counting loop. -/
theorem countBody_spec (m₀ : Mem) (bs : List Bool) (p : ℕ) (m : Mem) (hI : CountInv m₀ bs p m)
    (hb : (Cond.eq CONT ONE).eval m = true) :
    ∃ m' k, Cmd.Exec (.seq (add CNT CNT ONE) (.seq (add POS POS ONE) contM)) m m' k ∧
      CountInv m₀ bs p m' ∧ k ≤ 7 ∧ bs.length - m' POS < bs.length - m POS := by
  -- the condition says `CONT = 1`, so the current bit is a one
  have h1 : m CONT = 1 := by
    simp [Cond.eval] at hb; rw [hI.st.one] at hb; exact hb
  have hlt : m POS < bs.length := by
    by_contra hn
    have := hI.cont
    rw [dif_neg hn] at this
    omega
  have hbit : bs[m POS] = true := by
    have := hI.cont
    rw [dif_pos hlt] at this
    cases hb' : bs[m POS] <;> simp [hb', bitv] at this ⊢; omega
  -- execute the body
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write CNT (m CNT + 1) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (add CNT CNT ONE) m m1 1 := by
    have := Exec.add CNT CNT ONE m
    rwa [hI.st.one, ← hm1] at this
  have hm1one : m1 ONE = 1 := by rw [hm1, Mem.write_ne _ _ (by decide)]; exact hI.st.one
  have hm1pos : m1 POS = m POS := by rw [hm1, Mem.write_ne _ _ (by decide)]
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write POS (m POS + 1) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add POS POS ONE) m1 m2 1 := by
    have := Exec.add POS POS ONE m1
    rwa [hm1one, hm1pos, ← hm2] at this
  have hpres2 : Pres m m2 (m HP) [CNT, POS] := by
    intro x _ hW
    simp at hW
    rw [hm2, hm1, Mem.write_ne _ _ hW.2, Mem.write_ne _ _ hW.1]
  have hs2 : PState m2 bs := hI.st.of_pres hpres2 (by decide)
  have hm2pos : m2 POS = m POS + 1 := by rw [hm2, Mem.write_same]
  have hm2cnt : m2 CNT = m CNT + 1 := by
    rw [hm2, Mem.write_ne _ _ (by decide), hm1, Mem.write_same]
  have hm2hp : m2 HP = m HP := by
    rw [hm2, Mem.write_ne _ _ (by decide), hm1, Mem.write_ne _ _ (by decide)]
  obtain ⟨m3, k3, e3, hk3, hcont3, hpres3⟩ := contM_spec hs2 hm2pos
  rw [hm2hp] at hpres3
  have p3 : ∀ x, x < IN → x ∉ contVars → m3 x = m2 x := fun x hx hW =>
    hpres3 x (hI.st.var_lt x hx) hW
  have hpos3 : m3 POS = m POS + 1 := by rw [p3 POS (by decide) (by decide)]; exact hm2pos
  have hcnt3 : m3 CNT = m CNT + 1 := by rw [p3 CNT (by decide) (by decide)]; exact hm2cnt
  have hhp3 : m3 HP = m HP := by rw [p3 HP (by decide) (by decide)]; exact hm2hp
  have hpres3' : Pres m2 m3 (m2 HP) contVars := by rw [hm2hp]; exact hpres3
  have hs3 : PState m3 bs := hs2.of_pres hpres3' (by decide)
  refine ⟨m3, 1 + (1 + k3), Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), ?_, by omega, ?_⟩
  · refine ⟨hs3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpos3]; have := hI.hp_le; omega
    · rw [hpos3]; exact hlt
    · rw [hcnt3, hpos3, hI.cnt]; have := hI.hp_le; omega
    · rw [hcont3, hpos3]
    · rw [hcnt3, hpos3, hI.dec]
      exact decodeNatAux_drop_true bs (m CNT) (m POS) hlt hbit
    · have hA : Pres m m3 (m HP) ([CNT, POS] ++ contVars) := hpres2.trans hpres3 le_rfl
      have hB := hI.pres.trans hA (by rw [hI.hp])
      exact hB.mono le_rfl (by decide)
    · rw [hhp3, hI.hp]
  · rw [hpos3]; omega

theorem countLoop_spec (m₀ : Mem) (bs : List Bool) (p : ℕ) (m : Mem) (hI : CountInv m₀ bs p m) :
    ∃ m' k, Cmd.Exec countLoop m m' k ∧ CountInv m₀ bs p m' ∧
      (m' POS = bs.length ∨ ∃ h : m' POS < bs.length, bs[m' POS] = false) ∧
      k ≤ (bs.length - m POS) * 9 + 2 := by
  have main := Exec.loop_measure (.eq CONT ONE)
    (.seq (add CNT CNT ONE) (.seq (add POS POS ONE) contM))
    (CountInv m₀ bs p) (fun m => bs.length - m POS) 7
    (fun m hI hb => by
      obtain ⟨m', k, e, hI', hk, hlt⟩ := countBody_spec m₀ bs p m hI hb
      exact ⟨m', k, e, hI', hk, hlt⟩)
  obtain ⟨m', k, e, hI', hb', hk⟩ := main m hI
  refine ⟨m', k, e, hI', ?_, hk⟩
  -- the exit condition
  have hne : m' CONT ≠ 1 := by
    simp [Cond.eval] at hb'; rw [hI'.st.one] at hb'; exact hb'
  by_cases hlt : m' POS < bs.length
  · right
    refine ⟨hlt, ?_⟩
    have := hI'.cont
    rw [dif_pos hlt] at this
    cases hb'' : bs[m' POS] <;> simp [hb'', bitv] at this ⊢
    exact absurd this hne
  · left; have := hI'.pos_le; omega

end DisequalityDispersion.Machine

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Reading the digits -/

def bitVars : List ℕ := [POS, VAL, POW, PTR, LAST, BIT, J]

/-- One digit: `BIT := input[POS]; if BIT = 1 then VAL := VAL + POW; LAST := BIT;
POW := 2·POW; POS := POS + 1`. -/
def bitBody : Cmd :=
  .seq readBitM (.seq (.ite (.eq BIT ONE) (add VAL VAL POW) nop)
    (.seq (mov LAST BIT) (.seq (add POW POW POW) (add POS POS ONE))))

/-- `for J < CNT do bitBody`. -/
def bitLoop : Cmd := forLoop J CNT bitBody

/-- Invariant of the digit loop: `j` digits read from position `q1`. -/
structure BitInv (m₀ : Mem) (bs : List Bool) (q1 c : ℕ) (j : ℕ) (m : Mem) : Prop where
  st : PState m bs
  hj : j ≤ c
  hc : q1 + c ≤ bs.length
  jv : m J = j
  cnt : m CNT = c
  pos : m POS = q1 + j
  val : m VAL = fromBits ((bs.drop q1).take j)
  pow : m POW = 2 ^ j
  last : m LAST = if h : 0 < j then bitv (bs[q1 + j - 1]'(by omega)) else 1
  pres : Pres m₀ m (m₀ HP) bitVars
  hp : m HP = m₀ HP

theorem bitBody_spec (m₀ : Mem) (bs : List Bool) (q1 c j : ℕ) (m : Mem)
    (hI : BitInv m₀ bs q1 c j m) (hjc : j < c) :
    ∃ m' k, Cmd.Exec bitBody m m' k ∧ k ≤ 8 ∧ m' J = j ∧ m' ONE = 1 ∧
      BitInv m₀ bs q1 c (j + 1) (m'.write J (j + 1)) := by
  have hq : q1 + j < bs.length := by have := hI.hc; omega
  -- read the bit
  have e1 := readBitM_spec hI.st hI.pos hq
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = (m.write PTR (IN + 1 + q1 + j)).write BIT (bitv bs[q1 + j]) :=
    ⟨_, rfl⟩
  rw [show IN + 1 + (q1 + j) = IN + 1 + q1 + j by omega, ← hm1] at e1
  have m1BIT : m1 BIT = bitv bs[q1 + j] := by rw [hm1, Mem.write_same]
  have m1x : ∀ x, x ≠ BIT → x ≠ PTR → m1 x = m x := by
    intro x h1 h2; rw [hm1, Mem.write_ne _ _ h1, Mem.write_ne _ _ h2]
  -- conditional add
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write VAL (m1 VAL + 2 ^ j * bitv bs[q1 + j]) := ⟨_, rfl⟩
  have e2 : ∃ k, Cmd.Exec (.ite (.eq BIT ONE) (add VAL VAL POW) nop) m1 m2 k ∧ k ≤ 3 := by
    have hone : m1 ONE = 1 := by rw [m1x ONE (by decide) (by decide)]; exact hI.st.one
    have hpow : m1 POW = 2 ^ j := by rw [m1x POW (by decide) (by decide)]; exact hI.pow
    cases hb : bs[q1 + j] with
    | true =>
        have hc : (Cond.eq BIT ONE).eval m1 = true := by
          simp [Cond.eval, m1BIT, hb, hone]
        refine ⟨1 + 1 + 1, Cmd.Exec.ite_true hc ?_, le_rfl⟩
        have := Exec.add VAL VAL POW m1
        rw [hpow] at this
        rw [hm2, hb]
        simpa using this
    | false =>
        have hc : (Cond.eq BIT ONE).eval m1 = false := by
          simp [Cond.eval, m1BIT, hb, hone]
        refine ⟨1 + 1 + 1, Cmd.Exec.ite_false hc ?_, le_rfl⟩
        have := Exec.nop m1
        have e : m2 = m1 := by
          rw [hm2, hb]; funext x; simp [Mem.write_apply]; intro hx; rw [hx]
        rw [e]; exact this
  obtain ⟨k2, e2, hk2⟩ := e2
  have m2VAL : m2 VAL = m VAL + 2 ^ j * bitv bs[q1 + j] := by
    rw [hm2, Mem.write_same, m1x VAL (by decide) (by decide)]
  have m2x : ∀ x, x ≠ VAL → x ≠ BIT → x ≠ PTR → m2 x = m x := by
    intro x h1 h2 h3; rw [hm2, Mem.write_ne _ _ h1, m1x x h2 h3]
  have m2BIT : m2 BIT = bitv bs[q1 + j] := by rw [hm2, Mem.write_ne _ _ (by decide), m1BIT]
  -- LAST := BIT
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write LAST (bitv bs[q1 + j]) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (mov LAST BIT) m2 m3 1 := by
    have := Exec.mov LAST BIT m2; rwa [m2BIT, ← hm3] at this
  -- POW := POW + POW
  have m3POW : m3 POW = 2 ^ j := by
    rw [hm3, Mem.write_ne _ _ (by decide), m2x POW (by decide) (by decide) (by decide)]; exact hI.pow
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write POW (2 ^ (j + 1)) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add POW POW POW) m3 m4 1 := by
    have := Exec.add POW POW POW m3
    rw [m3POW, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by rw [pow_succ]; ring, ← hm4] at this
    exact this
  -- POS := POS + 1
  have m4POS : m4 POS = q1 + j := by
    rw [hm4, Mem.write_ne _ _ (by decide), hm3, Mem.write_ne _ _ (by decide),
      m2x POS (by decide) (by decide) (by decide)]; exact hI.pos
  have m4ONE : m4 ONE = 1 := by
    rw [hm4, Mem.write_ne _ _ (by decide), hm3, Mem.write_ne _ _ (by decide),
      m2x ONE (by decide) (by decide) (by decide)]; exact hI.st.one
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write POS (q1 + j + 1) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add POS POS ONE) m4 m5 1 := by
    have := Exec.add POS POS ONE m4; rwa [m4POS, m4ONE, ← hm5] at this
  -- the whole body
  have ebody : Cmd.Exec bitBody m m5 (2 + (k2 + (1 + (1 + 1)))) :=
    Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e5)))
  -- values of the new state
  have m5x : ∀ x, x ≠ POS → x ≠ POW → x ≠ LAST → x ≠ VAL → x ≠ BIT → x ≠ PTR → m5 x = m x := by
    intro x h1 h2 h3 h4 h5 h6
    rw [hm5, Mem.write_ne _ _ h1, hm4, Mem.write_ne _ _ h2, hm3, Mem.write_ne _ _ h3, m2x x h4 h5 h6]
  have hpres5 : Pres m m5 (m HP) bitVars := by
    intro x _ hW
    simp [bitVars] at hW
    exact m5x x hW.1 hW.2.2.1 hW.2.2.2.2.1 hW.2.1 hW.2.2.2.2.2.1 hW.2.2.2.1
  refine ⟨m5, _, ebody, by omega, ?_, ?_, ?_⟩
  · rw [m5x J (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.jv
  · rw [m5x ONE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hI.st.one
  · have hpres6 : Pres m m5 (m HP) (bitVars ++ [J]) := hpres5.mono le_rfl (by intro x hx; simp [hx])
    have hpres6' : Pres m (m5.write J (j + 1)) (m HP) (bitVars ++ [J]) := by
      intro x hx hW
      rw [Mem.write_ne _ _ (by simp at hW; exact hW.2), hpres6 x hx hW]
    have hs5 : PState (m5.write J (j + 1)) bs := hI.st.of_pres hpres6' (by decide)
    have w : ∀ x, x ≠ J → (m5.write J (j + 1)) x = m5 x := fun x hx => Mem.write_ne _ _ hx
    refine ⟨hs5, by omega, hI.hc, Mem.write_same _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w CNT (by decide), m5x CNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hI.cnt
    · rw [w POS (by decide), hm5, Mem.write_same]; omega
    · rw [w VAL (by decide), hm5, Mem.write_ne _ _ (by decide), hm4, Mem.write_ne _ _ (by decide),
        hm3, Mem.write_ne _ _ (by decide), m2VAL, hI.val]
      rw [fromBits_take_succ j (bs.drop q1) (by simp; omega)]
      congr 2
      simp [List.getElem_drop]
    · rw [w POW (by decide), hm5, Mem.write_ne _ _ (by decide), hm4, Mem.write_same]
    · have hL : (m5.write J (j + 1)) LAST = bitv bs[q1 + j] := by
        rw [w LAST (by decide), hm5, Mem.write_ne _ _ (by decide), hm4, Mem.write_ne _ _ (by decide),
          hm3, Mem.write_same]
      rw [hL, dif_pos (by omega)]
      congr 2
    · have := hI.pres.trans hpres6' (by rw [hI.hp])
      exact this.mono le_rfl (by decide)
    · rw [w HP (by decide), m5x HP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hI.hp

theorem bitLoop_spec (m₀ : Mem) (bs : List Bool) (q1 c : ℕ) (m : Mem)
    (hI : BitInv m₀ bs q1 c 0 m) :
    ∃ m' k, Cmd.Exec bitLoop m m' k ∧ BitInv m₀ bs q1 c c m' ∧ k ≤ c * 11 + 2 := by
  have := forLoop_spec J CNT bitBody (BitInv m₀ bs q1 c) c 8
    (fun j m hI => ⟨hI.jv, hI.cnt⟩)
    (fun j m hj hI => by
      obtain ⟨m', k, e, hk, hJ, hone, hI'⟩ := bitBody_spec m₀ bs q1 c j m hI hj
      exact ⟨m', k, e, hk, hJ, hone, hI'⟩)
    0 m (by omega) hI
  obtain ⟨m', k, e, hI', hk⟩ := this
  exact ⟨m', k, e, hI', by simpa using hk⟩

end DisequalityDispersion.Machine

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### The whole natural-number decoder -/

/-- The result contract of a natural-number parse at cursor `p` on input `bs`. -/
def NatResult (m' : Mem) (bs : List Bool) (r : Option (ℕ × List Bool)) : Prop :=
  match r with
  | none => m' OK = 0
  | some (v, rest) => m' OK = 1 ∧ m' VAL = v ∧ m' POS = bs.length - rest.length

/-- After the zero: read `CNT` digits and test canonicity. -/
def natRead : Cmd :=
  .seq (.seq (setc VAL 0) (.seq (setc POW 1) (.seq (setc LAST 1) (setc J 0))))
    (.seq bitLoop (.ite (.eq LAST ONE) (setc OK 1) (setc OK 0)))

/-- Skip the zero; reject if fewer than `CNT` digits remain, else read them. -/
def natTail : Cmd :=
  .seq (add POS POS ONE) (.seq (add TMP POS CNT) (.ite (.lt N TMP) (setc OK 0) natRead))

def decodeNatM : Cmd :=
  .seq (setc CNT 0) (.seq contM (.seq countLoop (.ite (.lt POS N) natTail (setc OK 0))))

/-- Writing a variable preserves everything else. -/
theorem pres_write (m : Mem) (a v : ℕ) (lo : ℕ) : Pres m (m.write a v) lo [a] := by
  intro x _ hW
  simp at hW
  exact Mem.write_ne _ _ hW

theorem decodeNatM_spec {m : Mem} {bs : List Bool} (hs : PState m bs) {p : ℕ} (hp : m POS = p)
    (hpN : p ≤ bs.length) :
    ∃ m' k, Cmd.Exec decodeNatM m m' k ∧ k ≤ 20 * (bs.length - p) + 30 ∧
      Pres m m' (m HP) natVars ∧ PState m' bs ∧ m' HP = m HP ∧
      NatResult m' bs (decodeNat (bs.drop p)) := by
  -- CNT := 0
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write CNT 0 := ⟨_, rfl⟩
  have e1 : Cmd.Exec (setc CNT 0) m m1 1 := by rw [hm1]; exact Exec.setc CNT 0 m
  have p1 : Pres m m1 (m HP) [CNT] := by rw [hm1]; exact pres_write m CNT 0 _
  have hs1 : PState m1 bs := hs.of_pres p1 (by decide)
  have m1pos : m1 POS = p := by rw [hm1, Mem.write_ne _ _ (by decide)]; exact hp
  have m1cnt : m1 CNT = 0 := by rw [hm1, Mem.write_same]
  have m1hp : m1 HP = m HP := by rw [hm1, Mem.write_ne _ _ (by decide)]
  -- CONT := …
  obtain ⟨m2, k2, e2, hk2, hcont2, p2⟩ := contM_spec hs1 m1pos
  rw [m1hp] at p2
  have q2 : ∀ x, x < IN → x ∉ contVars → m2 x = m1 x := fun x hx hW => p2 x (hs.var_lt x hx) hW
  have m2pos : m2 POS = p := by rw [q2 POS (by decide) (by decide)]; exact m1pos
  have m2cnt : m2 CNT = 0 := by rw [q2 CNT (by decide) (by decide)]; exact m1cnt
  have m2hp : m2 HP = m HP := by rw [q2 HP (by decide) (by decide)]; exact m1hp
  have hs2 : PState m2 bs := hs1.of_pres (by rw [m1hp]; exact p2) (by decide)
  have hI2 : CountInv m bs p m2 := by
    refine ⟨hs2, by rw [m2pos], by rw [m2pos]; exact hpN, by rw [m2cnt, m2pos]; omega, ?_, ?_, ?_, m2hp⟩
    · rw [hcont2, m2pos]
    · rw [m2cnt, m2pos]
    · exact (p1.trans p2 le_rfl).mono le_rfl (by decide)
  -- count the ones
  obtain ⟨m3, k3, e3, hI3, hexit, hk3⟩ := countLoop_spec m bs p m2 hI2
  rw [m2pos] at hk3
  have hdec : decodeNat (bs.drop p) = decodeNatAux (m3 CNT) (bs.drop (m3 POS)) := hI3.dec
  rcases hexit with hend | ⟨hlt, hfalse⟩
  · -- the input is exhausted: reject
    have hb : (Cond.lt POS N).eval m3 = false := by
      simp [Cond.eval, hend, hI3.st.n]
    obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write OK 0 := ⟨_, rfl⟩
    have e4 : Cmd.Exec (setc OK 0) m3 m4 1 := by rw [hm4]; exact Exec.setc OK 0 m3
    have p4 : Pres m3 m4 (m3 HP) [OK] := by rw [hm4]; exact pres_write m3 OK 0 _
    refine ⟨m4, 1 + (k2 + (k3 + (1 + 1 + 1))), Cmd.Exec.seq e1 (Cmd.Exec.seq e2
      (Cmd.Exec.seq e3 (Cmd.Exec.ite_false hb e4))), by omega, ?_, ?_, ?_, ?_⟩
    · exact (hI3.pres.trans p4 (by rw [hI3.hp])).mono le_rfl (by decide)
    · exact hI3.st.of_pres p4 (by decide)
    · rw [hm4, Mem.write_ne _ _ (by decide), hI3.hp]
    · rw [hdec, hend, decodeNatAux_drop_end]
      show m4 OK = 0
      rw [hm4, Mem.write_same]
  · -- a zero at `m3 POS`: skip it and read `CNT` digits
    have hb : (Cond.lt POS N).eval m3 = true := by
      simp [Cond.eval, hI3.st.n, hlt]
    generalize hq : m3 POS = q at hlt hfalse hdec
    generalize hc : m3 CNT = c at hdec
    have hcq : c = q - p := by rw [← hc, ← hq]; exact hI3.cnt
    have hpq : p ≤ q := by rw [← hq]; exact hI3.hp_le
    -- POS := POS + 1
    obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write POS (q + 1) := ⟨_, rfl⟩
    have e4 : Cmd.Exec (add POS POS ONE) m3 m4 1 := by
      have := Exec.add POS POS ONE m3; rwa [hq, hI3.st.one, ← hm4] at this
    -- TMP := POS + CNT
    obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write TMP (q + 1 + c) := ⟨_, rfl⟩
    have m4pos : m4 POS = q + 1 := by rw [hm4, Mem.write_same]
    have m4cnt : m4 CNT = c := by rw [hm4, Mem.write_ne _ _ (by decide), hc]
    have e5 : Cmd.Exec (add TMP POS CNT) m4 m5 1 := by
      have := Exec.add TMP POS CNT m4
      rwa [m4pos, m4cnt, ← hm5] at this
    have p5 : Pres m3 m5 (m3 HP) [POS, TMP] := by
      intro x _ hW
      simp at hW
      rw [hm5, Mem.write_ne _ _ hW.2, hm4, Mem.write_ne _ _ hW.1]
    have hs5 : PState m5 bs := hI3.st.of_pres p5 (by decide)
    have m5tmp : m5 TMP = q + 1 + c := by rw [hm5, Mem.write_same]
    have m5pos : m5 POS = q + 1 := by rw [hm5, Mem.write_ne _ _ (by decide), hm4, Mem.write_same]
    have m5cnt : m5 CNT = c := by
      rw [hm5, Mem.write_ne _ _ (by decide), hm4, Mem.write_ne _ _ (by decide), hc]
    have m5hp : m5 HP = m HP := by
      rw [hm5, Mem.write_ne _ _ (by decide), hm4, Mem.write_ne _ _ (by decide), hI3.hp]
    rw [decodeNatAux_drop_false bs c q hlt hfalse] at hdec
    by_cases hover : bs.length < q + 1 + c
    · -- not enough digits: reject
      have hb2 : (Cond.lt N TMP).eval m5 = true := by
        simp [Cond.eval, hs5.n, m5tmp, hover]
      obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write OK 0 := ⟨_, rfl⟩
      have e6 : Cmd.Exec (setc OK 0) m5 m6 1 := by rw [hm6]; exact Exec.setc OK 0 m5
      have p6 : Pres m5 m6 (m5 HP) [OK] := by rw [hm6]; exact pres_write m5 OK 0 _
      refine ⟨m6, _,
        Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.ite_true hb
          (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 (Cmd.Exec.ite_true hb2 e6)))))), by omega, ?_, ?_, ?_, ?_⟩
      · have := (hI3.pres.trans p5 (by rw [hI3.hp])).trans p6 (by rw [m5hp])
        exact this.mono le_rfl (by decide)
      · exact hs5.of_pres p6 (by decide)
      · rw [hm6, Mem.write_ne _ _ (by decide), m5hp]
      · rw [hdec, if_neg (by omega)]
        show m6 OK = 0
        rw [hm6, Mem.write_same]
    · -- enough digits: read them
      have hle : q + 1 + c ≤ bs.length := by omega
      have hb2 : (Cond.lt N TMP).eval m5 = false := by
        simp [Cond.eval, hs5.n, m5tmp, hover]
      obtain ⟨m9, hm9⟩ : ∃ m9, m9 = (((m5.write VAL 0).write POW 1).write LAST 1).write J 0 :=
        ⟨_, rfl⟩
      have e9 : Cmd.Exec (.seq (setc VAL 0) (.seq (setc POW 1) (.seq (setc LAST 1) (setc J 0))))
          m5 m9 (1 + (1 + (1 + 1))) := by
        rw [hm9]
        exact Cmd.Exec.seq (Exec.setc _ _ _) (Cmd.Exec.seq (Exec.setc _ _ _)
          (Cmd.Exec.seq (Exec.setc _ _ _) (Exec.setc _ _ _)))
      have p9 : Pres m5 m9 (m5 HP) [VAL, POW, LAST, J] := by
        intro x _ hW
        simp at hW
        rw [hm9, Mem.write_ne _ _ hW.2.2.2, Mem.write_ne _ _ hW.2.2.1, Mem.write_ne _ _ hW.2.1,
          Mem.write_ne _ _ hW.1]
      have hs9 : PState m9 bs := hs5.of_pres p9 (by decide)
      have q9 : ∀ x, x ≠ VAL → x ≠ POW → x ≠ LAST → x ≠ J → m9 x = m5 x := by
        intro x h1 h2 h3 h4
        rw [hm9, Mem.write_ne _ _ h4, Mem.write_ne _ _ h3, Mem.write_ne _ _ h2, Mem.write_ne _ _ h1]
      have m9J : m9 J = 0 := by rw [hm9, Mem.write_same]
      have m9VAL : m9 VAL = 0 := by
        rw [hm9, Mem.write_ne _ _ (by decide), Mem.write_ne _ _ (by decide),
          Mem.write_ne _ _ (by decide), Mem.write_same]
      have m9POW : m9 POW = 1 := by
        rw [hm9, Mem.write_ne _ _ (by decide), Mem.write_ne _ _ (by decide), Mem.write_same]
      have m9LAST : m9 LAST = 1 := by rw [hm9, Mem.write_ne _ _ (by decide), Mem.write_same]
      have hI9 : BitInv m9 bs (q + 1) c 0 m9 := by
        refine ⟨hs9, Nat.zero_le _, hle, m9J, ?cnt, ?pos, ?val, ?pow, ?last, Pres.refl _ _ _, rfl⟩
        case cnt => rw [q9 CNT (by decide) (by decide) (by decide) (by decide), m5cnt]
        case pos => rw [q9 POS (by decide) (by decide) (by decide) (by decide), m5pos]
        case val => rw [m9VAL]; simp [fromBits]
        case pow => rw [m9POW]; simp
        case last => rw [m9LAST]; simp
      obtain ⟨m10, k10, e10, hI10, hk10⟩ := bitLoop_spec m9 bs (q + 1) c m9 hI9
      have m10hp : m10 HP = m HP := by rw [hI10.hp, q9 HP (by decide) (by decide) (by decide) (by decide), m5hp]
      have p10 : Pres m9 m10 (m9 HP) bitVars := hI10.pres
      -- the final acceptance test
      have hlastC : (m10 LAST = 1) ↔ Canon ((bs.drop (q + 1)).take c) = true := by
        rw [hI10.last, canon_take c _ (by simp; omega)]
        by_cases hc0 : 0 < c
        · rw [dif_pos hc0, dif_pos hc0]
          rw [List.getElem_drop]
          have : q + 1 + (c - 1) = q + 1 + c - 1 := by omega
          simp only [this]
          cases bs[q + 1 + c - 1] <;> simp [bitv]
        · rw [dif_neg hc0, dif_neg hc0]; simp
      obtain ⟨m11, k11, e11, hres, hk11⟩ : ∃ m11 k11,
          Cmd.Exec (.ite (.eq LAST ONE) (setc OK 1) (setc OK 0)) m10 m11 k11 ∧
          (Pres m10 m11 (m10 HP) [OK] ∧
            (m11 OK = if Canon ((bs.drop (q + 1)).take c) then 1 else 0)) ∧ k11 ≤ 3 := by
        by_cases hL : m10 LAST = 1
        · have hb3 : (Cond.eq LAST ONE).eval m10 = true := by simp [Cond.eval, hL, hI10.st.one]
          refine ⟨m10.write OK 1, 1 + 1 + 1, Cmd.Exec.ite_true hb3 (Exec.setc OK 1 m10),
            ⟨pres_write _ _ _ _, ?_⟩, le_rfl⟩
          rw [Mem.write_same, if_pos (hlastC.mp hL)]
        · have hb3 : (Cond.eq LAST ONE).eval m10 = false := by simp [Cond.eval, hL, hI10.st.one]
          refine ⟨m10.write OK 0, 1 + 1 + 1, Cmd.Exec.ite_false hb3 (Exec.setc OK 0 m10),
            ⟨pres_write _ _ _ _, ?_⟩, le_rfl⟩
          rw [Mem.write_same, if_neg (fun h => hL (hlastC.mpr h))]
      obtain ⟨p11, hok11⟩ := hres
      have q11 : ∀ x, x < IN → x ≠ OK → m11 x = m10 x := fun x hx hW =>
        p11 x (hI10.st.var_lt x hx) (by simpa using hW)
      -- assemble
      refine ⟨m11, _,
        Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.ite_true hb
          (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 (Cmd.Exec.ite_false hb2 (Cmd.Exec.seq e9
            (Cmd.Exec.seq e10 e11)))))))), ?_, ?_, ?_, ?_, ?_⟩
      · have : c ≤ bs.length - p := by omega
        have h2 : c * 11 ≤ (bs.length - p) * 11 := Nat.mul_le_mul_right _ this
        omega
      · have A : Pres m m5 (m HP) (countVars ++ [POS, TMP]) := hI3.pres.trans p5 (by rw [hI3.hp])
        have B : Pres m m9 (m HP) ((countVars ++ [POS, TMP]) ++ [VAL, POW, LAST, J]) :=
          A.trans p9 (by rw [m5hp])
        have C : Pres m m10 (m HP) (((countVars ++ [POS, TMP]) ++ [VAL, POW, LAST, J]) ++ bitVars) :=
          B.trans p10 (by rw [hI10.hp] at m10hp; rw [m10hp])
        have D := C.trans p11 (by rw [m10hp])
        exact D.mono le_rfl (by decide)
      · exact hI10.st.of_pres p11 (by decide)
      · rw [q11 HP (by decide) (by decide), m10hp]
      · rw [hdec, if_pos hle]
        by_cases hcan : Canon ((bs.drop (q + 1)).take c) = true
        · rw [if_pos hcan]
          refine ⟨by rw [hok11, if_pos hcan], ?_, ?_⟩
          · rw [q11 VAL (by decide) (by decide), hI10.val]
          · rw [q11 POS (by decide) (by decide), hI10.pos]
            simp only [List.length_drop]
            omega
        · rw [if_neg hcan]
          show m11 OK = 0
          rw [hok11, if_neg hcan]

end DisequalityDispersion.Machine
