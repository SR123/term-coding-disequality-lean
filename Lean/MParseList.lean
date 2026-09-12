import MParse
import ParsingCost

/-! # The parser on the machine, part 2: representations and lists

Parsed values live in the heap: a list of naturals is an array (`RepArr`), a pair is a
two-cell record (`RepPair`), a node is a tagged record (`RepNode`: `[0, i]` for `src i`,
`[1, f, argsPtr]` for `app f args`), a list of records is an array of pointers
(`RepListOf`).  Every representation predicate `rep m lo hi v a` says that the value `a` is
represented by the cell contents/pointer `v` with all its record cells inside `[lo, hi)`
(the part of the heap allocated by the parse that produced it), which makes representations
stable under later allocation (`rep_frame`).

`ParserSpec c f rep W S d` is the contract of a machine parser `c` for a decoder `f`:
on every input and cursor position it runs in at most `S·(|bs| - p + 1)^d` steps, writes
only the variables `W`, the heap pointer and the heap above the heap pointer, and succeeds with a
representation of the decoded value exactly when `f` succeeds, advancing the cursor to the
same rest.  `decodeNatM_pspec` instantiates it for naturals and `decodeListM_pspec` is the
generic list parser: a count followed by that many elements, stopping at the first failure
(so an announced count larger than the input costs nothing beyond the supplied data). -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Representations -/

/-- Representation predicates: `rep m lo hi v a`. -/
abbrev Rep (α : Type) := Mem → ℕ → ℕ → ℕ → α → Prop

def RepNat : Rep ℕ := fun _ _ _ v a => v = a

def RepPair : Rep (ℕ × ℕ) := fun m lo hi v p =>
  lo ≤ v ∧ v + 2 ≤ hi ∧ m v = p.1 ∧ m (v + 1) = p.2

def RepArr : Rep (List ℕ) := fun m lo hi v l =>
  lo ≤ v ∧ v + 1 + l.length ≤ hi ∧ m v = l.length ∧ ∀ i, (h : i < l.length) → m (v + 1 + i) = l[i]

def RepListOf {α : Type} (rep : Rep α) : Rep (List α) := fun m lo hi v l =>
  lo ≤ v ∧ v + 1 + l.length ≤ hi ∧ m v = l.length ∧
    ∀ i, (h : i < l.length) → rep m lo hi (m (v + 1 + i)) l[i]

def RepNode : Rep Node := fun m lo hi v nd =>
  lo ≤ v ∧ match nd with
  | .src i => v + 2 ≤ hi ∧ m v = 0 ∧ m (v + 1) = i
  | .app f args => v + 3 ≤ hi ∧ m v = 1 ∧ m (v + 1) = f ∧ RepArr m lo hi (m (v + 2)) args

/-- A representation is *framed* if it only depends on the cells in `[lo, hi)`, and
*monotone* in the interval. -/
structure GoodRep {α : Type} (rep : Rep α) : Prop where
  frame : ∀ m m' lo hi v a, rep m lo hi v a → (∀ x, lo ≤ x → x < hi → m' x = m x) → rep m' lo hi v a
  mono : ∀ m lo hi lo' hi' v a, rep m lo hi v a → lo' ≤ lo → hi ≤ hi' → rep m lo' hi' v a

theorem goodRep_nat : GoodRep RepNat := ⟨fun _ _ _ _ _ _ h _ => h, fun _ _ _ _ _ _ _ h _ _ => h⟩

theorem goodRep_pair : GoodRep RepPair := by
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v p h hf
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by rw [hf v h1 (by omega), h3], by rw [hf (v + 1) (by omega) (by omega), h4]⟩
  · intro m lo hi lo' hi' v p h h1 h2
    obtain ⟨g1, g2, g3, g4⟩ := h
    exact ⟨by omega, by omega, g3, g4⟩

theorem goodRep_arr : GoodRep RepArr := by
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v l h hf
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, by rw [hf v h1 (by omega), h3], fun i hi => ?_⟩
    rw [hf (v + 1 + i) (by omega) (by omega), h4 i hi]
  · intro m lo hi lo' hi' v l h h1 h2
    obtain ⟨g1, g2, g3, g4⟩ := h
    exact ⟨by omega, by omega, g3, g4⟩

theorem goodRep_listOf {α : Type} {rep : Rep α} (hr : GoodRep rep) : GoodRep (RepListOf rep) := by
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v l h hf
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, by rw [hf v h1 (by omega), h3], fun i hi' => ?_⟩
    rw [hf (v + 1 + i) (by omega) (by omega)]
    exact hr.frame m m' lo hi _ _ (h4 i hi') hf
  · intro m lo hi lo' hi' v l h h1 h2
    obtain ⟨g1, g2, g3, g4⟩ := h
    exact ⟨by omega, by omega, g3, fun i hlt => hr.mono m lo hi lo' hi' _ _ (g4 i hlt) h1 h2⟩

theorem goodRep_node : GoodRep RepNode := by
  refine ⟨?_, ?_⟩
  · intro m m' lo hi v nd h hf
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    cases nd with
    | src i =>
        obtain ⟨g1, g2, g3⟩ := h2
        exact ⟨g1, by rw [hf v h1 (by omega), g2], by rw [hf (v + 1) (by omega) (by omega), g3]⟩
    | app f args =>
        obtain ⟨g1, g2, g3, g4⟩ := h2
        refine ⟨g1, by rw [hf v h1 (by omega), g2], by rw [hf (v + 1) (by omega) (by omega), g3], ?_⟩
        rw [hf (v + 2) (by omega) (by omega)]
        exact goodRep_arr.frame m m' lo hi _ _ g4 hf
  · intro m lo hi lo' hi' v nd h h1 h2
    obtain ⟨g1, g2⟩ := h
    refine ⟨by omega, ?_⟩
    cases nd with
    | src i => obtain ⟨k1, k2, k3⟩ := g2; exact ⟨by omega, k2, k3⟩
    | app f args =>
        obtain ⟨k1, k2, k3, k4⟩ := g2
        exact ⟨by omega, k2, k3, goodRep_arr.mono m lo hi lo' hi' _ _ k4 h1 h2⟩

/-! ### Parser contracts -/

/-- Variables a parser may write must lie strictly between the fixed constants and the input. -/
def GoodVars (W : List ℕ) : Prop := ∀ x, x ∈ W → 5 ≤ x ∧ x < IN

theorem PState.of_pres' {m m' : Mem} {bs : List Bool} (h : PState m bs) {W : List ℕ}
    (hp : Pres m m' (m HP) W) (hW : GoodVars W) : PState m' bs := by
  have hlt : ∀ x, x ∈ W → x < IN := fun x hx => (hW x hx).2
  have hn : ∀ x, x ∈ W → x ≤ 4 → False := fun x hx h4 => by have := (hW x hx).1; omega
  refine ⟨h.input.of_pres hp h.hp hlt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp N (h.var_lt N (by decide)) (fun hm => hn N hm (by decide)), h.n]
  · rw [hp INB (h.var_lt INB (by decide)) (fun hm => hn INB hm (by decide)), h.inb]
  · rw [hp ONE (h.var_lt ONE (by decide)) (fun hm => hn ONE hm (by decide)), h.one]
  · rw [hp ZERO (h.var_lt ZERO (by decide)) (fun hm => hn ZERO hm (by decide)), h.zero]
  · rw [hp HP (h.var_lt HP (by decide)) (fun hm => hn HP hm (by decide))]
    exact h.hp

/-- The result clause of a parser contract. -/
def PResult {α : Type} (rep : Rep α) (m m' : Mem) (bs : List Bool)
    (r : Option (α × List Bool)) : Prop :=
  match r with
  | none => m' OK = 0
  | some (a, rest) => m' OK = 1 ∧ rep m' (m HP) (m' HP) (m' VAL) a ∧ m' POS = bs.length - rest.length

/-- The contract of a machine parser `c` for the decoder `f`. -/
def ParserSpec {α : Type} (c : Cmd) (f : List Bool → Option (α × List Bool)) (rep : Rep α)
    (W : List ℕ) (S d : ℕ) : Prop :=
  ∀ (m : Mem) (bs : List Bool) (p : ℕ), PState m bs → m POS = p → p ≤ bs.length →
    ∃ m' k, Cmd.Exec c m m' k ∧ k ≤ S * (bs.length - p + 1) ^ d ∧ Pres m m' (m HP) (HP :: W) ∧
      PState m' bs ∧ m HP ≤ m' HP ∧ PResult rep m m' bs (f (bs.drop p))

/-- Decoders return a suffix of their input. -/
def SuffixP {α : Type} (f : List Bool → Option (α × List Bool)) : Prop :=
  ∀ l a rest, f l = some (a, rest) → ∃ pre, l = pre ++ rest

theorem suffix_drop {α : Type} {f : List Bool → Option (α × List Bool)} (hs : SuffixP f)
    (bs : List Bool) (p : ℕ) (hp : p ≤ bs.length) {a : α} {rest : List Bool}
    (h : f (bs.drop p) = some (a, rest)) : rest = bs.drop (bs.length - rest.length) := by
  obtain ⟨pre, hpre⟩ := hs _ a rest h
  have h2 := congrArg List.length hpre
  simp at h2
  calc rest = (bs.drop p).drop pre.length := by rw [hpre, List.drop_left]
    _ = bs.drop (p + pre.length) := List.drop_drop
    _ = bs.drop (bs.length - rest.length) := by congr 1; omega

theorem suffix_decodeNat : SuffixP decodeNat := fun l a rest h => ⟨_, decodeNat_some l a rest h⟩

theorem natVars_good : GoodVars natVars := by
  intro x hx
  simp [natVars, POS, OK, VAL, TMP, CNT, POW, PTR, LAST, BIT, J, CONT] at hx
  simp [IN]; omega

/-- The natural-number parser satisfies the contract with `rep = RepNat`. -/
theorem decodeNatM_pspec : ParserSpec decodeNatM decodeNat RepNat natVars 50 1 := by
  intro m bs p hs hp hpN
  obtain ⟨m', k, e, hk, hpres, hs', hhp, hres⟩ := decodeNatM_spec hs hp hpN
  refine ⟨m', k, e, ?_, hpres.mono le_rfl (fun x hx => List.mem_cons_of_mem _ hx), hs', by rw [hhp], ?_⟩
  · have : 20 * (bs.length - p) + 30 ≤ 50 * (bs.length - p + 1) ^ 1 := by simp; omega
    omega
  · unfold PResult
    unfold NatResult at hres
    revert hres
    cases decodeNat (bs.drop p) with
    | none => exact id
    | some q =>
        obtain ⟨v, rest⟩ := q
        exact fun hres => ⟨hres.1, hres.2.1, hres.2.2⟩

end DisequalityDispersion.Machine

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### The generic list parser -/

/-- Loop variables of nesting level `l` (`l ≤ 1`). -/
def A_ (l : ℕ) : ℕ := 20 + 4 * l
def NEL (l : ℕ) : ℕ := 21 + 4 * l
def JJ (l : ℕ) : ℕ := 22 + 4 * l
def CC (l : ℕ) : ℕ := 23 + 4 * l

def loopVars (l : ℕ) : List ℕ := [JJ l, CC l, PTR, VAL, OK, HP]

/-- Decide (in)equalities between fixed addresses. -/
macro "addr" : tactic => `(tactic| (first | omega | (simp only [A_, NEL, JJ, CC, IN_eq', HP_eq',
  ONE_eq', POS_eq, OK_eq, VAL_eq, TMP_eq, N_eq, INB_eq, ZERO_eq, CNT_eq, POW_eq, PTR_eq, LAST_eq,
  BIT_eq, J_eq, CONT_eq] at * <;> omega)))

/-- `CC := if JJ < NEL then OK else 0`. -/
def computeCC (l : ℕ) : Cmd := .ite (.lt (JJ l) (NEL l)) (mov (CC l) OK) (setc (CC l) 0)

/-- Store `VAL` into slot `JJ` of the array at `A_`, advance, recompute the flag. -/
def storeStep (l : ℕ) : Cmd :=
  .seq (add PTR (A_ l) (JJ l)) (.seq (add PTR PTR ONE) (.seq (store PTR VAL)
    (.seq (add (JJ l) (JJ l) ONE) (computeCC l))))

def listBody (l : ℕ) (elemM : Cmd) : Cmd :=
  .seq elemM (.ite (.eq OK ONE) (storeStep l) (setc (CC l) 0))

def listLoop (l : ℕ) (elemM : Cmd) : Cmd := .loop (.eq (CC l) ONE) (listBody l elemM)

/-- After the count is in `VAL`: reserve the array, set the header, start the loop flag. -/
def listSetup (l : ℕ) : Cmd :=
  .seq (mov (NEL l) VAL) (.seq (mov (A_ l) HP) (.seq (add HP HP ONE) (.seq (add HP HP (NEL l))
    (.seq (store (A_ l) (NEL l)) (.seq (setc (JJ l) 0) (computeCC l))))))

/-- The list parser: a count, then that many elements, stopping at the first failure. -/
def decodeListM (l : ℕ) (elemM : Cmd) : Cmd :=
  .seq decodeNatM (.ite (.eq OK ONE)
    (.seq (listSetup l) (.seq (listLoop l elemM) (.ite (.eq OK ONE) (mov VAL (A_ l)) nop)))
    nop)

/-- A `PState` survives changes above the input region. -/
theorem PState.of_pres_lo {m m' : Mem} {bs : List Bool} (h : PState m bs) {W : List ℕ}
    (hp : Pres m m' (IN + 1 + bs.length) W) (hW : GoodVars W) : PState m' bs := by
  have hlt : ∀ x, x ∈ W → x < IN := fun x hx => (hW x hx).2
  have hn : ∀ x, x ∈ W → x ≤ 4 → False := fun x hx h4 => by have := (hW x hx).1; omega
  have hv : ∀ x, x < IN → x < IN + 1 + bs.length := fun x hx => by omega
  refine ⟨h.input.of_pres hp le_rfl hlt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp N (hv N (by decide)) (fun hm => hn N hm (by decide)), h.n]
  · rw [hp INB (hv INB (by decide)) (fun hm => hn INB hm (by decide)), h.inb]
  · rw [hp ONE (hv ONE (by decide)) (fun hm => hn ONE hm (by decide)), h.one]
  · rw [hp ZERO (hv ZERO (by decide)) (fun hm => hn ZERO hm (by decide)), h.zero]
  · rw [hp HP (hv HP (by decide)) (fun hm => hn HP hm (by decide))]; exact h.hp

/-- State of the list loop: array at `A` with `n` slots, `j` filled, cursor `p`. -/
structure LInv (bs : List Bool) (l : ℕ) (A n j p : ℕ) (m : Mem) : Prop where
  st : PState m bs
  a : m (A_ l) = A
  nel : m (NEL l) = n
  jj : m (JJ l) = j
  pos : m POS = p
  hpN : p ≤ bs.length
  ok : m OK = 1
  cc : m (CC l) = if j < n then 1 else 0
  hj : j ≤ n
  region : A + 1 + n ≤ m HP
  hA : IN + 1 + bs.length ≤ A

/-- The result clause of the loop. -/
def LResult {α : Type} (rep : Rep α) (m m' : Mem) (bs : List Bool) (l A j n : ℕ)
    (r : Option (List α × List Bool)) : Prop :=
  match r with
  | none => m' OK = 0
  | some (as, rest) => m' OK = 1 ∧
      (∀ i, (h : i < as.length) → rep m' (m HP) (m' HP) (m' (A + 1 + j + i)) as[i]) ∧
      m' POS = bs.length - rest.length ∧ m' (JJ l) = n

theorem decodeN_zero {α : Type} (f : List Bool → Option (α × List Bool)) (l : List Bool) :
    decodeN f 0 l = some ([], l) := rfl

theorem decodeN_succ {α : Type} (f : List Bool → Option (α × List Bool)) (r : ℕ) (l : List Bool) :
    decodeN f (r + 1) l = bindP f (fun a => bindP (decodeN f r) (fun as => pureP (a :: as))) l := rfl

theorem bindP_none {α β : Type} {f : List Bool → Option (α × List Bool)}
    {g : α → List Bool → Option (β × List Bool)} {l : List Bool} (h : f l = none) :
    bindP f g l = none := by simp [bindP, h]

theorem listLoop_spec {α : Type} {f : List Bool → Option (α × List Bool)} {rep : Rep α}
    (hgr : GoodRep rep) {elemM : Cmd} {W : List ℕ} {S d : ℕ}
    (hspec : ParserSpec elemM f rep W S d) (hprog : Progress f) (hsuf : SuffixP f)
    (hW : GoodVars W) (l : ℕ) (hl : l ≤ 1)
    (hWl : A_ l ∉ W ∧ NEL l ∉ W ∧ JJ l ∉ W ∧ CC l ∉ W) :
    ∀ (r : ℕ) (bs : List Bool) (A n j p : ℕ) (m : Mem), LInv bs l A n j p m → r = n - j →
      ∃ m' k, Cmd.Exec (listLoop l elemM) m m' k ∧
        (∀ x, x < m HP → x ∉ W → x ∉ loopVars l → ¬ (A + 1 + j ≤ x ∧ x < A + 1 + n) →
          m' x = m x) ∧
        PState m' bs ∧ m HP ≤ m' HP ∧ m' (A_ l) = A ∧ m' (NEL l) = n ∧
        LResult rep m m' bs l A j n (decodeN f r (bs.drop p)) ∧
        k ≤ (bs.length - p + 1) * (S * (bs.length - p + 1) ^ d + 14) + 2 := by
  have hvars : ∀ x, x ∈ loopVars l → x < IN := by
    intro x hx; simp [loopVars] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> addr
  intro r
  induction r with
  | zero =>
      intro bs A n j p m hI hr
      have hj := hI.hj
      have hjn : j = n := by omega
      have hcc : (Cond.eq (CC l) ONE).eval m = false := by
        simp [Cond.eval, hI.cc, hI.st.one, hjn]
      refine ⟨m, 1 + 1, Cmd.Exec.loop_false hcc, fun x _ _ _ _ => rfl, hI.st, le_rfl, hI.a, hI.nel,
        ?_, ?_⟩
      · rw [decodeN_zero]
        refine ⟨hI.ok, fun i h => absurd h (by simp), ?_, by rw [hI.jj, hjn]⟩
        rw [hI.pos, List.length_drop]
        have := hI.hpN; omega
      · omega
  | succ r ih =>
      intro bs A n j p m hI hr
      have hA := hI.hA
      have hj := hI.hj
      have hreg := hI.region
      have hhp0 := hI.st.hp
      have hjn : j < n := by omega
      have hcc : (Cond.eq (CC l) ONE).eval m = true := by
        simp [Cond.eval, hI.cc, hI.st.one, hjn]
      -- run the element parser
      obtain ⟨m1, k1, e1, hk1, pres1, hs1, hhp1, res1⟩ := hspec m bs p hI.st hI.pos hI.hpN
      have q1 : ∀ x, x < IN → x ≠ HP → x ∉ W → m1 x = m x := fun x hx hHP hW' =>
        pres1 x (hI.st.var_lt x hx) (by rw [List.mem_cons]; exact fun h => h.elim hHP hW')
      have m1A : m1 (A_ l) = A := by rw [q1 _ (by addr) (by addr) hWl.1]; exact hI.a
      have m1NEL : m1 (NEL l) = n := by rw [q1 _ (by addr) (by addr) hWl.2.1]; exact hI.nel
      have m1JJ : m1 (JJ l) = j := by rw [q1 _ (by addr) (by addr) hWl.2.2.1]; exact hI.jj
      have m1CC : m1 (CC l) = 1 := by
        rw [q1 _ (by addr) (by addr) hWl.2.2.2, hI.cc, if_pos hjn]
      have hregion1 : A + 1 + n ≤ m1 HP := le_trans hI.region hhp1
      unfold PResult at res1
      cases hf : f (bs.drop p) with
      | none =>
          rw [hf] at res1
          -- the element failed: clear the flag and leave the loop
          have hok1 : (Cond.eq OK ONE).eval m1 = false := by simp [Cond.eval, res1, hs1.one]
          obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (CC l) 0 := ⟨_, rfl⟩
          have e2 : Cmd.Exec (setc (CC l) 0) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
          have q2 : ∀ x, x ≠ CC l → m2 x = m1 x := fun x hx => by rw [hm2, Mem.write_ne _ _ hx]
          have hcc2 : (Cond.eq (CC l) ONE).eval m2 = false := by
            have h1 : m2 ONE = 1 := by rw [q2 ONE (by addr)]; exact hs1.one
            have h0 : m2 (CC l) = 0 := by rw [hm2, Mem.write_same]
            simp [Cond.eval, h0, h1]
          refine ⟨m2, _, Cmd.Exec.loop_true hcc (Cmd.Exec.seq e1 (Cmd.Exec.ite_false hok1 e2))
            (Cmd.Exec.loop_false hcc2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx hxW hxL _
            have hxCC : x ≠ CC l := fun h => hxL (by rw [h]; simp [loopVars])
            have hxHP : x ≠ HP := fun h => hxL (by rw [h]; simp [loopVars])
            rw [q2 x hxCC, pres1 x hx (by rw [List.mem_cons]; exact fun h => h.elim hxHP hxW)]
          · exact hs1.of_pres' (by rw [hm2]; exact pres_write _ _ _ _)
              (by intro x hx; simp at hx; subst hx; constructor <;> addr)
          · rw [q2 HP (by addr)]; exact hhp1
          · rw [q2 _ (by addr)]; exact m1A
          · rw [q2 _ (by addr)]; exact m1NEL
          · rw [decodeN_succ, bindP_none hf]
            show m2 OK = 0
            rw [q2 OK (by addr)]; exact res1
          · have hx : 1 ≤ bs.length - p + 1 := by omega
            have := Nat.mul_le_mul hx (le_refl (S * (bs.length - p + 1) ^ d + 14))
            omega
      | some q =>
          obtain ⟨a, rest⟩ := q
          rw [hf] at res1
          obtain ⟨hok1, hrep1, hpos1⟩ := res1
          -- progress of the element parser
          have hrest : rest.length < bs.length - p := by
            have := hprog _ _ _ hf; simpa using this
          have hrest' : rest = bs.drop (bs.length - rest.length) := suffix_drop hsuf bs p hI.hpN hf
          obtain ⟨p', hp'⟩ : ∃ p', p' = bs.length - rest.length := ⟨_, rfl⟩
          have hpp' : p < p' := by omega
          have hp'N : p' ≤ bs.length := by omega
          rw [← hp'] at hpos1 hrest'
          -- store the element
          have hok1' : (Cond.eq OK ONE).eval m1 = true := by simp [Cond.eval, hok1, hs1.one]
          obtain ⟨v, hv⟩ : ∃ v, v = m1 VAL := ⟨_, rfl⟩
          obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write PTR (A + j) := ⟨_, rfl⟩
          have e2 : Cmd.Exec (add PTR (A_ l) (JJ l)) m1 m2 1 := by
            have := Exec.add PTR (A_ l) (JJ l) m1; rwa [m1A, m1JJ, ← hm2] at this
          obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write PTR (A + j + 1) := ⟨_, rfl⟩
          have e3 : Cmd.Exec (add PTR PTR ONE) m2 m3 1 := by
            have := Exec.add PTR PTR ONE m2
            rw [hm2, Mem.write_same, Mem.write_ne _ _ (by decide), hs1.one] at this
            rw [hm3, hm2]; exact this
          have m3PTR : m3 PTR = A + j + 1 := by rw [hm3, Mem.write_same]
          have m3VAL : m3 VAL = v := by
            rw [hm3, Mem.write_ne _ _ (by decide), hm2, Mem.write_ne _ _ (by decide), hv]
          obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (A + j + 1) v := ⟨_, rfl⟩
          have e4 : Cmd.Exec (store PTR VAL) m3 m4 1 := by
            have := Exec.store PTR VAL m3; rwa [m3PTR, m3VAL, ← hm4] at this
          have m4JJ : m4 (JJ l) = j := by
            rw [hm4, Mem.write_ne _ _ (by addr), hm3, Mem.write_ne _ _ (by addr), hm2,
              Mem.write_ne _ _ (by addr), m1JJ]
          have m4ONE : m4 ONE = 1 := by
            rw [hm4, Mem.write_ne _ _ (by addr), hm3, Mem.write_ne _ _ (by decide), hm2,
              Mem.write_ne _ _ (by decide), hs1.one]
          obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (JJ l) (j + 1) := ⟨_, rfl⟩
          have e5 : Cmd.Exec (add (JJ l) (JJ l) ONE) m4 m5 1 := by
            have := Exec.add (JJ l) (JJ l) ONE m4; rwa [m4JJ, m4ONE, ← hm5] at this
          -- values after the four stores
          have q5 : ∀ x, x ≠ JJ l → x ≠ PTR → x ≠ A + j + 1 → m5 x = m1 x := by
            intro x h1 h2 h3
            rw [hm5, Mem.write_ne _ _ h1, hm4, Mem.write_ne _ _ h3, hm3, Mem.write_ne _ _ h2, hm2,
              Mem.write_ne _ _ h2]
          have m5JJ : m5 (JJ l) = j + 1 := by rw [hm5, Mem.write_same]
          have m5NEL : m5 (NEL l) = n := by
            rw [q5 _ (by addr) (by addr) (by addr)]; exact m1NEL
          have m5OK : m5 OK = 1 := by
            rw [q5 _ (by addr) (by decide) (by addr)]; exact hok1
          have m5ONE : m5 ONE = 1 := by
            rw [q5 _ (by addr) (by decide) (by addr)]; exact hs1.one
          -- recompute the flag
          obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write (CC l) (if j + 1 < n then 1 else 0) := ⟨_, rfl⟩
          have e6 : ∃ k, Cmd.Exec (computeCC l) m5 m6 k ∧ k ≤ 3 := by
            unfold computeCC
            by_cases hlt : j + 1 < n
            · have hc : (Cond.lt (JJ l) (NEL l)).eval m5 = true := by
                simp [Cond.eval, m5JJ, m5NEL, hlt]
              have hm6' : m6 = m5.write (CC l) 1 := by rw [hm6, if_pos hlt]
              refine ⟨1 + 1 + 1, Cmd.Exec.ite_true hc ?_, le_rfl⟩
              have := Exec.mov (CC l) OK m5
              rwa [m5OK, ← hm6'] at this
            · have hc : (Cond.lt (JJ l) (NEL l)).eval m5 = false := by
                simp [Cond.eval, m5JJ, m5NEL, hlt]
              have hm6' : m6 = m5.write (CC l) 0 := by rw [hm6, if_neg hlt]
              refine ⟨1 + 1 + 1, Cmd.Exec.ite_false hc ?_, le_rfl⟩
              have := Exec.setc (CC l) 0 m5
              rwa [← hm6'] at this
          obtain ⟨k6, e6, hk6⟩ := e6
          have q6 : ∀ x, x ≠ CC l → m6 x = m5 x := fun x hx => by rw [hm6, Mem.write_ne _ _ hx]
          have q6' : ∀ x, x ≠ CC l → x ≠ JJ l → x ≠ PTR → x ≠ A + j + 1 → m6 x = m1 x :=
            fun x h0 h1 h2 h3 => by rw [q6 x h0, q5 x h1 h2 h3]
          -- the new loop state
          have hpres6 : Pres m1 m6 (IN + 1 + bs.length) [CC l, JJ l, PTR] := by
            intro x hx hxW
            simp at hxW
            exact q6' x hxW.1 hxW.2.1 hxW.2.2 (by omega)
          have hs6 : PState m6 bs := hs1.of_pres_lo hpres6
            (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> constructor <;> addr)
          have m6HP : m6 HP = m1 HP := by
            rw [q6' HP (by addr) (by addr) (by decide) (by addr)]
          have hI6 : LInv bs l A n (j + 1) p' m6 := by
            refine ⟨hs6, ?_, ?_, ?_, ?_, hp'N, ?_, ?_, by omega, ?_, hA⟩
            · rw [q6' _ (by addr) (by addr) (by addr) (by addr)]; exact m1A
            · rw [q6 _ (by addr)]; exact m5NEL
            · rw [q6 _ (by addr)]; exact m5JJ
            · rw [q6' _ (by addr) (by addr) (by decide) (by addr)]; exact hpos1
            · rw [q6 _ (by addr)]; exact m5OK
            · rw [hm6, Mem.write_same]
            · rw [m6HP]; exact hregion1
          -- the rest of the loop
          obtain ⟨m7, k7, e7, frame7, hs7, hhp7, a7, nel7, res7, hk7⟩ :=
            ih bs A n (j + 1) p' m6 hI6 (by omega)
          rw [m6HP] at frame7 hhp7
          have hnotW : ∀ x, IN ≤ x → x ∉ W := fun x hx h => by have := (hW _ h).2; omega
          have hnotL : ∀ x, IN ≤ x → x ∉ loopVars l := fun x hx h => by have := hvars _ h; omega
          -- assemble
          refine ⟨m7, _, Cmd.Exec.loop_true hcc (Cmd.Exec.seq e1 (Cmd.Exec.ite_true hok1'
            (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 e6)))))) e7,
            ?_, hs7, le_trans hhp1 hhp7, a7, nel7, ?_, ?_⟩
          · intro x hx hxW hxL hxR
            have hxCC : x ≠ CC l := fun h => hxL (by rw [h]; simp [loopVars])
            have hxJJ : x ≠ JJ l := fun h => hxL (by rw [h]; simp [loopVars])
            have hxPTR : x ≠ PTR := fun h => hxL (by rw [h]; simp [loopVars])
            have hxHP : x ≠ HP := fun h => hxL (by rw [h]; simp [loopVars])
            rw [frame7 x (by omega) hxW hxL (by omega), q6' x hxCC hxJJ hxPTR (by omega),
              pres1 x hx (by rw [List.mem_cons]; exact fun h => h.elim hxHP hxW)]
          · unfold LResult at res7
            rw [m6HP] at res7
            rw [decodeN_succ, bindP_of_eq hf, hrest']
            rcases hd : decodeN f r (bs.drop p') with _ | ⟨as, rest'⟩
            · rw [hd] at res7
              rw [show bindP (decodeN f r) (fun as => pureP (a :: as)) (bs.drop p') = none from by
                simp [bindP, hd]]
              exact res7
            · rw [hd] at res7
              obtain ⟨hok7, hels7, hpos7, hjj7⟩ := res7
              rw [show bindP (decodeN f r) (fun as => pureP (a :: as)) (bs.drop p') =
                  some (a :: as, rest') from by simp [bindP, hd, pureP]]
              refine ⟨hok7, ?_, hpos7, hjj7⟩
              intro i hi
              cases i with
              | zero =>
                  simp only [Nat.add_zero, List.getElem_cons_zero]
                  -- the freshly stored element
                  have hcell : m7 (A + 1 + j) = v := by
                    rw [frame7 (A + 1 + j) (by omega) (hnotW _ (by omega)) (hnotL _ (by omega))
                      (by omega)]
                    rw [q6 _ (by addr), hm5, Mem.write_ne _ _ (by addr), hm4,
                      show A + 1 + j = A + j + 1 by omega, Mem.write_same]
                  rw [hcell]
                  have hrep' : rep m6 (m HP) (m1 HP) v a := by
                    rw [hv]
                    refine hgr.frame m1 m6 (m HP) (m1 HP) _ _ hrep1 ?_
                    intro x hx1 hx2
                    exact q6' x (by addr) (by addr) (by addr) (by omega)
                  have hrep'' : rep m7 (m HP) (m1 HP) v a := by
                    refine hgr.frame m6 m7 (m HP) (m1 HP) _ _ hrep' ?_
                    intro x hx1 hx2
                    exact frame7 x hx2 (hnotW _ (by omega)) (hnotL _ (by omega)) (by omega)
                  exact hgr.mono m7 _ _ _ _ _ _ hrep'' le_rfl hhp7
              | succ i =>
                  simp only [List.getElem_cons_succ]
                  have := hels7 i (by simpa using hi)
                  rw [show A + 1 + j + (i + 1) = A + 1 + (j + 1) + i by omega]
                  exact hgr.mono m7 _ _ _ _ _ _ this hhp1 le_rfl
          · -- cost
            have hx : bs.length - p' + 1 ≤ bs.length - p := by omega
            have hmono : (bs.length - p' + 1) ^ d ≤ (bs.length - p + 1) ^ d :=
              Nat.pow_le_pow_left (by omega) d
            have h1 : (bs.length - p' + 1) * (S * (bs.length - p' + 1) ^ d + 14) ≤
                (bs.length - p) * (S * (bs.length - p + 1) ^ d + 14) :=
              Nat.mul_le_mul hx (by have := Nat.mul_le_mul_left S hmono; omega)
            have e : (bs.length - p + 1) * (S * (bs.length - p + 1) ^ d + 14) =
                (bs.length - p) * (S * (bs.length - p + 1) ^ d + 14) + (S * (bs.length - p + 1) ^ d + 14) := by
              ring
            omega


/-! ### Suffix facts for the combinators -/

theorem suffix_bind {α β : Type} {f : List Bool → Option (α × List Bool)}
    {g : α → List Bool → Option (β × List Bool)} (hf : SuffixP f)
    (hg : ∀ a, SuffixP (g a)) : SuffixP (bindP f g) := by
  intro l b rest h
  cases hfl : f l with
  | none => simp [bindP, hfl] at h
  | some q =>
      obtain ⟨a, rest'⟩ := q
      rw [bindP_of_eq hfl] at h
      obtain ⟨pre1, h1⟩ := hf l a rest' hfl
      obtain ⟨pre2, h2⟩ := hg a rest' b rest h
      exact ⟨pre1 ++ pre2, by rw [h1, h2, List.append_assoc]⟩

theorem suffix_pure {β : Type} (b : β) : SuffixP (pureP b) := fun l b' rest h => by
  obtain ⟨_, h2⟩ := pureP_some h
  exact ⟨[], by rw [h2]; rfl⟩

theorem suffix_decodeN {α : Type} {f : List Bool → Option (α × List Bool)} (hf : SuffixP f) :
    ∀ n, SuffixP (decodeN f n)
  | 0 => fun l as rest h => by
      rw [decodeN_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[], by rw [h.2]; rfl⟩
  | n + 1 => by
      show SuffixP (bindP f (fun a => bindP (decodeN f n) (fun as => pureP (a :: as))))
      exact suffix_bind hf (fun a => suffix_bind (suffix_decodeN hf n) (fun as => suffix_pure _))

theorem suffix_decodeList {α : Type} {f : List Bool → Option (α × List Bool)} (hf : SuffixP f) :
    SuffixP (decodeList f) :=
  suffix_bind suffix_decodeNat (fun n => suffix_decodeN hf n)

theorem suffix_tagP {α : Type} {f0 f1 : List Bool → Option (α × List Bool)} (h0 : SuffixP f0)
    (h1 : SuffixP f1) : SuffixP (tagP f0 f1) := by
  intro l a rest h
  cases l with
  | nil => simp [tagP] at h
  | cons b l =>
      cases b with
      | false =>
          obtain ⟨pre, hpre⟩ := h0 l a rest h
          exact ⟨false :: pre, by rw [List.cons_append, hpre]⟩
      | true =>
          obtain ⟨pre, hpre⟩ := h1 l a rest h
          exact ⟨true :: pre, by rw [List.cons_append, hpre]⟩

theorem decodeN_length {α : Type} (f : List Bool → Option (α × List Bool)) :
    ∀ (n : ℕ) (l : List Bool) (as : List α) (rest : List Bool),
      decodeN f n l = some (as, rest) → as.length = n
  | 0, l, as, rest, h => by
      rw [decodeN_zero] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
  | n + 1, l, as, rest, h => by
      rw [decodeN_succ] at h
      obtain ⟨a, l1, h1, h2⟩ := bindP_some h
      obtain ⟨as1, l2, h3, h4⟩ := bindP_some h2
      obtain ⟨h5, _⟩ := pureP_some h4
      rw [h5, List.length_cons, decodeN_length f n l1 as1 l2 h3]

/-! ### The list parser's contract -/

theorem listSetup_spec (l : ℕ) (hl : l ≤ 1) {m : Mem} {bs : List Bool} (hs : PState m bs) (n : ℕ)
    (hv : m VAL = n) :
    ∃ m' k, Cmd.Exec (listSetup l) m m' k ∧ k ≤ 9 ∧
      (∀ x, x ≠ NEL l → x ≠ A_ l → x ≠ HP → x ≠ JJ l → x ≠ CC l → x ≠ m HP → m' x = m x) ∧
      m' (NEL l) = n ∧ m' (A_ l) = m HP ∧ m' HP = m HP + 1 + n ∧ m' (m HP) = n ∧
      m' (JJ l) = 0 ∧ m' (CC l) = (if 0 < n then m OK else 0) := by
  have hhp := hs.hp
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write (NEL l) n := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (NEL l) VAL) m m1 1 := by
    have := Exec.mov (NEL l) VAL m; rwa [hv, ← hm1] at this
  have q1 : ∀ x, x ≠ NEL l → m1 x = m x := fun x h => by rw [hm1, Mem.write_ne _ _ h]
  have m1NEL : m1 (NEL l) = n := by rw [hm1, Mem.write_same]
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (A_ l) (m HP) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (mov (A_ l) HP) m1 m2 1 := by
    have := Exec.mov (A_ l) HP m1; rwa [q1 HP (by addr), ← hm2] at this
  have q2 : ∀ x, x ≠ NEL l → x ≠ A_ l → m2 x = m x := fun x h1 h2 => by
    rw [hm2, Mem.write_ne _ _ h2, q1 x h1]
  have m2A : m2 (A_ l) = m HP := by rw [hm2, Mem.write_same]
  have m2NEL : m2 (NEL l) = n := by rw [hm2, Mem.write_ne _ _ (by addr), m1NEL]
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write HP (m HP + 1) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add HP HP ONE) m2 m3 1 := by
    have := Exec.add HP HP ONE m2
    rwa [q2 HP (by addr) (by addr), q2 ONE (by addr) (by addr), hs.one, ← hm3] at this
  have q3 : ∀ x, x ≠ NEL l → x ≠ A_ l → x ≠ HP → m3 x = m x := fun x h1 h2 h3 => by
    rw [hm3, Mem.write_ne _ _ h3, q2 x h1 h2]
  have m3HP : m3 HP = m HP + 1 := by rw [hm3, Mem.write_same]
  have m3NEL : m3 (NEL l) = n := by rw [hm3, Mem.write_ne _ _ (by addr), m2NEL]
  have m3A : m3 (A_ l) = m HP := by rw [hm3, Mem.write_ne _ _ (by addr), m2A]
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (m HP + 1 + n) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (NEL l)) m3 m4 1 := by
    have := Exec.add HP HP (NEL l) m3; rwa [m3HP, m3NEL, ← hm4] at this
  have q4 : ∀ x, x ≠ NEL l → x ≠ A_ l → x ≠ HP → m4 x = m x := fun x h1 h2 h3 => by
    rw [hm4, Mem.write_ne _ _ h3, q3 x h1 h2 h3]
  have m4HP : m4 HP = m HP + 1 + n := by rw [hm4, Mem.write_same]
  have m4NEL : m4 (NEL l) = n := by rw [hm4, Mem.write_ne _ _ (by addr), m3NEL]
  have m4A : m4 (A_ l) = m HP := by rw [hm4, Mem.write_ne _ _ (by addr), m3A]
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (m HP) n := ⟨_, rfl⟩
  have e5 : Cmd.Exec (store (A_ l) (NEL l)) m4 m5 1 := by
    have := Exec.store (A_ l) (NEL l) m4; rwa [m4A, m4NEL, ← hm5] at this
  have q5 : ∀ x, x ≠ NEL l → x ≠ A_ l → x ≠ HP → x ≠ m HP → m5 x = m x := fun x h1 h2 h3 h4 => by
    rw [hm5, Mem.write_ne _ _ h4, q4 x h1 h2 h3]
  have m5hdr : m5 (m HP) = n := by rw [hm5, Mem.write_same]
  have m5HP : m5 HP = m HP + 1 + n := by rw [hm5, Mem.write_ne _ _ (by addr), m4HP]
  have m5NEL : m5 (NEL l) = n := by rw [hm5, Mem.write_ne _ _ (by addr), m4NEL]
  have m5A : m5 (A_ l) = m HP := by rw [hm5, Mem.write_ne _ _ (by addr), m4A]
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write (JJ l) 0 := ⟨_, rfl⟩
  have e6 : Cmd.Exec (setc (JJ l) 0) m5 m6 1 := by rw [hm6]; exact Exec.setc _ _ _
  have q6 : ∀ x, x ≠ NEL l → x ≠ A_ l → x ≠ HP → x ≠ JJ l → x ≠ m HP → m6 x = m x :=
    fun x h1 h2 h3 h4 h5 => by rw [hm6, Mem.write_ne _ _ h4, q5 x h1 h2 h3 h5]
  have m6JJ : m6 (JJ l) = 0 := by rw [hm6, Mem.write_same]
  have m6NEL : m6 (NEL l) = n := by rw [hm6, Mem.write_ne _ _ (by addr), m5NEL]
  have m6OK : m6 OK = m OK := q6 OK (by addr) (by addr) (by addr) (by addr) (by addr)
  obtain ⟨m7, hm7⟩ : ∃ m7, m7 = m6.write (CC l) (if 0 < n then m OK else 0) := ⟨_, rfl⟩
  have e7 : ∃ k, Cmd.Exec (computeCC l) m6 m7 k ∧ k ≤ 3 := by
    unfold computeCC
    by_cases hlt : 0 < n
    · have hc : (Cond.lt (JJ l) (NEL l)).eval m6 = true := by simp [Cond.eval, m6JJ, m6NEL, hlt]
      have hm7' : m7 = m6.write (CC l) (m OK) := by rw [hm7, if_pos hlt]
      refine ⟨1 + 1 + 1, Cmd.Exec.ite_true hc ?_, le_rfl⟩
      have := Exec.mov (CC l) OK m6
      rwa [m6OK, ← hm7'] at this
    · have hc : (Cond.lt (JJ l) (NEL l)).eval m6 = false := by simp [Cond.eval, m6JJ, m6NEL, hlt]
      have hm7' : m7 = m6.write (CC l) 0 := by rw [hm7, if_neg hlt]
      refine ⟨1 + 1 + 1, Cmd.Exec.ite_false hc ?_, le_rfl⟩
      have := Exec.setc (CC l) 0 m6
      rwa [← hm7'] at this
  obtain ⟨k7, e7, hk7⟩ := e7
  have q7 : ∀ x, x ≠ NEL l → x ≠ A_ l → x ≠ HP → x ≠ JJ l → x ≠ CC l → x ≠ m HP → m7 x = m x :=
    fun x h1 h2 h3 h4 h5 h6 => by rw [hm7, Mem.write_ne _ _ h5, q6 x h1 h2 h3 h4 h6]
  refine ⟨m7, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
    (Cmd.Exec.seq e5 (Cmd.Exec.seq e6 e7))))), by omega, q7, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm7, Mem.write_ne _ _ (by addr), m6NEL]
  · rw [hm7, Mem.write_ne _ _ (by addr), hm6, Mem.write_ne _ _ (by addr), m5A]
  · rw [hm7, Mem.write_ne _ _ (by addr), hm6, Mem.write_ne _ _ (by addr), m5HP]
  · rw [hm7, Mem.write_ne _ _ (by addr), hm6, Mem.write_ne _ _ (by addr), m5hdr]
  · rw [hm7, Mem.write_ne _ _ (by addr), m6JJ]
  · rw [hm7, Mem.write_same]

/-- The generic list parser satisfies the contract with `rep = RepListOf rep`. -/
theorem decodeListM_pspec {α : Type} {f : List Bool → Option (α × List Bool)} {rep : Rep α}
    (hgr : GoodRep rep) {elemM : Cmd} {W : List ℕ} {S d : ℕ}
    (hspec : ParserSpec elemM f rep W S d) (hprog : Progress f) (hsuf : SuffixP f)
    (hW : GoodVars W) (l : ℕ) (hl : l ≤ 1)
    (hWl : A_ l ∉ W ∧ NEL l ∉ W ∧ JJ l ∉ W ∧ CC l ∉ W) :
    ParserSpec (decodeListM l elemM) (decodeList f) (RepListOf rep)
      (W ++ natVars ++ [A_ l, NEL l, JJ l, CC l]) (S + 200) (d + 1) := by
  intro m bs p hs hp hpN
  have hhp0 := hs.hp
  -- arithmetic for the cost bound
  obtain ⟨X, hX⟩ : ∃ X, X = bs.length - p + 1 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by omega
  have hXP : X ≤ X ^ (d + 1) := Nat.le_self_pow (by omega) X
  have hXd : X * (S * X ^ d + 14) = S * X ^ (d + 1) + 14 * X := by ring
  have hSP : (S + 200) * X ^ (d + 1) = S * X ^ (d + 1) + 200 * X ^ (d + 1) := by ring
  -- the count
  obtain ⟨m1, k1, e1, hk1, pres1, hs1, hhp1, res1⟩ := decodeNatM_pspec m bs p hs hp hpN
  rw [pow_one, ← hX] at hk1
  have hhp1' := hs1.hp
  unfold PResult at res1
  unfold decodeList
  cases hn : decodeNat (bs.drop p) with
  | none =>
      rw [hn] at res1
      have hok : (Cond.eq OK ONE).eval m1 = false := by simp [Cond.eval, res1, hs1.one]
      refine ⟨m1, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_false hok (Exec.nop m1)), ?_, ?_, hs1, hhp1, ?_⟩
      · rw [← hX, hSP]; omega
      · refine pres1.mono le_rfl (fun x hx => ?_)
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        tauto
      · unfold PResult; rw [bindP_none hn]; exact res1
  | some q =>
      obtain ⟨n, rest1⟩ := q
      rw [hn] at res1
      obtain ⟨hok1, hrep1, hpos1⟩ := res1
      have hv : m1 VAL = n := hrep1
      have hrest1 : rest1 = bs.drop (bs.length - rest1.length) :=
        suffix_drop suffix_decodeNat bs p hpN hn
      have hprog1 : rest1.length < bs.length - p := by
        have := progress_decodeNat _ _ _ hn; simpa using this
      obtain ⟨p1, hp1⟩ : ∃ p1, p1 = bs.length - rest1.length := ⟨_, rfl⟩
      rw [← hp1] at hpos1 hrest1
      have hp1N : p1 ≤ bs.length := by omega
      have hok : (Cond.eq OK ONE).eval m1 = true := by simp [Cond.eval, hok1, hs1.one]
      -- the setup
      obtain ⟨m2, k2, e2, hk2, fr2, m2NEL, m2A, m2HP, m2hdr, m2JJ, m2CC⟩ := listSetup_spec l hl hs1 n hv
      have hs2 : PState m2 bs := by
        refine ⟨hs1.input.of_pres (lo := IN + 1 + bs.length) (W := [NEL l, A_ l, HP, JJ l, CC l])
          ?_ le_rfl ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x hx hxW
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxW
          exact fr2 x hxW.1 hxW.2.1 hxW.2.2.1 hxW.2.2.2.1 hxW.2.2.2.2 (by omega)
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> addr
        · rw [fr2 N (by addr) (by addr) (by addr) (by addr) (by addr) (by addr), hs1.n]
        · rw [fr2 INB (by addr) (by addr) (by addr) (by addr) (by addr) (by addr), hs1.inb]
        · rw [fr2 ONE (by addr) (by addr) (by addr) (by addr) (by addr) (by addr), hs1.one]
        · rw [fr2 ZERO (by addr) (by addr) (by addr) (by addr) (by addr) (by addr), hs1.zero]
        · rw [m2HP]; omega
      have hI : LInv bs l (m1 HP) n 0 p1 m2 := by
        refine ⟨hs2, m2A, m2NEL, m2JJ, ?_, hp1N, ?_, ?_, Nat.zero_le n, by rw [m2HP], hhp1'⟩
        · rw [fr2 POS (by addr) (by addr) (by addr) (by addr) (by addr) (by addr), hpos1]
        · rw [fr2 OK (by addr) (by addr) (by addr) (by addr) (by addr) (by addr), hok1]
        · rw [m2CC, hok1]
      -- the loop
      obtain ⟨m3, k3, e3, fr3, hs3, hhp3, a3, nel3, res3, hk3⟩ :=
        listLoop_spec hgr hspec hprog hsuf hW l hl hWl n bs (m1 HP) n 0 p1 m2 hI (by omega)
      have hk3' : k3 ≤ X * (S * X ^ d + 14) + 2 := by
        have hx : bs.length - p1 + 1 ≤ X := by omega
        have hmono : (bs.length - p1 + 1) ^ d ≤ X ^ d := Nat.pow_le_pow_left hx d
        have h1 : (bs.length - p1 + 1) * (S * (bs.length - p1 + 1) ^ d + 14) ≤ X * (S * X ^ d + 14) :=
          Nat.mul_le_mul hx (by have := Nat.mul_le_mul_left S hmono; omega)
        omega
      unfold LResult at res3
      -- the frame of the whole parser
      have frame : ∀ x, x < m HP → x ∉ HP :: (W ++ natVars ++ [A_ l, NEL l, JJ l, CC l]) →
          m3 x = m x := by
        intro x hx hxW
        have hxHP : x ≠ HP := fun h => hxW (by rw [h]; simp)
        have hxW0 : x ∉ W := fun h => hxW (by simp [h])
        have hxN : x ∉ natVars := fun h => hxW (by simp [h])
        have hxA : x ≠ A_ l := fun h => hxW (by rw [h]; simp)
        have hxNEL : x ≠ NEL l := fun h => hxW (by rw [h]; simp)
        have hxJJ : x ≠ JJ l := fun h => hxW (by rw [h]; simp)
        have hxCC : x ≠ CC l := fun h => hxW (by rw [h]; simp)
        have hxL : x ∉ loopVars l := by
          intro h
          simp only [loopVars, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h | h | h | h | h
          · exact hxJJ h
          · exact hxCC h
          · exact hxN (by rw [h]; decide)
          · exact hxN (by rw [h]; decide)
          · exact hxN (by rw [h]; decide)
          · exact hxHP h
        rw [fr3 x (by omega) hxW0 hxL (by omega), fr2 x hxNEL hxA hxHP hxJJ hxCC (by omega),
          pres1 x hx (by rw [List.mem_cons]; exact fun h => h.elim hxHP hxN)]
      have hhp3' : m HP ≤ m3 HP := by omega
      cases hd : decodeN f n (bs.drop p1) with
      | none =>
          rw [hd] at res3
          have hok3 : (Cond.eq OK ONE).eval m3 = false := by simp [Cond.eval, res3, hs3.one]
          refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hok (Cmd.Exec.seq e2 (Cmd.Exec.seq e3
            (Cmd.Exec.ite_false hok3 (Exec.nop m3))))), ?_, frame, hs3, hhp3', ?_⟩
          · rw [← hX, hSP]; omega
          · unfold PResult; rw [bindP_of_eq hn, hrest1, hd]; exact res3
      | some q =>
          obtain ⟨as, rest⟩ := q
          rw [hd] at res3
          obtain ⟨hok3, hels3, hpos3, _⟩ := res3
          have hlen : as.length = n := decodeN_length f n _ as rest hd
          have hok3' : (Cond.eq OK ONE).eval m3 = true := by simp [Cond.eval, hok3, hs3.one]
          obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write VAL (m1 HP) := ⟨_, rfl⟩
          have e4 : Cmd.Exec (mov VAL (A_ l)) m3 m4 1 := by
            have := Exec.mov VAL (A_ l) m3; rwa [a3, ← hm4] at this
          have q4 : ∀ x, x ≠ VAL → m4 x = m3 x := fun x h => by rw [hm4, Mem.write_ne _ _ h]
          have m4HP : m4 HP = m3 HP := q4 HP (by addr)
          have m4VAL : m4 VAL = m1 HP := by rw [hm4, Mem.write_same]
          have hs4 : PState m4 bs := hs3.of_pres' (by rw [hm4]; exact pres_write _ _ _ _)
            (by intro x hx; simp at hx; subst hx; constructor <;> addr)
          refine ⟨m4, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hok (Cmd.Exec.seq e2 (Cmd.Exec.seq e3
            (Cmd.Exec.ite_true hok3' e4)))), ?_, ?_, hs4, by rw [m4HP]; exact hhp3', ?_⟩
          · rw [← hX, hSP]; omega
          · intro x hx hxW
            have hxV : x ≠ VAL := fun h => hxW (by rw [h]; simp [natVars])
            rw [q4 x hxV, frame x hx hxW]
          · unfold PResult; rw [bindP_of_eq hn, hrest1, hd]
            refine ⟨by rw [q4 OK (by addr), hok3], ?_, by rw [q4 POS (by addr), hpos3]⟩
            rw [m4VAL]
            refine ⟨hhp1, by rw [m4HP, hlen]; omega, ?_, ?_⟩
            · rw [q4 _ (by addr),
                fr3 (m1 HP) (by omega) (fun h => by have := (hW _ h).2; omega) ?_ (by omega), m2hdr, hlen]
              intro h
              simp only [loopVars, List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h | h | h | h | h | h <;> addr
            · intro i hi
              have h1 := hels3 i hi
              simp only [Nat.add_zero] at h1
              have h2 : rep m4 (m2 HP) (m3 HP) (m3 (m1 HP + 1 + i)) as[i] :=
                hgr.frame m3 m4 _ _ _ _ h1 (fun x hx1 _ => q4 x (by addr))
              rw [← q4 (m1 HP + 1 + i) (by addr)] at h2
              exact hgr.mono m4 _ _ _ _ _ _ h2 (by omega) (by rw [m4HP])

end DisequalityDispersion.Machine
