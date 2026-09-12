import MParseList

/-! # A verified library of array routines for the RAM

All data produced by the decision procedure lives in the heap as arrays of naturals
(`arrAt m a = [m (a+1), …, m (a + m a)]`); pairs and records are pointers to small
cell groups.  Routines are specified uniformly:

* `Agree m m' V`: `m'` differs from `m` below the old heap pointer only on the variables
  `V` (and `HP`), and the heap pointer did not decrease — the *persistent heap* discipline;
* `RSpec c V B Pre Post`: from any state satisfying `Pre`, `c` terminates within `B` steps
  and the final state agrees with the initial one off `V` and satisfies `Post`;
* `TestSpec t V B Pre P`: an `RSpec` whose result is the Boolean `P m` in `FLAG`;
* `Stable Pre P V`: the value `P m` only depends on the part of `m` that a routine writing
  `V` leaves alone, so that tests can be run inside loops.

The generic loops (`anyM`, `filterM`, `mapM`, …) take the nesting level `L` selecting a
block of scratch variables, so that loops can be nested without interference. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Scratch variables -/

/-- Boolean result of tests. -/
def FLAG : ℕ := 9
theorem FLAG_eq : FLAG = 9 := rfl
/-- Second result of pair-valued routines (the first is `VAL`). -/
def V2 : ℕ := 17
theorem V2_eq : V2 = 17 := rfl

/-- Scratch variables of nesting level `L` (`L ≤ 9`). -/
def I_ (L : ℕ) : ℕ := 40 + 6 * L
def CNT_ (L : ℕ) : ℕ := 41 + 6 * L
def PTR_ (L : ℕ) : ℕ := 42 + 6 * L
def CONT_ (L : ℕ) : ℕ := 43 + 6 * L
def X_ (L : ℕ) : ℕ := 44 + 6 * L
def OUT_ (L : ℕ) : ℕ := 45 + 6 * L

/-- Decide (in)equalities between fixed addresses (extended). -/
macro "addr'" : tactic => `(tactic| (first | omega | (simp only [A_, NEL, JJ, CC, I_, CNT_, PTR_,
  CONT_, X_, OUT_, FLAG_eq, V2_eq, IN_eq', HP_eq', ONE_eq', POS_eq, OK_eq, VAL_eq, TMP_eq, N_eq, INB_eq,
  ZERO_eq, CNT_eq, POW_eq, PTR_eq, LAST_eq, BIT_eq, J_eq, CONT_eq] at * <;> omega)))

/-! ### Arrays as functions of the memory -/

/-- The array stored at address `a`. -/
def arrAt (m : Mem) (a : ℕ) : List ℕ := (List.range (m a)).map (fun i => m (a + 1 + i))

@[simp] theorem arrAt_length (m : Mem) (a : ℕ) : (arrAt m a).length = m a := by
  simp [arrAt]

theorem arrAt_getElem (m : Mem) (a i : ℕ) (h : i < (arrAt m a).length) :
    (arrAt m a)[i] = m (a + 1 + i) := by
  simp [arrAt]

theorem arrAt_eq_of_Arr {m : Mem} {a : ℕ} {l : List ℕ} (h : Arr m a l) : arrAt m a = l := by
  obtain ⟨h1, h2⟩ := h
  apply List.ext_getElem
  · simp [h1]
  · intro i hi hi'
    rw [arrAt_getElem, h2 i hi']

theorem Arr_of_arrAt {m : Mem} {a : ℕ} {l : List ℕ} (h : arrAt m a = l) : Arr m a l := by
  refine ⟨by rw [← h, arrAt_length], fun i hi => ?_⟩
  have := arrAt_getElem m a i (by rw [h]; exact hi)
  rw [← this]
  simp only [h]

theorem arrAt_congr {m m' : Mem} {a : ℕ} (h : ∀ x, a ≤ x → x ≤ a + m a → m' x = m x) :
    arrAt m' a = arrAt m a := by
  unfold arrAt
  rw [h a le_rfl (by omega)]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact h _ (by omega) (by omega)

/-! ### Agreement and routine specifications -/

/-- `m'` agrees with `m` below the old heap pointer except on `HP :: V`, and the heap
pointer did not decrease. -/
def Agree (m m' : Mem) (V : List ℕ) : Prop := Pres m m' (m HP) (HP :: V) ∧ m HP ≤ m' HP

theorem Agree.refl (m : Mem) (V : List ℕ) : Agree m m V := ⟨Pres.refl _ _ _, le_rfl⟩

theorem Agree.trans {m₁ m₂ m₃ : Mem} {V₁ V₂ : List ℕ} (h₁ : Agree m₁ m₂ V₁)
    (h₂ : Agree m₂ m₃ V₂) : Agree m₁ m₃ (V₁ ++ V₂) := by
  have h12 := h₁.2
  refine ⟨fun x hx hW => ?_, le_trans h₁.2 h₂.2⟩
  simp only [List.mem_cons, List.mem_append, not_or] at hW
  rw [h₂.1 x (by omega) (by simp only [List.mem_cons, not_or]; exact ⟨hW.1, hW.2.2⟩),
    h₁.1 x hx (by simp only [List.mem_cons, not_or]; exact ⟨hW.1, hW.2.1⟩)]

theorem Agree.mono {m m' : Mem} {V V' : List ℕ} (h : Agree m m' V) (hV : ∀ x, x ∈ V → x ∈ V') :
    Agree m m' V' := by
  refine ⟨fun x hx hW => h.1 x hx ?_, h.2⟩
  simp only [List.mem_cons, not_or] at hW ⊢
  exact ⟨hW.1, fun h' => hW.2 (hV x h')⟩

theorem Agree.write (m : Mem) (x v : ℕ) (hx : x ≠ HP) : Agree m (m.write x v) [x] := by
  refine ⟨fun y _ hW => ?_, by rw [Mem.write_ne _ _ (Ne.symm hx)]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hW
  exact Mem.write_ne _ _ hW.2

/-- A variable outside `V` keeps its value (variables lie below the heap pointer). -/
theorem Agree.var {m m' : Mem} {V : List ℕ} (h : Agree m m' V) (x : ℕ) (hx : x < m HP)
    (hHP : x ≠ HP) (hV : x ∉ V) : m' x = m x :=
  h.1 x hx (by simp only [List.mem_cons, not_or]; exact ⟨hHP, hV⟩)

/-- A heap cell below the old heap pointer keeps its value. -/
theorem Agree.heap {m m' : Mem} {V : List ℕ} (h : Agree m m' V) (hV : ∀ x, x ∈ V → x < IN)
    (x : ℕ) (hx : IN ≤ x) (hx' : x < m HP) : m' x = m x :=
  h.1 x hx' (by
    simp only [List.mem_cons, not_or]
    exact ⟨by unfold HP IN at *; omega, fun h' => by have := hV x h'; omega⟩)

/-- An array below the old heap pointer survives. -/
theorem Agree.arrAt {m m' : Mem} {V : List ℕ} (h : Agree m m' V) (hV : ∀ x, x ∈ V → x < IN)
    (a : ℕ) (ha : IN ≤ a) (ha' : a + 1 + m a ≤ m HP) : arrAt m' a = arrAt m a :=
  arrAt_congr (fun x h1 h2 => h.heap hV x (by omega) (by omega))

/-- The routine `c` runs from any state satisfying `Pre` within `B` steps, writing only the
variables `V` and the heap above the heap pointer, and establishes `Post`. -/
def RSpec (c : Cmd) (V : List ℕ) (B : ℕ) (Pre : Mem → Prop) (Post : Mem → Mem → Prop) : Prop :=
  ∀ m, Pre m → ∃ m' k, Cmd.Exec c m m' k ∧ k ≤ B ∧ Agree m m' V ∧ Post m m'

/-- A test computes the Boolean `P m` into `FLAG`. -/
def TestSpec (t : Cmd) (V : List ℕ) (B : ℕ) (Pre : Mem → Prop) (P : Mem → Bool) : Prop :=
  RSpec t V B Pre (fun m m' => m' FLAG = bitv (P m))

/-- `Pre` is stable under changes of the variables `V` and heap growth. -/
def StableP (Pre : Mem → Prop) (V : List ℕ) : Prop :=
  ∀ m m', Pre m → Agree m m' V → Pre m'

/-- `f` is stable under changes of the variables `V` and heap growth (on states satisfying `Pre`). -/
def Stable {α : Type} (Pre : Mem → Prop) (f : Mem → α) (V : List ℕ) : Prop :=
  ∀ m m', Pre m → Agree m m' V → f m' = f m

/-- `f` is stable under changes of `V` and heap growth, on states satisfying `Pre` in which
the element variable `X_ L` holds an element of the array at `SRC`. -/
def StableX {α : Type} (Pre : Mem → Prop) (SRC L : ℕ) (f : Mem → α) (V : List ℕ) : Prop :=
  ∀ m m', Pre m → m (X_ L) ∈ arrAt m (m SRC) → Agree m m' V → f m' = f m

theorem Stable.toX {α : Type} {Pre : Mem → Prop} {f : Mem → α} {V : List ℕ} (h : Stable Pre f V)
    (SRC L : ℕ) : StableX Pre SRC L f V := fun m m' hm _ ha => h m m' hm ha

theorem StableP.mono {Pre : Mem → Prop} {V V' : List ℕ} (h : StableP Pre V)
    (hV : ∀ x, x ∈ V' → x ∈ V) : StableP Pre V' :=
  fun m m' hm ha => h m m' hm (ha.mono hV)

theorem Stable.mono {α : Type} {Pre : Mem → Prop} {f : Mem → α} {V V' : List ℕ}
    (h : Stable Pre f V) (hV : ∀ x, x ∈ V' → x ∈ V) : Stable Pre f V' :=
  fun m m' hm ha => h m m' hm (ha.mono hV)

theorem RSpec.mono {c : Cmd} {V V' : List ℕ} {B B' : ℕ} {Pre Pre' : Mem → Prop}
    {Post Post' : Mem → Mem → Prop} (h : RSpec c V B Pre Post) (hV : ∀ x, x ∈ V → x ∈ V')
    (hB : B ≤ B') (hPre : ∀ m, Pre' m → Pre m) (hPost : ∀ m m', Pre' m → Post m m' → Post' m m') :
    RSpec c V' B' Pre' Post' := by
  intro m hm
  obtain ⟨m', k, e, hk, ha, hp⟩ := h m (hPre m hm)
  exact ⟨m', k, e, by omega, ha.mono hV, hPost m m' hm hp⟩

theorem TestSpec.mono {t : Cmd} {V V' : List ℕ} {B B' : ℕ} {Pre Pre' : Mem → Prop}
    {P : Mem → Bool} (h : TestSpec t V B Pre P) (hV : ∀ x, x ∈ V → x ∈ V') (hB : B ≤ B')
    (hPre : ∀ m, Pre' m → Pre m) : TestSpec t V' B' Pre' P :=
  RSpec.mono h hV hB hPre (fun _ _ _ hp => hp)

/-- The basic context every routine assumes: the constants and a heap pointer above the
variables. -/
def Ctx (m : Mem) : Prop := m ONE = 1 ∧ m ZERO = 0 ∧ IN ≤ m HP

theorem Ctx.of_agree {m m' : Mem} {V : List ℕ} (h : Ctx m) (ha : Agree m m' V)
    (hV : ∀ x, x ∈ V → 5 ≤ x) : Ctx m' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, le_trans h3 ha.2⟩
  · rw [ha.var ONE (by addr') (by addr') (fun h => by have := hV _ h; addr'), h1]
  · rw [ha.var ZERO (by addr') (by addr') (fun h => by have := hV _ h; addr'), h2]


/-! ### Small facts -/

theorem bitv_eq_zero {b : Bool} (h : bitv b = 0) : b = false := by cases b <;> simp_all [bitv]
theorem bitv_eq_one {b : Bool} (h : bitv b = 1) : b = true := by cases b <;> simp_all [bitv]
theorem bitv_ne_zero {b : Bool} (h : bitv b ≠ 0) : b = true := by cases b <;> simp_all [bitv]

theorem any_take_succ {l : List ℕ} {i : ℕ} (h : i < l.length) (f : ℕ → Bool) :
    (l.take (i + 1)).any f = ((l.take i).any f || f l[i]) := by
  rw [List.take_succ_eq_append_getElem h, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem any_of_any_take {l : List ℕ} {i : ℕ} {f : ℕ → Bool} (h : (l.take i).any f = true) :
    l.any f = true := by
  rw [List.any_eq_true] at h ⊢
  obtain ⟨x, hx, hf⟩ := h
  exact ⟨x, List.mem_of_mem_take hx, hf⟩

/-- The scratch variables of level `L`. -/
def Lvars (L : ℕ) : List ℕ := [I_ L, CNT_ L, PTR_ L, CONT_ L, X_ L, OUT_ L]
/-- The scratch variables of level `L` other than the element variable. -/
def LvarsX (L : ℕ) : List ℕ := [I_ L, CNT_ L, PTR_ L, CONT_ L, OUT_ L]

theorem Lvars_range (L : ℕ) (hL : L ≤ 9) : ∀ x, x ∈ Lvars L → 40 ≤ x ∧ x < IN := by
  intro x hx
  simp only [Lvars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> addr'

/-! ### `any` over an array -/

/-- `CONT := 1` iff `I < CNT ∧ FLAG = 0`. -/
def contA (L : ℕ) : Cmd :=
  .ite (.lt (I_ L) (CNT_ L)) (.ite (.eq FLAG ZERO) (setc (CONT_ L) 1) (setc (CONT_ L) 0))
    (setc (CONT_ L) 0)

theorem contA_spec (L : ℕ) (m : Mem) (hz : m ZERO = 0) :
    ∃ k, Cmd.Exec (contA L) m
      (m.write (CONT_ L) (if m (I_ L) < m (CNT_ L) ∧ m FLAG = 0 then 1 else 0)) k ∧ k ≤ 5 := by
  unfold contA
  by_cases h1 : m (I_ L) < m (CNT_ L)
  · have hc : (Cond.lt (I_ L) (CNT_ L)).eval m = true := by simp [Cond.eval, h1]
    by_cases h2 : m FLAG = 0
    · have hc2 : (Cond.eq FLAG ZERO).eval m = true := by simp [Cond.eval, h2, hz]
      rw [if_pos ⟨h1, h2⟩]
      exact ⟨_, Cmd.Exec.ite_true hc (Cmd.Exec.ite_true hc2 (Exec.setc _ _ _)), by omega⟩
    · have hc2 : (Cond.eq FLAG ZERO).eval m = false := by simp [Cond.eval, h2, hz]
      rw [if_neg (fun h => h2 h.2)]
      exact ⟨_, Cmd.Exec.ite_true hc (Cmd.Exec.ite_false hc2 (Exec.setc _ _ _)), by omega⟩
  · have hc : (Cond.lt (I_ L) (CNT_ L)).eval m = false := by simp [Cond.eval, h1]
    rw [if_neg (fun h => h1 h.1)]
    exact ⟨_, Cmd.Exec.ite_false hc (Exec.setc _ _ _), by omega⟩

/-- Does some element of the array at `SRC` satisfy the test `t` (run with the element in
`X_ L`)?  Stops at the first hit. -/
def anyM (L : ℕ) (SRC : ℕ) (t : Cmd) : Cmd :=
  .seq (load (CNT_ L) SRC) (.seq (setc (I_ L) 0) (.seq (setc FLAG 0) (.seq (contA L)
    (.loop (.eq (CONT_ L) ONE)
      (.seq (add (PTR_ L) SRC (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE)
        (.seq (load (X_ L) (PTR_ L)) (.seq t (.seq (add (I_ L) (I_ L) ONE) (contA L))))))))))

/-- The loop invariant of `anyM`. -/
structure AnyInv (L : ℕ) (V : List ℕ) (Pre : Mem → Prop) (P : Mem → Bool) (m0 : Mem)
    (l : List ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ FLAG :: V)
  pre : Pre m
  cnt : m (CNT_ L) = l.length
  hi : m (I_ L) ≤ l.length
  flag : m FLAG = bitv ((l.take (m (I_ L))).any (fun x => P (m0.write (X_ L) x)))
  cont : m (CONT_ L) = if m (I_ L) < l.length ∧ m FLAG = 0 then 1 else 0

theorem anyM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool} (L SRC n : ℕ)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) P) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hSF : SRC ≠ FLAG) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L)
    (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ FLAG :: V))
    (hP : StableX Pre SRC L P (LvarsX L ++ FLAG :: V)) :
    TestSpec (anyM L SRC t) (Lvars L ++ FLAG :: V) (n * (B + 11) + 10) Pre
      (fun m => (arrAt m (m SRC)).any (fun x => P (m.write (X_ L) x))) := by
  intro m0 hm0
  have hLv := Lvars_range L hL
  have hVlt : ∀ x, x ∈ Lvars L ++ FLAG :: V → x < IN := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | h | h
    · exact (hLv x h).2
    · rw [h]; addr'
    · exact (hV x h).2
  have hV5 : ∀ x, x ∈ Lvars L ++ FLAG :: V → 5 ≤ x := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | h | h
    · have := (hLv x h).1; omega
    · rw [h]; addr'
    · exact (hV x h).1
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨hsrc0, harr0, hn0⟩ := harr m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hwrite : ∀ x, Pre (m0.write (X_ L) x) := fun x =>
    hPre m0 _ hm0 ((Agree.write m0 (X_ L) x (by addr')).mono (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; simp [Lvars]))
  have hmemx : ∀ x, x ∈ l → (m0.write (X_ L) x) (X_ L) ∈ arrAt (m0.write (X_ L) x) ((m0.write (X_ L) x) SRC) := by
    intro x hx
    rw [Mem.write_same, Mem.write_ne _ _ (show SRC ≠ X_ L from fun h => hSL (by rw [h]; simp [Lvars]))]
    rw [arrAt_congr (fun y h1 h2 => Mem.write_ne _ _ (show y ≠ X_ L by addr')), hl]
    exact hx
  have hIV : I_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hCV : CNT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  -- the setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (CNT_ L) (m0 (m0 SRC)) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load (CNT_ L) SRC) m0 m1 1 := by rw [hm1]; exact Exec.load _ _ _
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (I_ L) 0 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (setc (I_ L) 0) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write FLAG 0 := ⟨_, rfl⟩
  have e3 : Cmd.Exec (setc FLAG 0) m2 m3 1 := by rw [hm3]; exact Exec.setc _ _ _
  have q3 : ∀ x, x ≠ CNT_ L → x ≠ I_ L → x ≠ FLAG → m3 x = m0 x := fun x h1 h2 h3 => by
    rw [hm3, Mem.write_ne _ _ h3, hm2, Mem.write_ne _ _ h2, hm1, Mem.write_ne _ _ h1]
  have m3I : m3 (I_ L) = 0 := by rw [hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
  have m3C : m3 (CNT_ L) = l.length := by
    rw [hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same, hlen]
  have m3F : m3 FLAG = 0 := by rw [hm3, Mem.write_same]
  have m3Z : m3 ZERO = 0 := by rw [q3 _ (by addr') (by addr') (by addr'), hzero0]
  obtain ⟨k4, e4, hk4⟩ := contA_spec L m3 m3Z
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (CONT_ L) (if m3 (I_ L) < m3 (CNT_ L) ∧ m3 FLAG = 0 then 1 else 0) :=
    ⟨_, rfl⟩
  rw [← hm4] at e4
  have q4 : ∀ x, x ≠ CONT_ L → x ≠ CNT_ L → x ≠ I_ L → x ≠ FLAG → m4 x = m0 x :=
    fun x h0 h1 h2 h3 => by rw [hm4, Mem.write_ne _ _ h0, q3 x h1 h2 h3]
  have agree4 : Agree m0 m4 (Lvars L ++ FLAG :: V) := by
    refine ⟨fun x _ hx => ?_, by rw [q4 HP (by addr') (by addr') (by addr') (by addr')]⟩
    simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hx
    exact q4 x hx.2.1.2.2.2.1 hx.2.1.2.1 hx.2.1.1 hx.2.2.1
  have inv4 : AnyInv L V Pre P m0 l m4 := by
    refine ⟨agree4, hPre m0 m4 hm0 agree4, ?_, ?_, ?_, ?_⟩
    · rw [hm4, Mem.write_ne _ _ (by addr'), m3C]
    · rw [hm4, Mem.write_ne _ _ (by addr'), m3I]; exact Nat.zero_le _
    · rw [hm4, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m3I, m3F]; simp
    · rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m3C]
  -- the loop
  have main := Exec.loop_measure (.eq (CONT_ L) ONE)
    (.seq (add (PTR_ L) SRC (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE)
        (.seq (load (X_ L) (PTR_ L)) (.seq t (.seq (add (I_ L) (I_ L) ONE) (contA L))))))
    (AnyInv L V Pre P m0 l) (fun m => l.length - m (I_ L)) (B + 9) ?_ m4 inv4
  · obtain ⟨m', k, e, inv', hb, hk⟩ := main
    dsimp only at hk
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e))), ?_,
      inv'.agree, ?_⟩
    · have h1 : l.length - m4 (I_ L) ≤ n := by omega
      have h2 : (l.length - m4 (I_ L)) * (B + 9 + 2) ≤ n * (B + 11) :=
        Nat.mul_le_mul_right _ h1
      omega
    · -- the exit condition
      have hone' : m' ONE = 1 := by
        rw [inv'.agree.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
      simp only [Cond.eval, hone', decide_eq_false_iff_not] at hb
      rw [inv'.cont] at hb
      have hfl := inv'.flag
      show m' FLAG = bitv ((arrAt m0 (m0 SRC)).any (fun x => P (m0.write (X_ L) x)))
      by_cases hi : m' (I_ L) < l.length
      · have hf : m' FLAG ≠ 0 := fun h => hb (by rw [if_pos ⟨hi, h⟩])
        rw [hfl] at hf ⊢
        have h1 := bitv_ne_zero hf
        rw [h1, hl, any_of_any_take h1]
      · have hi' : m' (I_ L) = l.length := by have := inv'.hi; omega
        rw [hfl, hi', List.take_length, hl]
  · -- one iteration
    intro m inv hb
    have hone : m ONE = 1 := by
      rw [inv.agree.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    have hzero : m ZERO = 0 := by
      rw [inv.agree.var ZERO (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hzero0]
    have hsrc : m SRC = m0 SRC := inv.agree.var SRC (by addr') (by addr') (by
      simp only [List.mem_append, List.mem_cons, not_or]; exact ⟨hSL, hSF, hSV⟩)
    simp only [Cond.eval, hone, decide_eq_true_eq] at hb
    rw [inv.cont] at hb
    have hcond : m (I_ L) < l.length ∧ m FLAG = 0 := by
      by_contra h; rw [if_neg h] at hb; exact absurd hb (by decide)
    obtain ⟨hi, hfl0⟩ := hcond
    obtain ⟨i, hi_def⟩ : ∃ i, i = m (I_ L) := ⟨_, rfl⟩
    rw [← hi_def] at hi
    have hhp : m0 HP ≤ m HP := inv.agree.2
    have hcell : m (m0 SRC + 1 + i) = l[i]'(by rw [hlen]; omega) := by
      rw [inv.agree.heap hVlt _ (by omega) (by omega),
        ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length]; omega)]
      exact List.getElem_of_eq hl _
    -- PTR := SRC + I; PTR := PTR + 1; X := M[PTR]
    obtain ⟨n1, hn1⟩ : ∃ n1, n1 = m.write (PTR_ L) (m0 SRC + i) := ⟨_, rfl⟩
    have f1 : Cmd.Exec (add (PTR_ L) SRC (I_ L)) m n1 1 := by
      have := Exec.add (PTR_ L) SRC (I_ L) m; rwa [hsrc, ← hi_def, ← hn1] at this
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = n1.write (PTR_ L) (m0 SRC + i + 1) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) n1 n2 1 := by
      have := Exec.add (PTR_ L) (PTR_ L) ONE n1
      rw [hn1, Mem.write_same, Mem.write_ne _ _ (by addr'), hone] at this
      rw [hn2, hn1]; exact this
    have n2cell : n2 (m0 SRC + i + 1) = l[i]'(by rw [hlen]; omega) := by
      rw [hn2, Mem.write_ne _ _ (by addr'), hn1, Mem.write_ne _ _ (by addr'),
        show m0 SRC + i + 1 = m0 SRC + 1 + i by omega, hcell]
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n2.write (X_ L) (l[i]'(by rw [hlen]; omega)) := ⟨_, rfl⟩
    have f3 : Cmd.Exec (load (X_ L) (PTR_ L)) n2 n3 1 := by
      have := Exec.load (X_ L) (PTR_ L) n2
      rw [hn2, Mem.write_same, ← hn2, n2cell] at this
      rw [hn3]; exact this
    have q3 : ∀ x, x ≠ PTR_ L → x ≠ X_ L → n3 x = m x := fun x h1 h2 => by
      rw [hn3, Mem.write_ne _ _ h2, hn2, Mem.write_ne _ _ h1, hn1, Mem.write_ne _ _ h1]
    have n3X : n3 (X_ L) = l[i]'(by rw [hlen]; omega) := by rw [hn3, Mem.write_same]
    have n3HP : n3 HP = m HP := q3 HP (by addr') (by addr')
    have agree3 : Agree m n3 [PTR_ L, X_ L] := by
      refine ⟨fun x _ hx => ?_, by rw [n3HP]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      exact q3 x hx.2.1 hx.2.2
    have pre3 : Pre n3 := hPre m n3 inv.pre (agree3.mono (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.mem_append, Lvars, List.mem_cons]
      rcases hx with rfl | rfl <;> simp))
    -- the test
    have hmem3 : n3 (X_ L) ∈ arrAt n3 (n3 SRC) := by
      rw [n3X, q3 SRC (fun h => hSL (by rw [h]; simp [Lvars])) (fun h => hSL (by rw [h]; simp [Lvars])),
        hsrc, (inv.agree.trans agree3).arrAt (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact hVlt x h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with h | h <;> rw [h] <;> addr') (m0 SRC) hsrc0 harr0, hl]
      exact List.getElem_mem _
    obtain ⟨n4, k4, f4, hk4, agree4, hfl4⟩ := ht n3 ⟨pre3, hmem3⟩
    have hPval : P n3 = P (m0.write (X_ L) (l[i]'(by rw [hlen]; omega))) := by
      refine hP _ _ (hwrite _) (hmemx _ (List.getElem_mem _)) ⟨fun y hy hyV => ?_, ?_⟩
      · simp only [List.mem_cons, not_or] at hyV
        by_cases hyx : y = X_ L
        · rw [hyx, Mem.write_same, n3X]
        · rw [Mem.write_ne _ _ hyx, q3 y (by
            simp only [List.mem_append, LvarsX, List.mem_cons, List.not_mem_nil, or_false, not_or] at hyV
            exact hyV.2.1.2.2.1) hyx]
          exact inv.agree.var y (by rw [Mem.write_ne _ _ (by addr')] at hy; exact hy) hyV.1 (by
            simp only [List.mem_append, List.mem_cons, LvarsX, Lvars, List.not_mem_nil,
              or_false, not_or] at hyV ⊢
            exact ⟨⟨hyV.2.1.1, hyV.2.1.2.1, hyV.2.1.2.2.1, hyV.2.1.2.2.2.1, hyx,
              hyV.2.1.2.2.2.2⟩, hyV.2.2⟩)
      · rw [Mem.write_ne _ _ (by addr'), n3HP]; exact hhp
    have n4I : n4 (I_ L) = i := by
      rw [agree4.var (I_ L) (by have := n3HP; addr') (by addr') hIV,
        q3 _ (by addr') (by addr'), hi_def]
    have n4one : n4 ONE = 1 := by
      rw [agree4.var ONE (by have := n3HP; addr') (by addr') (fun h => by have := hV _ h; addr'),
        q3 _ (by addr') (by addr'), hone]
    have n4zero : n4 ZERO = 0 := by
      rw [agree4.var ZERO (by have := n3HP; addr') (by addr') (fun h => by have := hV _ h; addr'),
        q3 _ (by addr') (by addr'), hzero]
    have n4C : n4 (CNT_ L) = l.length := by
      rw [agree4.var (CNT_ L) (by have := n3HP; addr') (by addr') hCV,
        q3 _ (by addr') (by addr'), inv.cnt]
    -- I := I + 1; contA
    obtain ⟨n5, hn5⟩ : ∃ n5, n5 = n4.write (I_ L) (i + 1) := ⟨_, rfl⟩
    have f5 : Cmd.Exec (add (I_ L) (I_ L) ONE) n4 n5 1 := by
      have := Exec.add (I_ L) (I_ L) ONE n4; rwa [n4I, n4one, ← hn5] at this
    have n5Z : n5 ZERO = 0 := by rw [hn5, Mem.write_ne _ _ (by addr'), n4zero]
    obtain ⟨k6, f6, hk6⟩ := contA_spec L n5 n5Z
    obtain ⟨n6, hn6⟩ : ∃ n6, n6 = n5.write (CONT_ L) (if n5 (I_ L) < n5 (CNT_ L) ∧ n5 FLAG = 0 then 1 else 0) :=
      ⟨_, rfl⟩
    rw [← hn6] at f6
    have q6 : ∀ x, x ≠ CONT_ L → x ≠ I_ L → n6 x = n4 x := fun x h1 h2 => by
      rw [hn6, Mem.write_ne _ _ h1, hn5, Mem.write_ne _ _ h2]
    have n6I : n6 (I_ L) = i + 1 := by rw [hn6, Mem.write_ne _ _ (by addr'), hn5, Mem.write_same]
    have n6F : n6 FLAG = n4 FLAG := q6 FLAG (by addr') (by addr')
    have n6C : n6 (CNT_ L) = l.length := by rw [q6 _ (by addr') (by addr'), n4C]
    have n6HP : n6 HP = n4 HP := q6 HP (by addr') (by addr')
    have agree6 : Agree m0 n6 (Lvars L ++ FLAG :: V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [q6 y hyV'.2.1.2.2.2.1 hyV'.2.1.1, agree4.var y (by rw [n3HP]; omega) hyV'.1 hyV'.2.2.2,
          q3 y hyV'.2.1.2.2.1 hyV'.2.1.2.2.2.2.1]
        exact inv.agree.1 y hy hyV
      · rw [n6HP]; exact le_trans hhp (le_trans (le_of_eq n3HP.symm) agree4.2)
    refine ⟨n6, _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 (Cmd.Exec.seq f3 (Cmd.Exec.seq f4
      (Cmd.Exec.seq f5 f6)))), ?_, by omega, ?_⟩
    · refine ⟨agree6, ?_, n6C, by rw [n6I]; omega, ?_, ?_⟩
      · refine hPre n4 n6 (hPre n3 n4 pre3 (agree4.mono (fun x hx => by
          simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hx)))) ?_
        refine ⟨fun y hy hyV => ?_, by rw [n6HP]⟩
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV
        exact q6 y hyV.2.1.2.2.2.1 hyV.2.1.1
      · rw [n6F, hfl4, hPval, n6I, any_take_succ (by omega)]
        have : (l.take i).any (fun x => P (m0.write (X_ L) x)) = false := by
          have h := inv.flag
          rw [← hi_def, hfl0] at h
          exact (bitv_eq_zero h.symm)
        rw [this, Bool.false_or]
      · rw [n6I, n6F, hn6, Mem.write_same, hn5, Mem.write_same, Mem.write_ne _ _ (by addr'), n4C,
          Mem.write_ne _ _ (by addr')]
    · show l.length - n6 (I_ L) < l.length - m (I_ L)
      rw [n6I]; omega


/-! ### Iteration over an array with a user-supplied invariant -/

theorem Mem.write_write (m : Mem) (a v w : ℕ) : (m.write a v).write a w = m.write a w := by
  funext x; simp only [Mem.write_apply]; split_ifs <;> rfl

/-- `for X in array at SRC do body` (the loop counter is `I_ L`, the length `CNT_ L`, and
`PTR_ L` holds the address of the current element). -/
def forEachM (L SRC : ℕ) (body : Cmd) : Cmd :=
  .seq (load (CNT_ L) SRC) (.seq (setc (I_ L) 0)
    (forLoop (I_ L) (CNT_ L) (.seq (add (PTR_ L) SRC (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE)
      (.seq (load (X_ L) (PTR_ L)) body)))))

theorem forEachM_spec (L SRC : ℕ) (hL : L ≤ 9) (hSRC : SRC < IN) (hSL : SRC ∉ Lvars L)
    (body : Cmd) (Inv : ℕ → Mem → Prop) (a : ℕ) (ha : IN ≤ a) (l : List ℕ) (B : ℕ)
    (hI : ∀ j m, Inv j m → m (I_ L) = j ∧ m (CNT_ L) = l.length ∧ m SRC = a ∧ m ONE = 1 ∧
      a + 1 + l.length ≤ m HP ∧ (∀ i, (h : i < l.length) → m (a + 1 + i) = l[i]))
    (hstable : ∀ j m v w, Inv j m → Inv j ((m.write (PTR_ L) v).write (X_ L) w))
    (hbody : ∀ j m, (h : j < l.length) → Inv j m → m (X_ L) = l[j] → m (PTR_ L) = a + 1 + j →
      ∃ m' k, Cmd.Exec body m m' k ∧ k ≤ B ∧ m' (I_ L) = j ∧ m' ONE = 1 ∧
        Inv (j + 1) (m'.write (I_ L) (j + 1))) :
    ∀ m, m SRC = a → m a = l.length → Inv 0 ((m.write (CNT_ L) l.length).write (I_ L) 0) →
      ∃ m' k, Cmd.Exec (forEachM L SRC body) m m' k ∧ Inv l.length m' ∧
        k ≤ l.length * (B + 6) + 4 := by
  intro m hsrc hlen hinv
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write (CNT_ L) l.length := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load (CNT_ L) SRC) m m1 1 := by
    have := Exec.load (CNT_ L) SRC m; rwa [hsrc, hlen, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (I_ L) 0 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (setc (I_ L) 0) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
  rw [← hm1, ← hm2] at hinv
  have main := forLoop_spec (I_ L) (CNT_ L)
    (.seq (add (PTR_ L) SRC (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE) (.seq (load (X_ L) (PTR_ L)) body)))
    Inv l.length (B + 3) (fun j m hm => ⟨(hI j m hm).1, (hI j m hm).2.1⟩) ?_ 0 m2 (Nat.zero_le _) hinv
  · obtain ⟨m', k, e, hinv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e), hinv', ?_⟩
    have : (l.length - 0) * (B + 3 + 3) = l.length * (B + 6) := by simp
    omega
  · intro j m hj hm
    obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := hI j m hm
    have hSP : SRC ≠ PTR_ L := fun h => hSL (by rw [h]; simp [Lvars])
    obtain ⟨n1, hn1⟩ : ∃ n1, n1 = m.write (PTR_ L) (a + j) := ⟨_, rfl⟩
    have f1 : Cmd.Exec (add (PTR_ L) SRC (I_ L)) m n1 1 := by
      have := Exec.add (PTR_ L) SRC (I_ L) m; rwa [hI3, hI1, ← hn1] at this
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = m.write (PTR_ L) (a + 1 + j) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) n1 n2 1 := by
      have := Exec.add (PTR_ L) (PTR_ L) ONE n1
      rw [hn1, Mem.write_same, Mem.write_ne _ _ (by addr'), hI4, Mem.write_write,
        show a + j + 1 = a + 1 + j by omega] at this
      rw [hn2, hn1]; exact this
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n2.write (X_ L) (l[j]) := ⟨_, rfl⟩
    have f3 : Cmd.Exec (load (X_ L) (PTR_ L)) n2 n3 1 := by
      have := Exec.load (X_ L) (PTR_ L) n2
      rw [hn2, Mem.write_same, Mem.write_ne _ _ (by addr'), hI6 j hj] at this
      rw [hn3, hn2]; exact this
    have inv3 : Inv j n3 := by rw [hn3, hn2]; exact hstable j m _ _ hm
    obtain ⟨m', k, e, hk, hi', hone', hinv'⟩ := hbody j n3 hj inv3 (by rw [hn3, Mem.write_same])
      (by rw [hn3, Mem.write_ne _ _ (by addr'), hn2, Mem.write_same])
    exact ⟨m', _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 (Cmd.Exec.seq f3 e)), by omega, hi', hone', hinv'⟩


/-! ### Pushing onto an array under construction -/

theorem arrAt_push {m m' : Mem} {hdr v : ℕ} (h1 : m' hdr = m hdr + 1)
    (h2 : m' (hdr + 1 + m hdr) = v) (h3 : ∀ i, i < m hdr → m' (hdr + 1 + i) = m (hdr + 1 + i)) :
    arrAt m' hdr = arrAt m hdr ++ [v] := by
  unfold arrAt
  rw [h1, List.range_succ, List.map_append, List.map_singleton, h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact h3 i hi

/-- Append `X_ L` to the array whose header address is in `OUT_ L`. -/
def pushM (L : ℕ) : Cmd :=
  .seq (load (CONT_ L) (OUT_ L)) (.seq (add (PTR_ L) (OUT_ L) (CONT_ L))
    (.seq (add (PTR_ L) (PTR_ L) ONE) (.seq (store (PTR_ L) (X_ L))
      (.seq (add (CONT_ L) (CONT_ L) ONE) (store (OUT_ L) (CONT_ L))))))

theorem pushM_spec (L : ℕ) (hL : L ≤ 9) (m : Mem) (hdr : ℕ) (hout : m (OUT_ L) = hdr)
    (hone : m ONE = 1) (hhdr : IN ≤ hdr) :
    ∃ m' k, Cmd.Exec (pushM L) m m' k ∧ k ≤ 6 ∧
      (∀ x, x ≠ CONT_ L → x ≠ PTR_ L → x ≠ hdr → x ≠ hdr + 1 + m hdr → m' x = m x) ∧
      m' hdr = m hdr + 1 ∧ m' (hdr + 1 + m hdr) = m (X_ L) := by
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write (CONT_ L) (m hdr) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load (CONT_ L) (OUT_ L)) m m1 1 := by
    have := Exec.load (CONT_ L) (OUT_ L) m; rwa [hout, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (PTR_ L) (hdr + m hdr) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add (PTR_ L) (OUT_ L) (CONT_ L)) m1 m2 1 := by
    have := Exec.add (PTR_ L) (OUT_ L) (CONT_ L) m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr'), hout] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m1.write (PTR_ L) (hdr + 1 + m hdr) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) m2 m3 1 := by
    have := Exec.add (PTR_ L) (PTR_ L) ONE m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hone,
      Mem.write_write, show hdr + m hdr + 1 = hdr + 1 + m hdr by omega] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (hdr + 1 + m hdr) (m (X_ L)) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (store (PTR_ L) (X_ L)) m3 m4 1 := by
    have := Exec.store (PTR_ L) (X_ L) m3
    rw [hm3, Mem.write_same, Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr')] at this
    rw [hm4, hm3, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (CONT_ L) (m hdr + 1) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add (CONT_ L) (CONT_ L) ONE) m4 m5 1 := by
    have := Exec.add (CONT_ L) (CONT_ L) ONE m4
    rw [hm4, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'),
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_same, Mem.write_ne _ _ (by addr'), hone] at this
    rw [hm5, hm4, hm3, hm1]; exact this
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write hdr (m hdr + 1) := ⟨_, rfl⟩
  have e6 : Cmd.Exec (store (OUT_ L) (CONT_ L)) m5 m6 1 := by
    have := Exec.store (OUT_ L) (CONT_ L) m5
    rw [hm5, Mem.write_same, Mem.write_ne _ _ (by addr'), hm4, Mem.write_ne _ _ (by addr'), hm3,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hout] at this
    rw [hm6, hm5, hm4, hm3, hm1]; exact this
  refine ⟨m6, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
    (Cmd.Exec.seq e5 e6)))), by omega, ?_, ?_, ?_⟩
  · intro x h1 h2 h3 h4
    rw [hm6, Mem.write_ne _ _ h3, hm5, Mem.write_ne _ _ h1, hm4, Mem.write_ne _ _ h4, hm3,
      Mem.write_ne _ _ h2, hm1, Mem.write_ne _ _ h1]
  · rw [hm6, Mem.write_same]
  · rw [hm6, Mem.write_ne _ _ (by omega), hm5, Mem.write_ne _ _ (by addr'), hm4, Mem.write_same]

/-! ### `filter` -/

/-- The elements of the array at `SRC` satisfying `t`, as a fresh array (address in `OUT_ L`). -/
def filterM (L SRC : ℕ) (t : Cmd) : Cmd :=
  .seq (mov (OUT_ L) HP) (.seq (store (OUT_ L) ZERO) (.seq (load (CONT_ L) SRC)
    (.seq (add HP HP (CONT_ L)) (.seq (add HP HP ONE)
      (forEachM L SRC (.seq t (.ite (.eq FLAG ONE) (pushM L) nop)))))))

/-- The loop invariant of `filterM`. -/
structure FilterInv (L : ℕ) (V : List ℕ) (Pre : Mem → Prop) (P : Mem → Bool) (m0 : Mem)
    (a : ℕ) (l : List ℕ) (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ FLAG :: V)
  pre : Pre m
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = m0 HP
  arr : arrAt m (m0 HP) = (l.take j).filter (fun x => P (m0.write (X_ L) x))
  room : m0 HP + 1 + l.length ≤ m HP

theorem filterM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool} (L SRC n : ℕ)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) P) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hSF : SRC ≠ FLAG) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hXV : X_ L ∉ V)
    (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ FLAG :: V))
    (hP : StableX Pre SRC L P (LvarsX L ++ FLAG :: V)) :
    RSpec (filterM L SRC t) (Lvars L ++ FLAG :: V) (n * (B + 14) + 9) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧
        arrAt m' (m HP) = (arrAt m (m SRC)).filter (fun x => P (m.write (X_ L) x)) ∧
        m HP + 1 + m (m SRC) ≤ m' HP) := by
  intro m0 hm0
  have hLv := Lvars_range L hL
  have hVlt : ∀ x, x ∈ Lvars L ++ FLAG :: V → x < IN := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | h | h
    · exact (hLv x h).2
    · rw [h]; addr'
    · exact (hV x h).2
  have hV5 : ∀ x, x ∈ Lvars L ++ FLAG :: V → 5 ≤ x := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | h | h
    · have := (hLv x h).1; omega
    · rw [h]; addr'
    · exact (hV x h).1
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨hsrc0, harr0, hn0⟩ := harr m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hwrite : ∀ x, Pre (m0.write (X_ L) x) := fun x =>
    hPre m0 _ hm0 ((Agree.write m0 (X_ L) x (by addr')).mono (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; simp [Lvars]))
  have hmemx : ∀ x, x ∈ l → (m0.write (X_ L) x) (X_ L) ∈ arrAt (m0.write (X_ L) x) ((m0.write (X_ L) x) SRC) := by
    intro x hx
    rw [Mem.write_same, Mem.write_ne _ _ (show SRC ≠ X_ L from fun h => hSL (by rw [h]; simp [Lvars]))]
    rw [arrAt_congr (fun y h1 h2 => Mem.write_ne _ _ (show y ≠ X_ L by addr')), hl]
    exact hx
  have hIV : I_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hCV : CNT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hOV : OUT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hSP : SRC ≠ PTR_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSX : SRC ≠ X_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSO : SRC ≠ OUT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSC : SRC ≠ CONT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSI : SRC ≠ I_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSCN : SRC ≠ CNT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  -- the setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ L) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ L) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write hdr 0 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (store (OUT_ L) ZERO) m1 m2 1 := by
    have := Exec.store (OUT_ L) ZERO m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr'), hzero0] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (CONT_ L) l.length := ⟨_, rfl⟩
  have e3 : Cmd.Exec (load (CONT_ L) SRC) m2 m3 1 := by
    have := Exec.load (CONT_ L) SRC m2
    rw [hm2, Mem.write_ne _ _ (show SRC ≠ hdr by addr'), hm1, Mem.write_ne _ _ hSO,
      Mem.write_ne _ _ (show m0 SRC ≠ hdr by omega), Mem.write_ne _ _ (by addr'), ← hlen] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + l.length) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (CONT_ L)) m3 m4 1 := by
    have := Exec.add HP HP (CONT_ L) m3
    rw [hm3, Mem.write_same, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1,
      Mem.write_ne _ _ (by addr'), ← hhdr] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m3.write HP (hdr + 1 + l.length) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hone0, Mem.write_write,
      show hdr + l.length + 1 = hdr + 1 + l.length by omega] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  have q5 : ∀ x, x ≠ HP → x ≠ CONT_ L → x ≠ hdr → x ≠ OUT_ L → m5 x = m0 x := fun x h1 h2 h3 h4 => by
    rw [hm5, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h2, hm2, Mem.write_ne _ _ h3, hm1,
      Mem.write_ne _ _ h4]
  have m5HP : m5 HP = hdr + 1 + l.length := by rw [hm5, Mem.write_same]
  have m5hdr : m5 hdr = 0 := by
    rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
  have agree5 : Agree m0 m5 (Lvars L ++ FLAG :: V) := by
    refine ⟨fun x hx hxV => ?_, by rw [m5HP]; omega⟩
    simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hxV
    obtain ⟨h0, ⟨_, _, _, h4, _, h6⟩, _, _⟩ := hxV
    exact q5 x h0 h4 (by omega) h6
  -- the loop
  have hf : ∀ (m : Mem) (x : ℕ), Agree m0 m (Lvars L ++ FLAG :: V) → m (X_ L) = x → x ∈ l →
      P m = P (m0.write (X_ L) x) := by
    intro m x hag hx hxl
    refine hP _ _ (hwrite x) (hmemx x hxl) ⟨fun y hy hyV => ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hyV
      by_cases hyx : y = X_ L
      · rw [hyx, Mem.write_same, hx]
      · rw [Mem.write_ne _ _ hyx]
        exact hag.var y (by rw [Mem.write_ne _ _ (by addr')] at hy; exact hy) hyV.1 (by
          simp only [List.mem_append, List.mem_cons, LvarsX, Lvars, List.not_mem_nil,
            or_false, not_or] at hyV ⊢
          exact ⟨⟨hyV.2.1.1, hyV.2.1.2.1, hyV.2.1.2.2.1, hyV.2.1.2.2.2.1, hyx,
            hyV.2.1.2.2.2.2⟩, hyV.2.2⟩)
    · rw [Mem.write_ne _ _ (by addr')]; exact hag.2
  have main := forEachM_spec L SRC hL hSRC.2 hSL (.seq t (.ite (.eq FLAG ONE) (pushM L) nop))
    (FilterInv L V Pre P m0 (m0 SRC) l) (m0 SRC) hsrc0 l (B + 8) ?_ ?_ ?_ m5
    (by rw [q5 SRC (by addr') hSC (by addr') hSO]) (by
      rw [q5 (m0 SRC) (by addr') (by addr') (by omega) (by addr'), hlen]) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 e)))), ?_, inv'.agree, ?_⟩
    · have h1 : l.length * (B + 8 + 6) ≤ n * (B + 14) := Nat.mul_le_mul_right _ (by omega)
      omega
    · refine ⟨inv'.out, ?_, ?_⟩
      · rw [inv'.arr, List.take_length, hl]
      · rw [← hlen]; exact inv'.room
  · -- hI
    intro j m hm
    obtain ⟨hag, hpre, hi, hcnt, hout, harr', hroom⟩ := hm
    refine ⟨hi, hcnt, ?_, ?_, ?_, ?_⟩
    · rw [hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, List.mem_cons, not_or]; exact ⟨hSL, hSF, hSV⟩)]
    · rw [hag.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    · exact le_trans (by rw [hlen]; exact harr0) hag.2
    · intro i hi'
      rw [hag.heap hVlt _ (by omega) (by omega),
        ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length, ← hlen]; exact hi')]
      exact List.getElem_of_eq hl _
  · -- hstable
    intro j m v w hm
    obtain ⟨hag, hpre, hi, hcnt, hout, harr', hroom⟩ := hm
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    have hsub : ∀ x, x ∈ [PTR_ L, X_ L] → x ∈ Lvars L ++ FLAG :: V := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [Lvars]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · exact hsub x h),
      hPre m _ hpre (hag'.mono hsub), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout]
    · rw [← harr']
      apply arrAt_congr
      intro x h1 h2
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom
  · -- hbody
    intro j m hj hm hx hptr
    obtain ⟨hag, hpre, hi, hcnt, hout, harr', hroom⟩ := hm
    have hhp : m0 HP ≤ m HP := hag.2
    -- the test
    have hmem : m (X_ L) ∈ arrAt m (m SRC) := by
      rw [hx, hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, List.mem_cons, not_or]; exact ⟨hSL, hSF, hSV⟩),
        hag.arrAt hVlt (m0 SRC) hsrc0 harr0, hl]
      exact List.getElem_mem hj
    obtain ⟨n1, k1, f1, hk1, agree1, hfl1⟩ := ht m ⟨hpre, hmem⟩
    have hPv : P m = P (m0.write (X_ L) l[j]) := hf m _ hag hx (List.getElem_mem hj)
    have n1HP : m HP ≤ n1 HP := agree1.2
    have v1 : ∀ x, x < IN → x ≠ HP → x ∉ V → n1 x = m x := fun x hx' hxH hxV =>
      agree1.var x (lt_of_lt_of_le hx' (le_trans hhp0 hhp)) hxH hxV
    have n1one : n1 ONE = 1 := by
      rw [v1 ONE (by addr') (by addr') (fun h => by have := hV _ h; addr'),
        hag.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    have n1I : n1 (I_ L) = j := by rw [v1 _ (by addr') (by addr') hIV, hi]
    have n1C : n1 (CNT_ L) = l.length := by rw [v1 _ (by addr') (by addr') hCV, hcnt]
    have n1O : n1 (OUT_ L) = hdr := by rw [v1 _ (by addr') (by addr') hOV, hout, hhdr]
    have n1X : n1 (X_ L) = l[j] := by rw [v1 _ (by addr') (by addr') hXV, hx]
    have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
    have hmhdr : m hdr = ((l.take j).filter (fun x => P (m0.write (X_ L) x))).length := by
      rw [← harr', hhdr, arrAt_length]
    have hmhdr' : m hdr ≤ j := by
      rw [hmhdr]; exact le_trans (List.length_filter_le _ _) (by simp)
    have harr1 : arrAt n1 hdr = (l.take j).filter (fun x => P (m0.write (X_ L) x)) := by
      rw [← harr', hhdr]
      exact agree1.arrAt (fun x hx => (hV x hx).2) _ hhp0 (by rw [← hhdr]; omega)
    -- the conditional push
    have hcases : ∃ n2 k2, Cmd.Exec (.ite (.eq FLAG ONE) (pushM L) nop) n1 n2 k2 ∧ k2 ≤ 8 ∧
        (∀ x, x < hdr → x ≠ CONT_ L → x ≠ PTR_ L → n2 x = n1 x) ∧ n2 HP = n1 HP ∧
        arrAt n2 hdr = (l.take (j + 1)).filter (fun x => P (m0.write (X_ L) x)) := by
      rw [hPv] at hfl1
      cases hfx : P (m0.write (X_ L) l[j]) with
      | true =>
          rw [hfx] at hfl1
          have hc : (Cond.eq FLAG ONE).eval n1 = true := by simp [Cond.eval, hfl1, n1one]
          obtain ⟨n2, k2, f2, hk2, fr2, hdr2, cell2⟩ := pushM_spec L hL n1 hdr n1O n1one hhdrIN
          refine ⟨n2, _, Cmd.Exec.ite_true hc f2, by omega, ?_, ?_, ?_⟩
          · intro x hx h1 h2; exact fr2 x h1 h2 (by omega) (by omega)
          · exact fr2 HP (by addr') (by addr') (by addr') (by addr')
          · rw [List.take_succ_eq_append_getElem hj, List.filter_append,
              List.filter_singleton, hfx, cond_true, ← harr1, ← n1X]
            exact arrAt_push hdr2 cell2 (fun i hi' => fr2 _ (by addr') (by addr') (by omega) (by omega))
      | false =>
          rw [hfx] at hfl1
          have hc : (Cond.eq FLAG ONE).eval n1 = false := by simp [Cond.eval, hfl1, n1one]
          refine ⟨n1, _, Cmd.Exec.ite_false hc (Exec.nop n1), by omega, fun _ _ _ _ => rfl, rfl, ?_⟩
          rw [List.take_succ_eq_append_getElem hj, List.filter_append, List.filter_singleton, hfx,
            cond_false, List.append_nil, harr1]
    obtain ⟨n2, k2, f2, hk2, fr2, hp2, arr2⟩ := hcases
    have n2I : n2 (I_ L) = j := by rw [fr2 _ (by addr') (by addr') (by addr'), n1I]
    have n2one : n2 ONE = 1 := by rw [fr2 _ (by addr') (by addr') (by addr'), n1one]
    have n2C : n2 (CNT_ L) = l.length := by rw [fr2 _ (by addr') (by addr') (by addr'), n1C]
    have n2O : n2 (OUT_ L) = hdr := by rw [fr2 _ (by addr') (by addr') (by addr'), n1O]
    refine ⟨n2, _, Cmd.Exec.seq f1 f2, by omega, n2I, n2one, ?_⟩
    have agree' : Agree m0 (n2.write (I_ L) (j + 1)) (Lvars L ++ FLAG :: V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, fr2 y (by omega) hyV'.2.1.2.2.2.1 hyV'.2.1.2.2.1,
          agree1.var y (by omega) hyV'.1 hyV'.2.2.2]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), hp2]; omega
    refine ⟨agree', hPre m0 _ hm0 agree', by rw [Mem.write_same], ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), n2C]
    · rw [Mem.write_ne _ _ (by addr'), n2O, hhdr]
    · rw [← hhdr, ← arr2]
      apply arrAt_congr
      intro x _ _
      rw [Mem.write_ne _ _ (by addr')]
    · rw [Mem.write_ne _ _ (by addr'), hp2, ← hhdr]; omega
  · -- the initial invariant
    have agree6 : Agree m0 ((m5.write (CNT_ L) l.length).write (I_ L) 0) (Lvars L ++ FLAG :: V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, Mem.write_ne _ _ hyV'.2.1.2.1]
        exact agree5.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact agree5.2
    have m5O : m5 (OUT_ L) = hdr := by
      rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
        Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
    refine ⟨agree6, hPre m0 _ hm0 agree6, by rw [Mem.write_same], ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_same]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5O, hhdr]
    · rw [List.take_zero, List.filter_nil, ← hhdr]
      simp only [arrAt, Mem.write_ne _ _ (show hdr ≠ I_ L by addr'),
        Mem.write_ne _ _ (show hdr ≠ CNT_ L by addr'), m5hdr, List.range_zero, List.map_nil]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5HP, hhdr]


/-! ### `map` -/

/-- A routine computing the value `F m` into `VAL`. -/
def FunSpec (c : Cmd) (V : List ℕ) (B : ℕ) (Pre : Mem → Prop) (F : Mem → ℕ) : Prop :=
  RSpec c V B Pre (fun m m' => m' VAL = F m)

theorem arrAt_of_cells {m : Mem} {hdr : ℕ} {l : List ℕ} (h1 : m hdr = l.length)
    (h2 : ∀ i, (h : i < l.length) → m (hdr + 1 + i) = l[i]) : arrAt m hdr = l :=
  arrAt_eq_of_Arr ⟨h1, h2⟩

/-- The images of the elements of the array at `SRC` under `c` (result in `VAL`), as a fresh
array of the same length (address in `OUT_ L`). -/
def mapM (L SRC : ℕ) (c : Cmd) : Cmd :=
  .seq (mov (OUT_ L) HP) (.seq (load (CONT_ L) SRC) (.seq (store (OUT_ L) (CONT_ L))
    (.seq (add HP HP (CONT_ L)) (.seq (add HP HP ONE)
      (forEachM L SRC (.seq c (.seq (add (PTR_ L) (OUT_ L) (I_ L))
        (.seq (add (PTR_ L) (PTR_ L) ONE) (store (PTR_ L) VAL)))))))))

/-- The loop invariant of `mapM`. -/
structure MapInv (L : ℕ) (V : List ℕ) (Pre : Mem → Prop) (F : Mem → ℕ) (m0 : Mem)
    (l : List ℕ) (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ V)
  pre : Pre m
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = m0 HP
  hdr : m (m0 HP) = l.length
  cells : ∀ i, (h : i < l.length) → i < j → m (m0 HP + 1 + i) = F (m0.write (X_ L) l[i])
  room : m0 HP + 1 + l.length ≤ m HP

theorem mapM_spec {c : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {F : Mem → ℕ} (L SRC n : ℕ)
    (hc : FunSpec c V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) F) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L)
    (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ V))
    (hF : StableX Pre SRC L F (LvarsX L ++ V)) :
    RSpec (mapM L SRC c) (Lvars L ++ V) (n * (B + 9) + 9) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧
        arrAt m' (m HP) = (arrAt m (m SRC)).map (fun x => F (m.write (X_ L) x)) ∧
        m HP + 1 + m (m SRC) ≤ m' HP) := by
  intro m0 hm0
  have hLv := Lvars_range L hL
  have hVlt : ∀ x, x ∈ Lvars L ++ V → x < IN := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact (hLv x h).2
    · exact (hV x h).2
  have hV5 : ∀ x, x ∈ Lvars L ++ V → 5 ≤ x := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · have := (hLv x h).1; omega
    · exact (hV x h).1
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨hsrc0, harr0, hn0⟩ := harr m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hwrite : ∀ x, Pre (m0.write (X_ L) x) := fun x =>
    hPre m0 _ hm0 ((Agree.write m0 (X_ L) x (by addr')).mono (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; simp [Lvars]))
  have hmemx : ∀ x, x ∈ l → (m0.write (X_ L) x) (X_ L) ∈ arrAt (m0.write (X_ L) x) ((m0.write (X_ L) x) SRC) := by
    intro x hx
    rw [Mem.write_same, Mem.write_ne _ _ (show SRC ≠ X_ L from fun h => hSL (by rw [h]; simp [Lvars]))]
    rw [arrAt_congr (fun y h1 h2 => Mem.write_ne _ _ (show y ≠ X_ L by addr')), hl]
    exact hx
  have hIV : I_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hCV : CNT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hOV : OUT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hSO : SRC ≠ OUT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSC : SRC ≠ CONT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  -- the setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ L) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ L) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (CONT_ L) l.length := ⟨_, rfl⟩
  have e2 : Cmd.Exec (load (CONT_ L) SRC) m1 m2 1 := by
    have := Exec.load (CONT_ L) SRC m1
    rw [hm1, Mem.write_ne _ _ hSO, Mem.write_ne _ _ (by addr'), ← hlen] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write hdr l.length := ⟨_, rfl⟩
  have e3 : Cmd.Exec (store (OUT_ L) (CONT_ L)) m2 m3 1 := by
    have := Exec.store (OUT_ L) (CONT_ L) m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + l.length) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (CONT_ L)) m3 m4 1 := by
    have := Exec.add HP HP (CONT_ L) m3
    rw [hm3, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm2, Mem.write_same,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), ← hhdr] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m3.write HP (hdr + 1 + l.length) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hone0, Mem.write_write,
      show hdr + l.length + 1 = hdr + 1 + l.length by omega] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  have q5 : ∀ x, x ≠ HP → x ≠ CONT_ L → x ≠ hdr → x ≠ OUT_ L → m5 x = m0 x := fun x h1 h2 h3 h4 => by
    rw [hm5, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h3, hm2, Mem.write_ne _ _ h2, hm1,
      Mem.write_ne _ _ h4]
  have m5HP : m5 HP = hdr + 1 + l.length := by rw [hm5, Mem.write_same]
  have m5hdr : m5 hdr = l.length := by
    rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
  have m5O : m5 (OUT_ L) = hdr := by
    rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
  have agree5 : Agree m0 m5 (Lvars L ++ V) := by
    refine ⟨fun x hx hxV => ?_, by rw [m5HP]; omega⟩
    simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hxV
    obtain ⟨h0, ⟨_, _, _, h4, _, h6⟩, _⟩ := hxV
    exact q5 x h0 h4 (by omega) h6
  -- stability of `F`
  have hf : ∀ (m : Mem) (x : ℕ), Agree m0 m (Lvars L ++ V) → m (X_ L) = x → x ∈ l →
      F m = F (m0.write (X_ L) x) := by
    intro m x hag hx hxl
    refine hF _ _ (hwrite x) (hmemx x hxl) ⟨fun y hy hyV => ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hyV
      by_cases hyx : y = X_ L
      · rw [hyx, Mem.write_same, hx]
      · rw [Mem.write_ne _ _ hyx]
        exact hag.var y (by rw [Mem.write_ne _ _ (by addr')] at hy; exact hy) hyV.1 (by
          simp only [List.mem_append, List.mem_cons, LvarsX, Lvars, List.not_mem_nil,
            or_false, not_or] at hyV ⊢
          exact ⟨⟨hyV.2.1.1, hyV.2.1.2.1, hyV.2.1.2.2.1, hyV.2.1.2.2.2.1, hyx,
            hyV.2.1.2.2.2.2⟩, hyV.2.2⟩)
    · rw [Mem.write_ne _ _ (by addr')]; exact hag.2
  have main := forEachM_spec L SRC hL hSRC.2 hSL
    (.seq c (.seq (add (PTR_ L) (OUT_ L) (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE) (store (PTR_ L) VAL))))
    (MapInv L V Pre F m0 l) (m0 SRC) hsrc0 l (B + 3) ?_ ?_ ?_ m5
    (by rw [q5 SRC (by addr') hSC (by addr') hSO]) (by
      rw [q5 (m0 SRC) (by addr') (by addr') (by omega) (by addr'), hlen]) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 e)))), ?_, inv'.agree, ?_⟩
    · have h1 : l.length * (B + 3 + 6) ≤ n * (B + 9) := Nat.mul_le_mul_right _ (by omega)
      omega
    · refine ⟨inv'.out, ?_, ?_⟩
      · rw [hl]
        apply arrAt_of_cells
        · rw [inv'.hdr, List.length_map]
        · intro i hi
          rw [List.length_map] at hi
          rw [List.getElem_map, inv'.cells i hi hi]
      · rw [← hlen]; exact inv'.room
  · -- hI
    intro j m hm
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    refine ⟨hi, hcnt, ?_, ?_, ?_, ?_⟩
    · rw [hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, not_or]; exact ⟨hSL, hSV⟩)]
    · rw [hag.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    · exact le_trans (by rw [hlen]; exact harr0) hag.2
    · intro i hi'
      rw [hag.heap hVlt _ (by omega) (by omega),
        ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length, ← hlen]; exact hi')]
      exact List.getElem_of_eq hl _
  · -- hstable
    intro j m v w hm
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    have hsub : ∀ x, x ∈ [PTR_ L, X_ L] → x ∈ Lvars L ++ V := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [Lvars]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · exact hsub x h),
      hPre m _ hpre (hag'.mono hsub), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hhdr']
    · intro i hi1 hi2
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcells i hi1 hi2]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom
  · -- hbody
    intro j m hj hm hx hptr
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    have hhp : m0 HP ≤ m HP := hag.2
    have hmem : m (X_ L) ∈ arrAt m (m SRC) := by
      rw [hx, hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, not_or]; exact ⟨hSL, hSV⟩),
        hag.arrAt hVlt (m0 SRC) hsrc0 harr0, hl]
      exact List.getElem_mem hj
    obtain ⟨n1, k1, f1, hk1, agree1, hval1⟩ := hc m ⟨hpre, hmem⟩
    have hFv : F m = F (m0.write (X_ L) l[j]) := hf m _ hag hx (List.getElem_mem hj)
    have n1HP : m HP ≤ n1 HP := agree1.2
    have v1 : ∀ x, x < IN → x ≠ HP → x ∉ V → n1 x = m x := fun x hx' hxH hxV =>
      agree1.var x (lt_of_lt_of_le hx' (le_trans hhp0 hhp)) hxH hxV
    have n1one : n1 ONE = 1 := by
      rw [v1 ONE (by addr') (by addr') (fun h => by have := hV _ h; addr'),
        hag.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    have n1I : n1 (I_ L) = j := by rw [v1 _ (by addr') (by addr') hIV, hi]
    have n1C : n1 (CNT_ L) = l.length := by rw [v1 _ (by addr') (by addr') hCV, hcnt]
    have n1O : n1 (OUT_ L) = hdr := by rw [v1 _ (by addr') (by addr') hOV, hout, hhdr]
    have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
    -- PTR := OUT + I + 1; M[PTR] := VAL
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = n1.write (PTR_ L) (hdr + j) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (PTR_ L) (OUT_ L) (I_ L)) n1 n2 1 := by
      have := Exec.add (PTR_ L) (OUT_ L) (I_ L) n1; rwa [n1O, n1I, ← hn2] at this
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n1.write (PTR_ L) (hdr + 1 + j) := ⟨_, rfl⟩
    have f3 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) n2 n3 1 := by
      have := Exec.add (PTR_ L) (PTR_ L) ONE n2
      rw [hn2, Mem.write_same, Mem.write_ne _ _ (by addr'), n1one, Mem.write_write,
        show hdr + j + 1 = hdr + 1 + j by omega] at this
      rw [hn3, hn2]; exact this
    obtain ⟨n4, hn4⟩ : ∃ n4, n4 = n3.write (hdr + 1 + j) (F (m0.write (X_ L) l[j])) := ⟨_, rfl⟩
    have f4 : Cmd.Exec (store (PTR_ L) VAL) n3 n4 1 := by
      have := Exec.store (PTR_ L) VAL n3
      rw [hn3, Mem.write_same, Mem.write_ne _ _ (by addr'), hval1, hFv] at this
      rw [hn4, hn3]; exact this
    have q4 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → n4 x = n1 x := fun x h1 h2 => by
      rw [hn4, Mem.write_ne _ _ h2, hn3, Mem.write_ne _ _ h1]
    have n4HP : n4 HP = n1 HP := q4 HP (by addr') (by addr')
    refine ⟨n4, _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 (Cmd.Exec.seq f3 f4)), by omega,
      by rw [q4 _ (by addr') (by addr'), n1I], by rw [q4 _ (by addr') (by addr'), n1one], ?_⟩
    have agree' : Agree m0 (n4.write (I_ L) (j + 1)) (Lvars L ++ V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, q4 y hyV'.2.1.2.2.1 (by omega),
          agree1.var y (by omega) hyV'.1 hyV'.2.2]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), n4HP]; omega
    refine ⟨agree', hPre m0 _ hm0 agree', by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), q4 _ (by addr') (by addr'), n1C]
    · rw [Mem.write_ne _ _ (by addr'), q4 _ (by addr') (by addr'), n1O, hhdr]
    · rw [Mem.write_ne _ _ (by addr'), ← hhdr, q4 _ (by addr') (by omega),
        agree1.heap (fun x hx => (hV x hx).2) _ hhdrIN (by omega), hhdr, hhdr']
    · intro i hi1 hi2
      rw [Mem.write_ne _ _ (by addr'), ← hhdr]
      by_cases hij : i = j
      · subst hij; rw [hn4, Mem.write_same]
      · rw [q4 _ (by addr') (by omega), agree1.heap (fun x hx => (hV x hx).2) _ (by omega) (by omega),
          hhdr, hcells i hi1 (by omega)]
    · rw [Mem.write_ne _ _ (by addr'), n4HP]; omega
  · -- the initial invariant
    have agree6 : Agree m0 ((m5.write (CNT_ L) l.length).write (I_ L) 0) (Lvars L ++ V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, Mem.write_ne _ _ hyV'.2.1.2.1]
        exact agree5.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact agree5.2
    refine ⟨agree6, hPre m0 _ hm0 agree6, by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_same]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5O, hhdr]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), ← hhdr, m5hdr]
    · intro i _ hi2; exact absurd hi2 (Nat.not_lt_zero _)
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5HP, hhdr]


/-! ### Elementary tests and their combinators -/

theorem Agree.write_flag (m : Mem) (v : ℕ) : Agree m (m.write FLAG v) [FLAG] :=
  Agree.write m FLAG v (by addr')

/-- `FLAG := (M[a] = M[b])`. -/
def eqTest (a b : ℕ) : Cmd := .ite (.eq a b) (setc FLAG 1) (setc FLAG 0)

theorem eqTest_spec (a b : ℕ) (Pre : Mem → Prop) :
    TestSpec (eqTest a b) [FLAG] 3 Pre (fun m => decide (m a = m b)) := by
  intro m _
  dsimp only
  unfold eqTest
  by_cases h : m a = m b
  · have hc : (Cond.eq a b).eval m = true := by simp [Cond.eval, h]
    exact ⟨_, _, Cmd.Exec.ite_true hc (Exec.setc _ _ _), by omega, Agree.write_flag m 1,
      by rw [Mem.write_same]; simp [h, bitv]⟩
  · have hc : (Cond.eq a b).eval m = false := by simp [Cond.eval, h]
    exact ⟨_, _, Cmd.Exec.ite_false hc (Exec.setc _ _ _), by omega, Agree.write_flag m 0,
      by rw [Mem.write_same]; simp [h, bitv]⟩

/-- `FLAG := (M[a] < M[b])`. -/
def ltTest (a b : ℕ) : Cmd := .ite (.lt a b) (setc FLAG 1) (setc FLAG 0)

theorem ltTest_spec (a b : ℕ) (Pre : Mem → Prop) :
    TestSpec (ltTest a b) [FLAG] 3 Pre (fun m => decide (m a < m b)) := by
  intro m _
  dsimp only
  unfold ltTest
  by_cases h : m a < m b
  · have hc : (Cond.lt a b).eval m = true := by simp [Cond.eval, h]
    exact ⟨_, _, Cmd.Exec.ite_true hc (Exec.setc _ _ _), by omega, Agree.write_flag m 1,
      by rw [Mem.write_same]; simp [h, bitv]⟩
  · have hc : (Cond.lt a b).eval m = false := by simp [Cond.eval, h]
    exact ⟨_, _, Cmd.Exec.ite_false hc (Exec.setc _ _ _), by omega, Agree.write_flag m 0,
      by rw [Mem.write_same]; simp [h, bitv]⟩

/-- Negation of a test: `FLAG := 1 - FLAG`. -/
def notM (t : Cmd) : Cmd := .seq t (sub FLAG ONE FLAG)

theorem notM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool}
    (ht : TestSpec t V B Pre P) (hV : ∀ x, x ∈ V → 5 ≤ x) (hctx : ∀ m, Pre m → Ctx m) :
    TestSpec (notM t) (FLAG :: V) (B + 1) Pre (fun m => !P m) := by
  intro m hm
  dsimp only
  obtain ⟨m1, k1, e1, hk1, ag1, hfl1⟩ := ht m hm
  have hone : m1 ONE = 1 := by
    rw [ag1.var ONE (by have := (hctx m hm).2.2; addr') (by addr') (fun h => by have := hV _ h; addr')]
    exact (hctx m hm).1
  have e2 : Cmd.Exec (sub FLAG ONE FLAG) m1 (m1.write FLAG (1 - bitv (P m))) 1 := by
    have := Exec.sub FLAG ONE FLAG m1; rwa [hone, hfl1] at this
  refine ⟨m1.write FLAG (1 - bitv (P m)), _, Cmd.Exec.seq e1 e2, by omega, ?_, ?_⟩
  · exact (ag1.trans (Agree.write_flag m1 _)).mono (fun x hx => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  · rw [Mem.write_same]; cases P m <;> simp [bitv]

/-- Short-circuit conjunction of tests. -/
def andM (t₁ t₂ : Cmd) : Cmd := .seq t₁ (.ite (.eq FLAG ONE) t₂ nop)

theorem andM_spec {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {P₁ P₂ : Mem → Bool} (h₁ : TestSpec t₁ V₁ B₁ Pre P₁) (h₂ : TestSpec t₂ V₂ B₂ Pre P₂)
    (hV₁ : ∀ x, x ∈ V₁ → 5 ≤ x) (hctx : ∀ m, Pre m → Ctx m)
    (hPre : StableP Pre V₁) (hP₂ : Stable Pre P₂ V₁) :
    TestSpec (andM t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 3) Pre (fun m => P₁ m && P₂ m) := by
  intro m hm
  dsimp only
  obtain ⟨m1, k1, e1, hk1, ag1, hfl1⟩ := h₁ m hm
  have hone : m1 ONE = 1 := by
    rw [ag1.var ONE (by have := (hctx m hm).2.2; addr') (by addr') (fun h => by have := hV₁ _ h; addr')]
    exact (hctx m hm).1
  cases hp : P₁ m with
  | true =>
      rw [hp] at hfl1
      have hc : (Cond.eq FLAG ONE).eval m1 = true := by simp [Cond.eval, hfl1, hone]
      obtain ⟨m2, k2, e2, hk2, ag2, hfl2⟩ := h₂ m1 (hPre m m1 hm ag1)
      refine ⟨m2, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc e2), by omega, ag1.trans ag2, ?_⟩
      rw [hfl2, hP₂ m m1 hm ag1, Bool.true_and]
  | false =>
      rw [hp] at hfl1
      have hc : (Cond.eq FLAG ONE).eval m1 = false := by simp [Cond.eval, hfl1, hone]
      refine ⟨m1, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_false hc (Exec.nop m1)), by omega,
        ag1.mono (fun x hx => List.mem_append_left _ hx), ?_⟩
      rw [hfl1, Bool.false_and]

/-- Short-circuit disjunction of tests. -/
def orM (t₁ t₂ : Cmd) : Cmd := .seq t₁ (.ite (.eq FLAG ONE) nop t₂)

theorem orM_spec {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {P₁ P₂ : Mem → Bool} (h₁ : TestSpec t₁ V₁ B₁ Pre P₁) (h₂ : TestSpec t₂ V₂ B₂ Pre P₂)
    (hV₁ : ∀ x, x ∈ V₁ → 5 ≤ x) (hctx : ∀ m, Pre m → Ctx m)
    (hPre : StableP Pre V₁) (hP₂ : Stable Pre P₂ V₁) :
    TestSpec (orM t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 3) Pre (fun m => P₁ m || P₂ m) := by
  intro m hm
  dsimp only
  obtain ⟨m1, k1, e1, hk1, ag1, hfl1⟩ := h₁ m hm
  have hone : m1 ONE = 1 := by
    rw [ag1.var ONE (by have := (hctx m hm).2.2; addr') (by addr') (fun h => by have := hV₁ _ h; addr')]
    exact (hctx m hm).1
  cases hp : P₁ m with
  | false =>
      rw [hp] at hfl1
      have hc : (Cond.eq FLAG ONE).eval m1 = false := by simp [Cond.eval, hfl1, hone]
      obtain ⟨m2, k2, e2, hk2, ag2, hfl2⟩ := h₂ m1 (hPre m m1 hm ag1)
      refine ⟨m2, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_false hc e2), by omega, ag1.trans ag2, ?_⟩
      rw [hfl2, hP₂ m m1 hm ag1, Bool.false_or]
  | true =>
      rw [hp] at hfl1
      have hc : (Cond.eq FLAG ONE).eval m1 = true := by simp [Cond.eval, hfl1, hone]
      refine ⟨m1, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc (Exec.nop m1)), by omega,
        ag1.mono (fun x hx => List.mem_append_left _ hx), ?_⟩
      rw [hfl1, Bool.true_or]


/-! ### Arrays of pairs (pointers to two-cell records) -/

/-- The list of pairs stored (as pointers to two-cell records) in the array at `a`. -/
def pairsAt (m : Mem) (a : ℕ) : List (ℕ × ℕ) := (arrAt m a).map (fun q => (m q, m (q + 1)))

/-- The records pointed to from the array at `a` lie in `[lo, hi)`. -/
def RecsIn (m : Mem) (a lo hi : ℕ) : Prop := ∀ q, q ∈ arrAt m a → lo ≤ q ∧ q + 2 ≤ hi

theorem pairsAt_congr {m m' : Mem} {a : ℕ} (h1 : arrAt m' a = arrAt m a)
    (h2 : ∀ q, q ∈ arrAt m a → m' q = m q ∧ m' (q + 1) = m (q + 1)) :
    pairsAt m' a = pairsAt m a := by
  unfold pairsAt
  rw [h1]
  apply List.map_congr_left
  intro q hq
  rw [(h2 q hq).1, (h2 q hq).2]

theorem Agree.pairsAt {m m' : Mem} {V : List ℕ} (h : Agree m m' V) (hV : ∀ x, x ∈ V → x < IN)
    (a : ℕ) (ha : IN ≤ a) (ha' : a + 1 + m a ≤ m HP) (hrec : RecsIn m a IN (m HP)) :
    pairsAt m' a = pairsAt m a := by
  refine pairsAt_congr (h.arrAt hV a ha ha') (fun q hq => ?_)
  obtain ⟨hq1, hq2⟩ := hrec q hq
  exact ⟨h.heap hV q hq1 (by omega), h.heap hV (q + 1) (by omega) (by omega)⟩

theorem RecsIn.of_agree {m m' : Mem} {V : List ℕ} (h : Agree m m' V) (hV : ∀ x, x ∈ V → x < IN)
    {a lo hi : ℕ} (ha : IN ≤ a) (ha' : a + 1 + m a ≤ m HP) (hrec : RecsIn m a lo hi) :
    RecsIn m' a lo hi := by
  intro q hq
  rw [h.arrAt hV a ha ha'] at hq
  exact hrec q hq

theorem RecsIn.mono {m : Mem} {a lo hi lo' hi' : ℕ} (h : RecsIn m a lo hi) (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : RecsIn m a lo' hi' := fun q hq => ⟨le_trans h1 (h q hq).1, le_trans (h q hq).2 h2⟩

/-- A routine computing the pair `F m` into `(VAL, V2)`. -/
def FunSpec2 (c : Cmd) (V : List ℕ) (B : ℕ) (Pre : Mem → Prop) (F : Mem → ℕ × ℕ) : Prop :=
  RSpec c V B Pre (fun m m' => (m' VAL, m' V2) = F m)

/-- The images of the elements of the array at `SRC` under the pair-valued `c`, as a fresh
array of pointers to fresh two-cell records (address in `OUT_ L`). -/
def mapPairM (L SRC : ℕ) (c : Cmd) : Cmd :=
  .seq (mov (OUT_ L) HP) (.seq (load (CONT_ L) SRC) (.seq (store (OUT_ L) (CONT_ L))
    (.seq (add HP HP (CONT_ L)) (.seq (add HP HP ONE)
      (forEachM L SRC (.seq c (.seq (add (PTR_ L) (OUT_ L) (I_ L))
        (.seq (add (PTR_ L) (PTR_ L) ONE) (.seq (store (PTR_ L) HP)
          (.seq (store HP VAL) (.seq (add HP HP ONE) (.seq (store HP V2) (add HP HP ONE)))))))))))))

/-- The loop invariant of `mapPairM`. -/
structure MapPairInv (L : ℕ) (V : List ℕ) (Pre : Mem → Prop) (F : Mem → ℕ × ℕ) (m0 : Mem)
    (hdr : ℕ) (l : List ℕ) (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ V)
  pre : Pre m
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = hdr
  hd : m hdr = l.length
  cells : ∀ i, (h : i < l.length) → i < j →
    hdr + 1 + l.length ≤ m (hdr + 1 + i) ∧ m (hdr + 1 + i) + 2 ≤ m HP ∧
    (m (m (hdr + 1 + i)), m (m (hdr + 1 + i) + 1)) = F (m0.write (X_ L) l[i])
  room : hdr + 1 + l.length ≤ m HP

theorem mapPairM_spec {c : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {F : Mem → ℕ × ℕ} (L SRC n : ℕ)
    (hc : FunSpec2 c V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) F) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L)
    (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ V))
    (hF : StableX Pre SRC L F (LvarsX L ++ V)) :
    RSpec (mapPairM L SRC c) (Lvars L ++ V) (n * (B + 14) + 9) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧
        pairsAt m' (m HP) = (arrAt m (m SRC)).map (fun x => F (m.write (X_ L) x)) ∧
        RecsIn m' (m HP) (m HP + 1 + m (m SRC)) (m' HP) ∧
        m HP + 1 + m (m SRC) ≤ m' HP) := by
  intro m0 hm0
  have hLv := Lvars_range L hL
  have hVlt : ∀ x, x ∈ Lvars L ++ V → x < IN := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact (hLv x h).2
    · exact (hV x h).2
  have hV5 : ∀ x, x ∈ Lvars L ++ V → 5 ≤ x := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · have := (hLv x h).1; omega
    · exact (hV x h).1
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨hsrc0, harr0, hn0⟩ := harr m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hwrite : ∀ x, Pre (m0.write (X_ L) x) := fun x =>
    hPre m0 _ hm0 ((Agree.write m0 (X_ L) x (by addr')).mono (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy; simp [Lvars]))
  have hmemx : ∀ x, x ∈ l → (m0.write (X_ L) x) (X_ L) ∈ arrAt (m0.write (X_ L) x) ((m0.write (X_ L) x) SRC) := by
    intro x hx
    rw [Mem.write_same, Mem.write_ne _ _ (show SRC ≠ X_ L from fun h => hSL (by rw [h]; simp [Lvars]))]
    rw [arrAt_congr (fun y h1 h2 => Mem.write_ne _ _ (show y ≠ X_ L by addr')), hl]
    exact hx
  have hIV : I_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hCV : CNT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hOV : OUT_ L ∉ V := fun h => hVL _ h (by simp [LvarsX])
  have hSO : SRC ≠ OUT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSC : SRC ≠ CONT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  -- the setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ L) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ L) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (CONT_ L) l.length := ⟨_, rfl⟩
  have e2 : Cmd.Exec (load (CONT_ L) SRC) m1 m2 1 := by
    have := Exec.load (CONT_ L) SRC m1
    rw [hm1, Mem.write_ne _ _ hSO, Mem.write_ne _ _ (by addr'), ← hlen] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write hdr l.length := ⟨_, rfl⟩
  have e3 : Cmd.Exec (store (OUT_ L) (CONT_ L)) m2 m3 1 := by
    have := Exec.store (OUT_ L) (CONT_ L) m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + l.length) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (CONT_ L)) m3 m4 1 := by
    have := Exec.add HP HP (CONT_ L) m3
    rw [hm3, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm2, Mem.write_same,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), ← hhdr] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m3.write HP (hdr + 1 + l.length) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hone0, Mem.write_write,
      show hdr + l.length + 1 = hdr + 1 + l.length by omega] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  have q5 : ∀ x, x ≠ HP → x ≠ CONT_ L → x ≠ hdr → x ≠ OUT_ L → m5 x = m0 x := fun x h1 h2 h3 h4 => by
    rw [hm5, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h3, hm2, Mem.write_ne _ _ h2, hm1,
      Mem.write_ne _ _ h4]
  have m5HP : m5 HP = hdr + 1 + l.length := by rw [hm5, Mem.write_same]
  have m5hdr : m5 hdr = l.length := by
    rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
  have m5O : m5 (OUT_ L) = hdr := by
    rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
  have agree5 : Agree m0 m5 (Lvars L ++ V) := by
    refine ⟨fun x hx hxV => ?_, by rw [m5HP]; omega⟩
    simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hxV
    obtain ⟨h0, ⟨_, _, _, h4, _, h6⟩, _⟩ := hxV
    exact q5 x h0 h4 (by omega) h6
  -- stability of `F`
  have hf : ∀ (m : Mem) (x : ℕ), Agree m0 m (Lvars L ++ V) → m (X_ L) = x → x ∈ l →
      F m = F (m0.write (X_ L) x) := by
    intro m x hag hx hxl
    refine hF _ _ (hwrite x) (hmemx x hxl) ⟨fun y hy hyV => ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hyV
      by_cases hyx : y = X_ L
      · rw [hyx, Mem.write_same, hx]
      · rw [Mem.write_ne _ _ hyx]
        exact hag.var y (by rw [Mem.write_ne _ _ (by addr')] at hy; exact hy) hyV.1 (by
          simp only [List.mem_append, List.mem_cons, LvarsX, Lvars, List.not_mem_nil,
            or_false, not_or] at hyV ⊢
          exact ⟨⟨hyV.2.1.1, hyV.2.1.2.1, hyV.2.1.2.2.1, hyV.2.1.2.2.2.1, hyx,
            hyV.2.1.2.2.2.2⟩, hyV.2.2⟩)
    · rw [Mem.write_ne _ _ (by addr')]; exact hag.2
  have main := forEachM_spec L SRC hL hSRC.2 hSL
    (.seq c (.seq (add (PTR_ L) (OUT_ L) (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE) (.seq (store (PTR_ L) HP)
      (.seq (store HP VAL) (.seq (add HP HP ONE) (.seq (store HP V2) (add HP HP ONE))))))))
    (MapPairInv L V Pre F m0 hdr l) (m0 SRC) hsrc0 l (B + 8) ?_ ?_ ?_ m5
    (by rw [q5 SRC (by addr') hSC (by addr') hSO]) (by
      rw [q5 (m0 SRC) (by addr') (by addr') (by omega) (by addr'), hlen]) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 e)))), ?_, inv'.agree, ?_⟩
    · have h1 : l.length * (B + 8 + 6) ≤ n * (B + 14) := Nat.mul_le_mul_right _ (by omega)
      omega
    · have harr' : arrAt m' hdr = (List.range l.length).map (fun i => m' (hdr + 1 + i)) := by
        unfold arrAt; rw [inv'.hd]
      show m' (OUT_ L) = m0 HP ∧ pairsAt m' (m0 HP) = (arrAt m0 (m0 SRC)).map (fun x => F (m0.write (X_ L) x)) ∧
        RecsIn m' (m0 HP) (m0 HP + 1 + m0 (m0 SRC)) (m' HP) ∧ m0 HP + 1 + m0 (m0 SRC) ≤ m' HP
      rw [← hhdr]
      refine ⟨inv'.out, ?_, ?_, ?_⟩
      · rw [hl]
        unfold pairsAt
        rw [harr', List.map_map]
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.length_map, List.length_range] at h1
        simp only [List.getElem_map, List.getElem_range, Function.comp]
        exact (inv'.cells i h1 h1).2.2
      · intro q hq
        rw [harr', List.mem_map] at hq
        obtain ⟨i, hi, rfl⟩ := hq
        rw [List.mem_range] at hi
        rw [← hlen]
        exact ⟨(inv'.cells i hi hi).1, (inv'.cells i hi hi).2.1⟩
      · rw [← hlen]; exact inv'.room
  · -- hI
    intro j m hm
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    refine ⟨hi, hcnt, ?_, ?_, ?_, ?_⟩
    · rw [hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, not_or]; exact ⟨hSL, hSV⟩)]
    · rw [hag.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    · exact le_trans (by rw [hlen]; exact harr0) hag.2
    · intro i hi'
      rw [hag.heap hVlt _ (by omega) (by omega),
        ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length, ← hlen]; exact hi')]
      exact List.getElem_of_eq hl _
  · -- hstable
    intro j m v w hm
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    have hsub : ∀ x, x ∈ [PTR_ L, X_ L] → x ∈ Lvars L ++ V := by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp [Lvars]
    have hw : ∀ x, IN ≤ x → ((m.write (PTR_ L) v).write (X_ L) w) x = m x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · exact hsub x h),
      hPre m _ hpre (hag'.mono hsub), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout]
    · rw [hw hdr (by omega), hhdr']
    · intro i hi1 hi2
      obtain ⟨c1, c2, c3⟩ := hcells i hi1 hi2
      rw [hw (hdr + 1 + i) (by omega), hw (m (hdr + 1 + i)) (by omega),
        hw (m (hdr + 1 + i) + 1) (by omega), Mem.write_ne _ _ (show HP ≠ X_ L by addr'),
        Mem.write_ne _ _ (show HP ≠ PTR_ L by addr')]
      exact ⟨c1, c2, c3⟩
    · rw [Mem.write_ne _ _ (show HP ≠ X_ L by addr'), Mem.write_ne _ _ (show HP ≠ PTR_ L by addr')]
      exact hroom
  · -- hbody
    intro j m hj hm hx hptr
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    have hhp : m0 HP ≤ m HP := hag.2
    have hmem : m (X_ L) ∈ arrAt m (m SRC) := by
      rw [hx, hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, not_or]; exact ⟨hSL, hSV⟩),
        hag.arrAt hVlt (m0 SRC) hsrc0 harr0, hl]
      exact List.getElem_mem hj
    obtain ⟨n1, k1, f1, hk1, agree1, hval1⟩ := hc m ⟨hpre, hmem⟩
    have hFv : F m = F (m0.write (X_ L) l[j]) := hf m _ hag hx (List.getElem_mem hj)
    have n1HP : m HP ≤ n1 HP := agree1.2
    have v1 : ∀ x, x < IN → x ≠ HP → x ∉ V → n1 x = m x := fun x hx' hxH hxV =>
      agree1.var x (lt_of_lt_of_le hx' (le_trans hhp0 hhp)) hxH hxV
    have n1one : n1 ONE = 1 := by
      rw [v1 ONE (by addr') (by addr') (fun h => by have := hV _ h; addr'),
        hag.var ONE (by addr') (by addr') (fun h => by have := hV5 _ h; addr'), hone0]
    have n1I : n1 (I_ L) = j := by rw [v1 _ (by addr') (by addr') hIV, hi]
    have n1C : n1 (CNT_ L) = l.length := by rw [v1 _ (by addr') (by addr') hCV, hcnt]
    have n1O : n1 (OUT_ L) = hdr := by rw [v1 _ (by addr') (by addr') hOV, hout, hhdr]
    have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
    have hheap1 : ∀ x, IN ≤ x → x < m HP → n1 x = m x := fun x h1 h2 =>
      agree1.heap (fun x hx => (hV x hx).2) x h1 h2
    obtain ⟨r, hr⟩ : ∃ r, r = n1 HP := ⟨_, rfl⟩
    have hr1 : hdr + 1 + l.length ≤ r := by rw [hr]; omega
    -- PTR := OUT + I + 1; M[PTR] := HP; M[HP] := VAL; HP += 1; M[HP] := V2; HP += 1
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = n1.write (PTR_ L) (hdr + j) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (PTR_ L) (OUT_ L) (I_ L)) n1 n2 1 := by
      have := Exec.add (PTR_ L) (OUT_ L) (I_ L) n1; rwa [n1O, n1I, ← hn2] at this
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n1.write (PTR_ L) (hdr + 1 + j) := ⟨_, rfl⟩
    have f3 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) n2 n3 1 := by
      have := Exec.add (PTR_ L) (PTR_ L) ONE n2
      rw [hn2, Mem.write_same, Mem.write_ne _ _ (by addr'), n1one, Mem.write_write,
        show hdr + j + 1 = hdr + 1 + j by omega] at this
      rw [hn3, hn2]; exact this
    obtain ⟨n4, hn4⟩ : ∃ n4, n4 = n3.write (hdr + 1 + j) r := ⟨_, rfl⟩
    have f4 : Cmd.Exec (store (PTR_ L) HP) n3 n4 1 := by
      have := Exec.store (PTR_ L) HP n3
      rw [hn3, Mem.write_same, Mem.write_ne _ _ (by addr'), ← hr] at this
      rw [hn4, hn3]; exact this
    have q4 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → n4 x = n1 x := fun x h1 h2 => by
      rw [hn4, Mem.write_ne _ _ h2, hn3, Mem.write_ne _ _ h1]
    obtain ⟨n5, hn5⟩ : ∃ n5, n5 = n4.write r (n1 VAL) := ⟨_, rfl⟩
    have f5 : Cmd.Exec (store HP VAL) n4 n5 1 := by
      have := Exec.store HP VAL n4
      rw [q4 HP (by addr') (by addr'), q4 VAL (by addr') (by addr'), ← hr] at this
      rw [hn5]; exact this
    have q5 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → x ≠ r → n5 x = n1 x := fun x h1 h2 h3 => by
      rw [hn5, Mem.write_ne _ _ h3, q4 x h1 h2]
    obtain ⟨n6, hn6⟩ : ∃ n6, n6 = n5.write HP (r + 1) := ⟨_, rfl⟩
    have f6 : Cmd.Exec (add HP HP ONE) n5 n6 1 := by
      have := Exec.add HP HP ONE n5
      rw [q5 HP (by addr') (by addr') (by addr'), q5 ONE (by addr') (by addr') (by addr'), n1one,
        ← hr] at this
      rw [hn6]; exact this
    have q6 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → x ≠ r → x ≠ HP → n6 x = n1 x := fun x h1 h2 h3 h4 => by
      rw [hn6, Mem.write_ne _ _ h4, q5 x h1 h2 h3]
    obtain ⟨n7, hn7⟩ : ∃ n7, n7 = n6.write (r + 1) (n1 V2) := ⟨_, rfl⟩
    have f7 : Cmd.Exec (store HP V2) n6 n7 1 := by
      have := Exec.store HP V2 n6
      rw [hn6, Mem.write_same, Mem.write_ne _ _ (by addr'), q5 V2 (by addr') (by addr') (by addr')] at this
      rw [hn7, hn6]; exact this
    have q7 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → x ≠ r → x ≠ HP → x ≠ r + 1 → n7 x = n1 x :=
      fun x h1 h2 h3 h4 h5 => by rw [hn7, Mem.write_ne _ _ h5, q6 x h1 h2 h3 h4]
    obtain ⟨n8, hn8⟩ : ∃ n8, n8 = n7.write HP (r + 2) := ⟨_, rfl⟩
    have f8 : Cmd.Exec (add HP HP ONE) n7 n8 1 := by
      have := Exec.add HP HP ONE n7
      rw [hn7, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hn6, Mem.write_same,
        Mem.write_ne _ _ (by addr'), q5 ONE (by addr') (by addr') (by addr'), n1one] at this
      rw [hn8, hn7, hn6]; exact this
    have q8 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → x ≠ r → x ≠ HP → x ≠ r + 1 → n8 x = n1 x :=
      fun x h1 h2 h3 h4 h5 => by rw [hn8, Mem.write_ne _ _ h4, q7 x h1 h2 h3 h4 h5]
    have n8HP : n8 HP = r + 2 := by rw [hn8, Mem.write_same]
    have n8slot : n8 (hdr + 1 + j) = r := by
      rw [hn8, Mem.write_ne _ _ (by addr'), hn7, Mem.write_ne _ _ (by omega), hn6,
        Mem.write_ne _ _ (by addr'), hn5, Mem.write_ne _ _ (by omega), hn4, Mem.write_same]
    have n8r : n8 r = n1 VAL := by
      rw [hn8, Mem.write_ne _ _ (by addr'), hn7, Mem.write_ne _ _ (by omega), hn6,
        Mem.write_ne _ _ (by addr'), hn5, Mem.write_same]
    have n8r1 : n8 (r + 1) = n1 V2 := by
      rw [hn8, Mem.write_ne _ _ (by addr'), hn7, Mem.write_same]
    refine ⟨n8, _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 (Cmd.Exec.seq f3 (Cmd.Exec.seq f4
      (Cmd.Exec.seq f5 (Cmd.Exec.seq f6 (Cmd.Exec.seq f7 f8)))))), by omega,
      by rw [q8 _ (by addr') (by addr') (by addr') (by addr') (by addr'), n1I],
      by rw [q8 _ (by addr') (by addr') (by addr') (by addr') (by addr'), n1one], ?_⟩
    have agree' : Agree m0 (n8.write (I_ L) (j + 1)) (Lvars L ++ V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, q8 y hyV'.2.1.2.2.1 (by omega) (by omega) hyV'.1 (by omega),
          agree1.var y (by omega) hyV'.1 hyV'.2.2]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), n8HP]; omega
    have hw : ∀ x, IN ≤ x → (n8.write (I_ L) (j + 1)) x = n8 x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr')]
    refine ⟨agree', hPre m0 _ hm0 agree', by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), q8 _ (by addr') (by addr') (by addr') (by addr') (by addr'), n1C]
    · rw [Mem.write_ne _ _ (by addr'), q8 _ (by addr') (by addr') (by addr') (by addr') (by addr'), n1O]
    · rw [hw hdr (by omega), q8 _ (by addr') (by omega) (by omega) (by addr') (by omega),
        hheap1 _ hhdrIN (by omega), hhdr']
    · intro i hi1 hi2
      rw [hw (hdr + 1 + i) (by omega)]
      by_cases hij : i = j
      · subst hij
        rw [n8slot, hw r (by omega), hw (r + 1) (by omega), n8r, n8r1, hval1, hFv,
          Mem.write_ne _ _ (show HP ≠ I_ L by addr'), n8HP]
        exact ⟨by omega, by omega, rfl⟩
      · have hslot : n8 (hdr + 1 + i) = m (hdr + 1 + i) := by
          rw [q8 _ (by addr') (by omega) (by omega) (by addr') (by omega), hheap1 _ (by omega) (by omega)]
        obtain ⟨c1, c2, c3⟩ := hcells i hi1 (by omega)
        rw [hslot, hw (m (hdr + 1 + i)) (by omega), hw (m (hdr + 1 + i) + 1) (by omega),
          Mem.write_ne _ _ (show HP ≠ I_ L by addr'), n8HP]
        refine ⟨c1, by omega, ?_⟩
        rw [← c3, q8 _ (by addr') (by omega) (by omega) (by addr') (by omega),
          q8 _ (by addr') (by omega) (by omega) (by addr') (by omega),
          hheap1 _ (by omega) (by omega), hheap1 _ (by omega) (by omega)]
    · rw [Mem.write_ne _ _ (show HP ≠ I_ L by addr'), n8HP]; omega
  · -- the initial invariant
    have agree6 : Agree m0 ((m5.write (CNT_ L) l.length).write (I_ L) 0) (Lvars L ++ V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, Mem.write_ne _ _ hyV'.2.1.2.1]
        exact agree5.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact agree5.2
    refine ⟨agree6, hPre m0 _ hm0 agree6, by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_same]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5O]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5hdr]
    · intro i _ hi2; exact absurd hi2 (Nat.not_lt_zero _)
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5HP]


/-! ### `range` -/

/-- The array `[0, …, M[N] - 1]` (address in `OUT_ L`). -/
def rangeM (L N : ℕ) : Cmd :=
  .seq (mov (OUT_ L) HP) (.seq (mov (CNT_ L) N) (.seq (store (OUT_ L) (CNT_ L))
    (.seq (add HP HP (CNT_ L)) (.seq (add HP HP ONE) (.seq (setc (I_ L) 0)
      (forLoop (I_ L) (CNT_ L) (.seq (add (PTR_ L) (OUT_ L) (I_ L))
        (.seq (add (PTR_ L) (PTR_ L) ONE) (store (PTR_ L) (I_ L))))))))))

theorem rangeM_spec (L N n : ℕ) (hL : L ≤ 9) (hN : 5 ≤ N ∧ N < IN) (hNL : N ∉ Lvars L)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hn : ∀ m, Pre m → m N ≤ n) :
    RSpec (rangeM L N) (Lvars L) (n * 6 + 8) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧ arrAt m' (m HP) = List.range (m N) ∧
        m HP + 1 + m N ≤ m' HP) := by
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  have hn0 := hn m0 hm0
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = m0 N := ⟨_, rfl⟩
  have hNO : N ≠ OUT_ L := fun h => hNL (by rw [h]; simp [Lvars])
  have hNC : N ≠ CNT_ L := fun h => hNL (by rw [h]; simp [Lvars])
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ L) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ L) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (CNT_ L) c := ⟨_, rfl⟩
  have e2 : Cmd.Exec (mov (CNT_ L) N) m1 m2 1 := by
    have := Exec.mov (CNT_ L) N m1
    rw [hm1, Mem.write_ne _ _ hNO, ← hc] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write hdr c := ⟨_, rfl⟩
  have e3 : Cmd.Exec (store (OUT_ L) (CNT_ L)) m2 m3 1 := by
    have := Exec.store (OUT_ L) (CNT_ L) m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + c) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (CNT_ L)) m3 m4 1 := by
    have := Exec.add HP HP (CNT_ L) m3
    rw [hm3, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm2, Mem.write_same,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), ← hhdr] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m3.write HP (hdr + 1 + c) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hone0, Mem.write_write,
      show hdr + c + 1 = hdr + 1 + c by omega] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write (I_ L) 0 := ⟨_, rfl⟩
  have e6 : Cmd.Exec (setc (I_ L) 0) m5 m6 1 := by rw [hm6]; exact Exec.setc _ _ _
  have q6 : ∀ x, x ≠ I_ L → x ≠ HP → x ≠ hdr → x ≠ CNT_ L → x ≠ OUT_ L → m6 x = m0 x :=
    fun x h1 h2 h3 h4 h5 => by
      rw [hm6, Mem.write_ne _ _ h1, hm5, Mem.write_ne _ _ h2, hm3, Mem.write_ne _ _ h3, hm2,
        Mem.write_ne _ _ h4, hm1, Mem.write_ne _ _ h5]
  -- the loop invariant: `I = j`, the first `j` cells are `0 … j-1`
  have main := forLoop_spec (I_ L) (CNT_ L)
    (.seq (add (PTR_ L) (OUT_ L) (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE) (store (PTR_ L) (I_ L))))
    (fun j m => m (I_ L) = j ∧ m (CNT_ L) = c ∧ m (OUT_ L) = hdr ∧ m ONE = 1 ∧ m HP = hdr + 1 + c ∧
      m hdr = c ∧ (∀ i, i < j → m (hdr + 1 + i) = i) ∧
      (∀ x, x < hdr → x ≠ I_ L → x ≠ CNT_ L → x ≠ OUT_ L → x ≠ PTR_ L → x ≠ HP → m x = m0 x))
    c 3 (fun j m hm => ⟨hm.1, hm.2.1⟩) ?_ 0 m6 (Nat.zero_le _) ?_
  · obtain ⟨m', k, e, ⟨hi, hcnt, hout, hone, hhp, hhdr', hcells, hfr⟩, hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 (Cmd.Exec.seq e6 e))))), ?_, ?_, ?_⟩
    · have : (c - 0) * (3 + 3) ≤ n * 6 := Nat.mul_le_mul_right _ (by omega)
      omega
    · refine ⟨fun x hx hxV => ?_, by rw [hhp]; omega⟩
      simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hxV
      exact hfr x (by omega) hxV.2.1 hxV.2.2.1 hxV.2.2.2.2.2.2 hxV.2.2.2.1 hxV.1
    · refine ⟨by rw [hout, hhdr], ?_, by rw [hhp, hhdr, hc]⟩
      rw [← hhdr, ← hc]
      apply arrAt_of_cells
      · rw [hhdr', List.length_range]
      · intro i hi'
        rw [List.length_range] at hi'
        rw [List.getElem_range, hcells i hi']
  · -- the body
    intro j m hj hm
    obtain ⟨hi, hcnt, hout, hone, hhp, hhdr', hcells, hfr⟩ := hm
    have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
    obtain ⟨n1, hn1⟩ : ∃ n1, n1 = m.write (PTR_ L) (hdr + j) := ⟨_, rfl⟩
    have f1 : Cmd.Exec (add (PTR_ L) (OUT_ L) (I_ L)) m n1 1 := by
      have := Exec.add (PTR_ L) (OUT_ L) (I_ L) m; rwa [hout, hi, ← hn1] at this
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = m.write (PTR_ L) (hdr + 1 + j) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) n1 n2 1 := by
      have := Exec.add (PTR_ L) (PTR_ L) ONE n1
      rw [hn1, Mem.write_same, Mem.write_ne _ _ (by addr'), hone, Mem.write_write,
        show hdr + j + 1 = hdr + 1 + j by omega] at this
      rw [hn2, hn1]; exact this
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n2.write (hdr + 1 + j) j := ⟨_, rfl⟩
    have f3 : Cmd.Exec (store (PTR_ L) (I_ L)) n2 n3 1 := by
      have := Exec.store (PTR_ L) (I_ L) n2
      rw [hn2, Mem.write_same, Mem.write_ne _ _ (by addr'), hi] at this
      rw [hn3, hn2]; exact this
    have q3 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → n3 x = m x := fun x h1 h2 => by
      rw [hn3, Mem.write_ne _ _ h2, hn2, Mem.write_ne _ _ h1]
    refine ⟨n3, _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 f3), by omega,
      by rw [q3 _ (by addr') (by addr'), hi], by rw [q3 _ (by addr') (by addr'), hone], ?_⟩
    refine ⟨by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), q3 _ (by addr') (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), q3 _ (by addr') (by addr'), hout]
    · rw [Mem.write_ne _ _ (by addr'), q3 _ (by addr') (by addr'), hone]
    · rw [Mem.write_ne _ _ (by addr'), q3 _ (by addr') (by addr'), hhp]
    · rw [Mem.write_ne _ _ (by addr'), q3 _ (by addr') (by omega), hhdr']
    · intro i hi'
      rw [Mem.write_ne _ _ (by addr')]
      by_cases hij : i = j
      · subst hij; rw [hn3, Mem.write_same]
      · rw [q3 _ (by addr') (by omega), hcells i (by omega)]
    · intro x hx h1 h2 h3 h4 h5
      rw [Mem.write_ne _ _ h1, q3 x h4 (by omega), hfr x hx h1 h2 h3 h4 h5]
  · -- the initial invariant
    refine ⟨by rw [hm6, Mem.write_same], ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
      ?_⟩
    · rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm3,
        Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
    · rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm3,
        Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
    · rw [q6 ONE (by addr') (by addr') (by addr') (by addr') (by addr'), hone0]
    · rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_same]
    · rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
    · intro x hx h1 h2 h3 _ h5
      exact q6 x h1 h5 (by omega) h2 h3

end DisequalityDispersion.Machine
