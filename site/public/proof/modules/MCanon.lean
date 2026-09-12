import MValid
import BuildList

/-! # Canonical identifiers on the machine

`canonIds = buildList canonStep n` is computed by an index-driven array construction
(`buildM`) whose body evaluates `canonStep` on the prefix built so far.  The header of the
array under construction always holds the number of entries already computed, so that
`ids.getD a 0` is read faithfully by `getDM`. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Index-driven array construction (`buildList`) -/

/-- Build an array of length `M[N]` at a fresh address (returned in `OUT_ L`).  Entry `j` is
computed into `VAL` by `body`, which runs with `I_ L = j` and the prefix of `j` entries in the
array at `OUT_ L` (its header is `j`). -/
def buildBody (L : ℕ) (body : Cmd) : Cmd :=
  .seq body (.seq (add (PTR_ L) (OUT_ L) (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE)
    (.seq (store (PTR_ L) VAL) (.seq (add (CONT_ L) (I_ L) ONE) (store (OUT_ L) (CONT_ L))))))

def buildM (L N : ℕ) (body : Cmd) : Cmd :=
  .seq (mov (OUT_ L) HP) (.seq (store (OUT_ L) ZERO) (.seq (mov (CNT_ L) N)
    (.seq (add HP HP (CNT_ L)) (.seq (add HP HP ONE) (.seq (setc (I_ L) 0)
      (forLoop (I_ L) (CNT_ L) (buildBody L body)))))))

/-- The loop invariant of `buildM`. -/
structure BuildInv (L : ℕ) (V : List ℕ) (Pre : Mem → Prop) (F : List ℕ → ℕ → ℕ) (m0 : Mem) (c : ℕ)
    (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ V)
  pre : Pre m
  i : m (I_ L) = j
  cnt : m (CNT_ L) = c
  out : m (OUT_ L) = m0 HP
  arr : arrAt m (m0 HP) = buildList F j
  room : m0 HP + 1 + c ≤ m HP

theorem buildM_spec {body : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {F : List ℕ → ℕ → ℕ}
    (L N n : ℕ)
    (hbody : ∀ m j, Pre m → m (I_ L) = j → j < m N → IN ≤ m (OUT_ L) → m (OUT_ L) + 1 + m N ≤ m HP →
      arrAt m (m (OUT_ L)) = buildList F j →
      ∃ m' k, Cmd.Exec body m m' k ∧ k ≤ B ∧ Agree m m' V ∧ m' VAL = F (buildList F j) j)
    (hL : L ≤ 9) (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hN : 5 ≤ N ∧ N < IN) (hNV : N ∉ V)
    (hNL : N ∉ Lvars L) (hVL : ∀ x, x ∈ V → x ≠ I_ L ∧ x ≠ CNT_ L ∧ x ≠ OUT_ L)
    (hctx : ∀ m, Pre m → Ctx m) (hn : ∀ m, Pre m → m N ≤ n) (hPre : StableP Pre (Lvars L ++ V)) :
    RSpec (buildM L N body) (Lvars L ++ V) (n * (B + 8) + 8) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧ arrAt m' (m HP) = buildList F (m N) ∧
        m HP + 1 + m N ≤ m' HP) := by
  intro m0 hm0
  dsimp only
  have hLv := Lvars_range L hL
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  have hn0 := hn m0 hm0
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = m0 N := ⟨_, rfl⟩
  have hNO : N ≠ OUT_ L := fun h => hNL (by rw [h]; simp [Lvars])
  have hNC : N ≠ CNT_ L := fun h => hNL (by rw [h]; simp [Lvars])
  have hNI : N ≠ I_ L := fun h => hNL (by rw [h]; simp [Lvars])
  have hNP : N ≠ PTR_ L := fun h => hNL (by rw [h]; simp [Lvars])
  have hNX : N ≠ CONT_ L := fun h => hNL (by rw [h]; simp [Lvars])
  have hVlt : ∀ x, x ∈ Lvars L ++ V → x < IN := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · exact (hLv x h).2
    · exact (hV x h).2
  have hVlt' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2
  have hV5 : ∀ x, x ∈ Lvars L ++ V → 5 ≤ x := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h | h
    · have := (hLv x h).1; omega
    · exact (hV x h).1
  have hIV : I_ L ∉ V := fun h => (hVL _ h).1 rfl
  have hCV : CNT_ L ∉ V := fun h => (hVL _ h).2.1 rfl
  have hOV : OUT_ L ∉ V := fun h => (hVL _ h).2.2 rfl
  have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
  -- the setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ L) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ L) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write hdr 0 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (store (OUT_ L) ZERO) m1 m2 1 := by
    have := Exec.store (OUT_ L) ZERO m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr'), hzero0] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (CNT_ L) c := ⟨_, rfl⟩
  have e3 : Cmd.Exec (mov (CNT_ L) N) m2 m3 1 := by
    have := Exec.mov (CNT_ L) N m2
    rw [hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ hNO, ← hc] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + c) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (CNT_ L)) m3 m4 1 := by
    have := Exec.add HP HP (CNT_ L) m3
    rw [hm3, Mem.write_same, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1,
      Mem.write_ne _ _ (by addr'), ← hhdr] at this
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
  have q6 : ∀ x, x ≠ I_ L → x ≠ HP → x ≠ CNT_ L → x ≠ hdr → x ≠ OUT_ L → m6 x = m0 x :=
    fun x h1 h2 h3 h4 h5 => by
      rw [hm6, Mem.write_ne _ _ h1, hm5, Mem.write_ne _ _ h2, hm3, Mem.write_ne _ _ h3, hm2,
        Mem.write_ne _ _ h4, hm1, Mem.write_ne _ _ h5]
  have m6HP : m6 HP = hdr + 1 + c := by rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_same]
  have m6hdr : m6 hdr = 0 := by
    rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm3,
      Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
  have m6O : m6 (OUT_ L) = hdr := by
    rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm3,
      Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]
  have m6C : m6 (CNT_ L) = c := by
    rw [hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
  have m6I : m6 (I_ L) = 0 := by rw [hm6, Mem.write_same]
  have agree6 : Agree m0 m6 (Lvars L ++ V) := by
    refine ⟨fun x hx hxV => ?_, by rw [m6HP]; omega⟩
    simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hxV
    obtain ⟨h0, ⟨h1, h2, _, _, _, h6⟩, _⟩ := hxV
    exact q6 x h1 h0 h2 (by omega) h6
  -- the loop
  have main := forLoop_spec (I_ L) (CNT_ L) (buildBody L body)
    (BuildInv L V Pre F m0 c) c (B + 5) (fun j m hm => ⟨hm.i, hm.cnt⟩) ?_ 0 m6 (Nat.zero_le _) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 (Cmd.Exec.seq e6 e))))), ?_, inv'.agree, ?_⟩
    · have : (c - 0) * (B + 5 + 3) ≤ n * (B + 8) := Nat.mul_le_mul_right _ (by omega)
      omega
    · refine ⟨inv'.out, ?_, ?_⟩
      · rw [inv'.arr, hc]
      · rw [← hc]; exact inv'.room
  · -- the body
    intro j m hj hm
    obtain ⟨hag, hpre, hi, hcnt, hout, harr, hroom⟩ := hm
    have hhp : m0 HP ≤ m HP := hag.2
    have hmN : m N = c := by
      rw [hag.var N (lt_of_lt_of_le hN.2 hhp0) (by addr')
        (by simp only [List.mem_append, not_or]; exact ⟨hNL, hNV⟩), hc]
    have hone : m ONE = 1 := by
      rw [hag.var ONE (lt_of_lt_of_le (by addr') hhp0) (by addr')
        (fun h => by have := hV5 _ h; addr'), hone0]
    obtain ⟨n1, k1, f1, hk1, ag1, hval1⟩ := hbody m j hpre hi (by rw [hmN]; exact hj)
      (by rw [hout]; exact hhp0) (by rw [hout, hmN]; exact hroom) (by rw [hout]; exact harr)
    have n1HP : m HP ≤ n1 HP := ag1.2
    have v1 : ∀ x, x < IN → x ≠ HP → x ∉ V → n1 x = m x := fun x hx' hxH hxV =>
      ag1.var x (lt_of_lt_of_le hx' (le_trans hhp0 hhp)) hxH hxV
    have n1one : n1 ONE = 1 := by
      rw [v1 ONE (by addr') (by addr') (fun h => by have := hV _ h; addr'), hone]
    have n1I : n1 (I_ L) = j := by rw [v1 _ (hLv _ (by simp [Lvars])).2 (by addr') hIV, hi]
    have n1C : n1 (CNT_ L) = c := by rw [v1 _ (hLv _ (by simp [Lvars])).2 (by addr') hCV, hcnt]
    have n1O : n1 (OUT_ L) = hdr := by rw [v1 _ (hLv _ (by simp [Lvars])).2 (by addr') hOV, hout, hhdr]
    -- PTR := OUT + I + 1; M[PTR] := VAL; CONT := I + 1; M[OUT] := CONT
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = n1.write (PTR_ L) (hdr + j) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (PTR_ L) (OUT_ L) (I_ L)) n1 n2 1 := by
      have := Exec.add (PTR_ L) (OUT_ L) (I_ L) n1; rwa [n1O, n1I, ← hn2] at this
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n1.write (PTR_ L) (hdr + 1 + j) := ⟨_, rfl⟩
    have f3 : Cmd.Exec (add (PTR_ L) (PTR_ L) ONE) n2 n3 1 := by
      have := Exec.add (PTR_ L) (PTR_ L) ONE n2
      rw [hn2, Mem.write_same, Mem.write_ne _ _ (by addr'), n1one, Mem.write_write,
        show hdr + j + 1 = hdr + 1 + j by omega] at this
      rw [hn3, hn2]; exact this
    obtain ⟨n4, hn4⟩ : ∃ n4, n4 = n3.write (hdr + 1 + j) (F (buildList F j) j) := ⟨_, rfl⟩
    have f4 : Cmd.Exec (store (PTR_ L) VAL) n3 n4 1 := by
      have := Exec.store (PTR_ L) VAL n3
      rw [hn3, Mem.write_same, Mem.write_ne _ _ (by addr'), hval1] at this
      rw [hn4, hn3]; exact this
    have q4 : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → n4 x = n1 x := fun x h1 h2 => by
      rw [hn4, Mem.write_ne _ _ h2, hn3, Mem.write_ne _ _ h1]
    obtain ⟨n5, hn5⟩ : ∃ n5, n5 = n4.write (CONT_ L) (j + 1) := ⟨_, rfl⟩
    have f5 : Cmd.Exec (add (CONT_ L) (I_ L) ONE) n4 n5 1 := by
      have := Exec.add (CONT_ L) (I_ L) ONE n4
      rw [q4 _ (by addr') (by addr'), q4 _ (by addr') (by addr'), n1I, n1one] at this
      rw [hn5]; exact this
    obtain ⟨n6, hn6⟩ : ∃ n6, n6 = n5.write hdr (j + 1) := ⟨_, rfl⟩
    have f6 : Cmd.Exec (store (OUT_ L) (CONT_ L)) n5 n6 1 := by
      have := Exec.store (OUT_ L) (CONT_ L) n5
      rw [hn5, Mem.write_same, Mem.write_ne _ _ (by addr'), q4 _ (by addr') (by addr'), n1O] at this
      rw [hn6, hn5]; exact this
    have q6' : ∀ x, x ≠ PTR_ L → x ≠ hdr + 1 + j → x ≠ CONT_ L → x ≠ hdr → n6 x = n1 x :=
      fun x h1 h2 h3 h4 => by
        rw [hn6, Mem.write_ne _ _ h4, hn5, Mem.write_ne _ _ h3, q4 x h1 h2]
    have n6HP : n6 HP = n1 HP := q6' HP (by addr') (by addr') (by addr') (by addr')
    refine ⟨n6, _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 (Cmd.Exec.seq f3 (Cmd.Exec.seq f4
      (Cmd.Exec.seq f5 f6)))), by omega,
      by rw [q6' _ (by addr') (by addr') (by addr') (by addr'), n1I],
      by rw [q6' _ (by addr') (by addr') (by addr') (by addr'), n1one], ?_⟩
    have hmhdr : m hdr = j := by
      have := congrArg List.length harr; rw [arrAt_length, buildList_length, ← hhdr] at this; exact this
    have agree' : Agree m0 (n6.write (I_ L) (j + 1)) (Lvars L ++ V) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, q6' y hyV'.2.1.2.2.1 (by omega) hyV'.2.1.2.2.2.1 (by omega),
          ag1.var y (by omega) hyV'.1 hyV'.2.2]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), n6HP]; omega
    refine ⟨agree', hPre m0 _ hm0 agree', by rw [Mem.write_same], ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), q6' _ (by addr') (by addr') (by addr') (by addr'), n1C]
    · rw [Mem.write_ne _ _ (by addr'), q6' _ (by addr') (by addr') (by addr') (by addr'), n1O, hhdr]
    · rw [buildList_succ, ← harr, ← hhdr]
      apply arrAt_push
      · rw [Mem.write_ne _ _ (by addr'), hn6, Mem.write_same, hmhdr]
      · rw [Mem.write_ne _ _ (by addr'), hmhdr, hn6, Mem.write_ne _ _ (by omega), hn5,
          Mem.write_ne _ _ (by addr'), hn4, Mem.write_same, hhdr, harr]
      · intro i hi'
        rw [hmhdr] at hi'
        rw [Mem.write_ne _ _ (by addr'), q6' _ (by addr') (by omega) (by addr') (by omega),
          ag1.heap hVlt' _ (by omega) (by omega)]
    · rw [Mem.write_ne _ _ (by addr'), n6HP]; omega
  · -- the initial invariant
    refine ⟨agree6, hPre m0 _ hm0 agree6, m6I, m6C, by rw [m6O, hhdr], ?_, by rw [m6HP, hhdr]⟩
    rw [← hhdr, buildList_zero]
    unfold arrAt
    rw [m6hdr]; rfl


/-! ### `List.getD` on an array -/

/-- `D := (array at M[P]).getD M[A] 0`. -/
def getDM (P A D : ℕ) : Cmd := .seq (load D P) (.ite (.lt A D) (elemM P A D) (setc D 0))

theorem getDM_spec (P A D : ℕ) (hD : 5 ≤ D ∧ D < IN) (hDP : D ≠ P) (hDA : D ≠ A)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hP : ∀ m, Pre m → IN ≤ m P) :
    RSpec (getDM P A D) [D] 6 Pre (fun m m' => m' D = (arrAt m (m P)).getD (m A) 0 ∧ m' HP = m HP) := by
  intro m hm
  dsimp only
  obtain ⟨hone, hzero, hhp⟩ := hctx m hm
  have hPm := hP m hm
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write D (m (m P)) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load D P) m m1 1 := by rw [hm1]; exact Exec.load _ _ _
  have q1 : ∀ x, x ≠ D → m1 x = m x := fun x hx => by rw [hm1, Mem.write_ne _ _ hx]
  have m1D : m1 D = m (m P) := by rw [hm1, Mem.write_same]
  have m1A : m1 A = m A := q1 A (Ne.symm hDA)
  have m1P : m1 P = m P := q1 P (Ne.symm hDP)
  by_cases hlt : m A < m (m P)
  · have hc : (Cond.lt A D).eval m1 = true := by simp [Cond.eval, m1A, m1D, hlt]
    have hctx1 : Ctx m1 := ⟨by rw [q1 _ (by addr3), hone], by rw [q1 _ (by addr3), hzero],
      by rw [q1 _ (by addr3)]; exact hhp⟩
    obtain ⟨m2, k2, e2, hk2, ag2, hD2, hHP2⟩ := elemM_spec P A D hD hDP hDA (fun m => Ctx m ∧ IN ≤ m P)
      (fun _ h => h.1) (fun _ h => h.2) m1 ⟨hctx1, by rw [m1P]; exact hPm⟩
    refine ⟨m2, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc e2), by omega, ?_, ?_, ?_⟩
    · refine ⟨fun x hx hxV => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
        rw [ag2.var x (by rw [q1 _ (by addr3)]; exact hx) hxV.1 (by simp; exact hxV.2), q1 x hxV.2]
      · rw [hHP2, q1 _ (by addr3)]
    · rw [hD2, m1P, m1A, q1 _ (by addr3), List.getD_eq_getElem _ _ (by rw [arrAt_length]; exact hlt),
        arrAt_getElem]
    · rw [hHP2, q1 _ (by addr3)]
  · have hc : (Cond.lt A D).eval m1 = false := by simp [Cond.eval, m1A, m1D, hlt]
    refine ⟨m1.write D 0, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_false hc (Exec.setc _ _ _)), by omega, ?_, ?_, ?_⟩
    · refine ⟨fun x hx hxV => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
        rw [Mem.write_ne _ _ hxV.2, q1 x hxV.2]
      · rw [Mem.write_ne _ _ (by addr3), q1 _ (by addr3)]
    · rw [Mem.write_same, List.getD_eq_default _ _ (by rw [arrAt_length]; omega)]
    · rw [Mem.write_ne _ _ (by addr3), q1 _ (by addr3)]

/-! ### `Instance.firstIndex` -/

/-- `R := Instance.firstIndex p M[CNT]`, where `p i` is the flag computed by `t` with `X_ L = i`. -/
def firstIndexM (L R CNT : ℕ) (t : Cmd) : Cmd :=
  .seq (setc R 0) (.seq (mov (CNT_ L) CNT) (.seq (setc (I_ L) 0)
    (forLoop (I_ L) (CNT_ L) (.ite (.lt R (I_ L)) nop (.seq (mov (X_ L) (I_ L))
      (.seq t (.ite (.eq FLAG ONE) nop (add R (I_ L) ONE))))))))

/-- The variables written by `firstIndexM L R CNT t` (`V` those of `t`). -/
def fiV (L R : ℕ) (V : List ℕ) : List ℕ := R :: I_ L :: CNT_ L :: X_ L :: FLAG :: V

theorem firstIndexM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool}
    (L R CNT n : ℕ) (hL : L ≤ 9)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) < m CNT) P)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hR : 5 ≤ R ∧ R < IN) (hRV : R ∉ V) (hRL : R ∉ Lvars L)
    (hRF : R ≠ FLAG) (hRC : R ≠ CNT) (hCNT : 5 ≤ CNT ∧ CNT < IN) (hCV : CNT ∉ V) (hCL : CNT ∉ Lvars L)
    (hCF : CNT ≠ FLAG) (hVL : ∀ x, x ∈ V → x ≠ I_ L ∧ x ≠ CNT_ L ∧ x ≠ X_ L)
    (hctx : ∀ m, Pre m → Ctx m) (hn : ∀ m, Pre m → m CNT ≤ n)
    (hPre : StableP Pre (fiV L R V))
    (hP : Stable (fun m => Pre m ∧ m (X_ L) < m CNT) P (R :: I_ L :: CNT_ L :: FLAG :: V)) :
    RSpec (firstIndexM L R CNT t) (fiV L R V) (n * (B + 9) + 5) Pre
      (fun m m' => m' R = Instance.firstIndex (fun i => P (m.write (X_ L) i)) (m CNT)) := by
  intro m0 hm0
  dsimp only
  have hLv := Lvars_range L hL
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  have hn0 := hn m0 hm0
  obtain ⟨c, hc⟩ : ∃ c, c = m0 CNT := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℕ → Bool, p = fun i => P (m0.write (X_ L) i) := ⟨_, rfl⟩
  have hRI : R ≠ I_ L := fun h => hRL (by rw [h]; simp [Lvars])
  have hRX : R ≠ X_ L := fun h => hRL (by rw [h]; simp [Lvars])
  have hRCn : R ≠ CNT_ L := fun h => hRL (by rw [h]; simp [Lvars])
  have hCI : CNT ≠ I_ L := fun h => hCL (by rw [h]; simp [Lvars])
  have hCX : CNT ≠ X_ L := fun h => hCL (by rw [h]; simp [Lvars])
  have hCCn : CNT ≠ CNT_ L := fun h => hCL (by rw [h]; simp [Lvars])
  have hVlt : ∀ x, x ∈ fiV L R V → x < IN := by
    intro x hx
    simp only [fiV, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | h
    · exact hR.2
    · exact (hLv _ (by simp [Lvars])).2
    · exact (hLv _ (by simp [Lvars])).2
    · exact (hLv _ (by simp [Lvars])).2
    · addr3
    · exact (hV x h).2
  have hV5 : ∀ x, x ∈ fiV L R V → 5 ≤ x := by
    intro x hx
    simp only [fiV, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | h
    · exact hR.1
    · have := (hLv (I_ L) (by simp [Lvars])).1; omega
    · have := (hLv (CNT_ L) (by simp [Lvars])).1; omega
    · have := (hLv (X_ L) (by simp [Lvars])).1; omega
    · addr3
    · exact (hV x h).1
  -- setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write R 0 := ⟨_, rfl⟩
  have e1 : Cmd.Exec (setc R 0) m0 m1 1 := by rw [hm1]; exact Exec.setc _ _ _
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (CNT_ L) c := ⟨_, rfl⟩
  have e2 : Cmd.Exec (mov (CNT_ L) CNT) m1 m2 1 := by
    have := Exec.mov (CNT_ L) CNT m1
    rw [hm1, Mem.write_ne _ _ (Ne.symm hRC), ← hc] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (I_ L) 0 := ⟨_, rfl⟩
  have e3 : Cmd.Exec (setc (I_ L) 0) m2 m3 1 := by rw [hm3]; exact Exec.setc _ _ _
  have q3 : ∀ x, x ≠ R → x ≠ CNT_ L → x ≠ I_ L → m3 x = m0 x := fun x h1 h2 h3 => by
    rw [hm3, Mem.write_ne _ _ h3, hm2, Mem.write_ne _ _ h2, hm1, Mem.write_ne _ _ h1]
  have agree3 : Agree m0 m3 (fiV L R V) := by
    refine ⟨fun x hx hxV => ?_, by rw [q3 _ (by addr3) (by addr3) (by addr3)]⟩
    simp only [List.mem_cons, fiV, not_or] at hxV
    exact q3 x hxV.2.1 hxV.2.2.2.1 hxV.2.2.1
  -- the loop
  have main := forLoop_spec (I_ L) (CNT_ L)
    (.ite (.lt R (I_ L)) nop (.seq (mov (X_ L) (I_ L)) (.seq t (.ite (.eq FLAG ONE) nop (add R (I_ L) ONE)))))
    (fun i m => Agree m0 m (fiV L R V) ∧ Pre m ∧ m (I_ L) = i ∧ m (CNT_ L) = c ∧ m R = Instance.firstIndex p i)
    c (B + 6) (fun i m hm => ⟨hm.2.2.1, hm.2.2.2.1⟩) ?_ 0 m3 (Nat.zero_le _) ?_
  · obtain ⟨m', k, e, ⟨hag, _, _, _, hres⟩, hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 e)), ?_, hag, ?_⟩
    · have : (c - 0) * (B + 6 + 3) ≤ n * (B + 9) := Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [hres, hp, hc]
  · -- the body
    intro i m hi hm
    obtain ⟨hag, hpre, hI, hC, hRv⟩ := hm
    have hhp : m0 HP ≤ m HP := hag.2
    have hone : m ONE = 1 := by
      rw [hag.var ONE (lt_of_lt_of_le (by addr3) hhp0) (by addr3) (fun h => by have := hV5 _ h; addr3), hone0]
    have hmC : m CNT = c := by
      rw [hag.var CNT (lt_of_lt_of_le hCNT.2 hhp0) (by addr3) (by
        simp only [fiV, List.mem_cons, not_or]; exact ⟨hRC.symm, hCI, hCCn, hCX, hCF, hCV⟩), hc]
    have hfi := Instance.firstIndex_le p i
    by_cases hlt : m R < i
    · -- `R < I`: nothing to do
      have hcond : (Cond.lt R (I_ L)).eval m = true := by simp [Cond.eval, hI, hlt]
      refine ⟨m, _, Cmd.Exec.ite_true hcond (Exec.nop m), by omega, hI, hone, ?_⟩
      have hag' : Agree m0 (m.write (I_ L) (i + 1)) (fiV L R V) :=
        hag.trans (Agree.write m (I_ L) (i + 1) (by addr3)) |>.mono (by
          intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | rfl
          · exact h
          · simp [fiV])
      refine ⟨hag', hPre m0 _ hm0 hag', by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr3), hC], ?_⟩
      rw [Mem.write_ne _ _ hRI, hRv]
      simp only [Instance.firstIndex]
      rw [if_pos (by rw [← hRv]; exact hlt)]
    · -- `R = I`: test `p i`
      have hRi : m R = i := by omega
      have hcond : (Cond.lt R (I_ L)).eval m = false := by simp [Cond.eval, hI, hlt]
      obtain ⟨n1, hn1⟩ : ∃ n1, n1 = m.write (X_ L) i := ⟨_, rfl⟩
      have f1 : Cmd.Exec (mov (X_ L) (I_ L)) m n1 1 := by
        have := Exec.mov (X_ L) (I_ L) m; rwa [hI, ← hn1] at this
      have q1 : ∀ x, x ≠ X_ L → n1 x = m x := fun x hx => by rw [hn1, Mem.write_ne _ _ hx]
      have agn1 : Agree m0 n1 (fiV L R V) := by
        rw [hn1]
        exact hag.trans (Agree.write m (X_ L) i (by addr3)) |>.mono (by
          intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with h | rfl
          · exact h
          · simp [fiV])
      have hpre1 : Pre n1 ∧ n1 (X_ L) < n1 CNT := ⟨hPre m0 _ hm0 agn1, by
        rw [hn1, Mem.write_same, Mem.write_ne _ _ hCX, hmC]; exact hi⟩
      obtain ⟨n2, k2, f2, hk2, ag2, hfl2⟩ := ht n1 hpre1
      -- the flag is `p i`
      have hPi : P n1 = p i := by
        rw [hp]
        refine hP _ _ ⟨hPre m0 _ hm0 (Agree.write m0 (X_ L) i (by addr3) |>.mono (by
            intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; simp [fiV])),
          by rw [Mem.write_same, Mem.write_ne _ _ hCX, ← hc]; exact hi⟩ ?_
        refine ⟨fun y hy hyV => ?_, ?_⟩
        · simp only [List.mem_cons, not_or] at hyV
          by_cases hyx : y = X_ L
          · rw [hyx, hn1, Mem.write_same, Mem.write_same]
          · rw [hn1, Mem.write_ne _ _ hyx, Mem.write_ne _ _ hyx]
            exact hag.var y (by rw [Mem.write_ne _ _ (by addr3)] at hy; exact hy) hyV.1 (by
              simp only [fiV, List.mem_cons, not_or]
              exact ⟨hyV.2.1, hyV.2.2.1, hyV.2.2.2.1, hyx, hyV.2.2.2.2.1, hyV.2.2.2.2.2⟩)
        · rw [Mem.write_ne _ _ (by addr3), hn1, Mem.write_ne _ _ (by addr3)]; exact hhp
      have n2HP : n1 HP ≤ n2 HP := ag2.2
      have v2 : ∀ x, x < IN → x ≠ HP → x ∉ V → n2 x = n1 x := fun x hx hxH hxV =>
        ag2.var x (by rw [hn1, Mem.write_ne _ _ (by addr3)]; exact lt_of_lt_of_le hx (le_trans hhp0 hhp)) hxH hxV
      have n2one : n2 ONE = 1 := by
        rw [v2 ONE (by addr3) (by addr3) (fun h => by have := hV _ h; addr3), q1 _ (by addr3), hone]
      have n2I : n2 (I_ L) = i := by
        rw [v2 _ (hLv _ (by simp [Lvars])).2 (by addr3) (fun h => (hVL _ h).1 rfl), q1 _ (by addr3), hI]
      have n2C : n2 (CNT_ L) = c := by
        rw [v2 _ (hLv _ (by simp [Lvars])).2 (by addr3) (fun h => (hVL _ h).2.1 rfl), q1 _ (by addr3), hC]
      have n2R : n2 R = i := by rw [v2 R hR.2 (by addr3) hRV, q1 _ hRX, hRi]
      have agn2 : Agree m0 n2 (fiV L R V) := (agn1.trans (ag2.mono (V' := fiV L R V) (fun x hx => by
          simp only [fiV, List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))))).mono (by
        intro x hx; simp only [List.mem_append] at hx; rcases hx with h | h <;> exact h)
      -- the conditional
      have hfi' : Instance.firstIndex p (i + 1) = if p i then i else i + 1 := by
        simp only [Instance.firstIndex]
        rw [if_neg (by rw [← hRv, hRi]; exact lt_irrefl _)]
      by_cases hpi : p i = true
      · have hcond2 : (Cond.eq FLAG ONE).eval n2 = true := by
          simp [Cond.eval, hfl2, hPi, hpi, n2one, bitv]
        refine ⟨n2, _, Cmd.Exec.ite_false hcond (Cmd.Exec.seq f1 (Cmd.Exec.seq f2
          (Cmd.Exec.ite_true hcond2 (Exec.nop n2)))), by omega, n2I, n2one, ?_⟩
        have hag' : Agree m0 (n2.write (I_ L) (i + 1)) (fiV L R V) :=
          agn2.trans (Agree.write n2 (I_ L) (i + 1) (by addr3)) |>.mono (by
            intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with h | rfl
            · exact h
            · simp [fiV])
        refine ⟨hag', hPre m0 _ hm0 hag', by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr3), n2C], ?_⟩
        rw [Mem.write_ne _ _ hRI, n2R, hfi', if_pos hpi]
      · have hpi' : p i = false := by simpa using hpi
        have hcond2 : (Cond.eq FLAG ONE).eval n2 = false := by
          simp [Cond.eval, hfl2, hPi, hpi', n2one, bitv]
        refine ⟨n2.write R (i + 1), _, Cmd.Exec.ite_false hcond (Cmd.Exec.seq f1 (Cmd.Exec.seq f2
          (Cmd.Exec.ite_false hcond2 (by
            have := Exec.add R (I_ L) ONE n2; rwa [n2I, n2one] at this)))), by omega,
          by rw [Mem.write_ne _ _ (Ne.symm hRI), n2I], by rw [Mem.write_ne _ _ (by addr3), n2one], ?_⟩
        have hag' : Agree m0 ((n2.write R (i + 1)).write (I_ L) (i + 1)) (fiV L R V) :=
          (agn2.trans (Agree.write n2 R (i + 1) (by addr3))).trans (Agree.write _ (I_ L) (i + 1) (by addr3))
            |>.mono (by
              intro x hx
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with (h | rfl) | rfl
              · exact h
              · simp [fiV]
              · simp [fiV])
        refine ⟨hag', hPre m0 _ hm0 hag', by rw [Mem.write_same], by
          rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (Ne.symm hRCn), n2C], ?_⟩
        rw [Mem.write_ne _ _ hRI, Mem.write_same, hfi', if_neg (by simp [hpi'])]
  · -- the initial invariant
    refine ⟨agree3, hPre m0 _ hm0 agree3, by rw [hm3, Mem.write_same], ?_, ?_⟩
    · rw [hm3, Mem.write_ne _ _ (by addr3), hm2, Mem.write_same]
    · rw [hm3, Mem.write_ne _ _ hRI, hm2, Mem.write_ne _ _ hRCn, hm1, Mem.write_same]
      rfl


/-! ### Signature equality in terms of the record cells -/

theorem sigEq_cells (ids : List ℕ) {m : Mem} {lo hi p₁ p₂ : ℕ} {nd₁ nd₂ : Node}
    (h₁ : RepNode m lo hi p₁ nd₁) (h₂ : RepNode m lo hi p₂ nd₂) :
    decide (Instance.sigWith ids nd₁ = Instance.sigWith ids nd₂) =
      (if m p₁ = m p₂ then
        (if m p₁ = 0 then decide (m (p₁ + 1) = m (p₂ + 1))
         else (decide (m (p₁ + 1) = m (p₂ + 1)) && decide (m (m (p₁ + 2)) = m (m (p₂ + 2)))) &&
           (List.range (m (m (p₁ + 2)))).all (fun idx => if idx < m (m (p₂ + 2)) then
             decide (ids.getD (m (m (p₁ + 2) + 1 + idx)) 0 = ids.getD (m (m (p₂ + 2) + 1 + idx)) 0)
             else false))
       else false) := by
  rcases repNode_cases h₁ with ⟨t₁, i₁, rfl, c₁⟩ | ⟨t₁, f₁, a₁, rfl, c₁, r₁⟩ <;>
  rcases repNode_cases h₂ with ⟨t₂, i₂, rfl, c₂⟩ | ⟨t₂, f₂, a₂, rfl, c₂, r₂⟩
  · rw [if_pos (by rw [t₁, t₂]), if_pos t₁, c₁, c₂]; simp [Instance.sigWith]
  · rw [if_neg (by rw [t₁, t₂]; decide)]; simp [Instance.sigWith]
  · rw [if_neg (by rw [t₁, t₂]; decide)]; simp [Instance.sigWith]
  · rw [if_pos (by rw [t₁, t₂]), if_neg (by rw [t₁]; decide), c₁, c₂, r₁.2.2.1, r₂.2.2.1]
    simp only [Instance.sigWith]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Node.app.injEq]
    constructor
    · rintro ⟨hf, hl⟩
      have hlen : a₁.length = a₂.length := by
        have := congrArg List.length hl; simpa using this
      refine ⟨⟨hf, hlen⟩, fun idx hidx => ?_⟩
      rw [if_pos (by omega)]
      simp only [decide_eq_true_eq]
      have := congrArg (fun l => l[idx]?) hl
      simp only [List.getElem?_map] at this
      rw [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem (by omega)] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [r₁.2.2.2 idx hidx, r₂.2.2.2 idx (by omega)]
      exact this
    · rintro ⟨⟨hf, hlen⟩, hall⟩
      refine ⟨hf, List.ext_getElem (by simp [hlen]) fun idx h₁' h₂' => ?_⟩
      simp only [List.getElem_map]
      simp only [List.length_map] at h₁' h₂'
      have := hall idx h₁'
      rw [if_pos h₂'] at this
      simp only [decide_eq_true_eq] at this
      rw [r₁.2.2.2 idx h₁', r₂.2.2.2 idx h₂'] at this
      exact this

/-! ### Comparing two argument lists under `ids.getD` -/

/-- Precondition of the argument comparison: two argument arrays (`G_ 7`, `G_ 8`) and the
identifier array (`OUT_ 0`), all in the heap; the first has at most `n` entries. -/
def ArgsPre2 (n : ℕ) (m : Mem) : Prop :=
  Ctx m ∧ IN ≤ m (G_ 7) ∧ m (G_ 7) + 1 + m (m (G_ 7)) ≤ m HP ∧ IN ≤ m (G_ 8) ∧
    m (G_ 8) + 1 + m (m (G_ 8)) ≤ m HP ∧ IN ≤ m (OUT_ 0) ∧ m (OUT_ 0) + 1 + m (m (OUT_ 0)) ≤ m HP ∧
    m (m (G_ 7)) ≤ n

/-- Compare entry `X_ 2` of both argument arrays under `ids.getD` (false beyond the second). -/
def idxTest : Cmd :=
  .ite (.lt (X_ 2) (G_ 10))
    (.seq (elemM (G_ 7) (X_ 2) (G_ 11)) (.seq (getDM (OUT_ 0) (G_ 11) (G_ 12))
      (.seq (elemM (G_ 8) (X_ 2) (G_ 13)) (.seq (getDM (OUT_ 0) (G_ 13) (G_ 14)) (eqTest (G_ 12) (G_ 14))))))
    (setc FLAG 0)

/-- The precondition of `idxTest` inside the scan. -/
def IdxPre (n : ℕ) (m : Mem) : Prop :=
  ArgsPre2 n m ∧ m (G_ 9) = m (m (G_ 7)) ∧ m (G_ 10) = m (m (G_ 8))

theorem ArgsPre2.stable {n : ℕ} {V : List ℕ} (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (h7 : G_ 7 ∉ V)
    (h8 : G_ 8 ∉ V) (hO : OUT_ 0 ∉ V) {m m₁ : Mem} (hag : Agree m m₁ V) (h : ArgsPre2 n m) :
    ArgsPre2 n m₁ ∧ m₁ (G_ 7) = m (G_ 7) ∧ m₁ (G_ 8) = m (G_ 8) ∧ m₁ (OUT_ 0) = m (OUT_ 0) ∧
      (∀ x, IN ≤ x → x < m HP → m₁ x = m x) := by
  obtain ⟨hctx, h1, h2, h3, h4, h5, h6, h7'⟩ := h
  have hhp : 200 ≤ m HP := hctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2
  have hG7 : m₁ (G_ 7) = m (G_ 7) := hag.var (G_ 7) (lt_hp hhp (by decide)) (by decide) h7
  have hG8 : m₁ (G_ 8) = m (G_ 8) := hag.var (G_ 8) (lt_hp hhp (by decide)) (by decide) h8
  have hO' : m₁ (OUT_ 0) = m (OUT_ 0) := hag.var (OUT_ 0) (lt_hp hhp (by decide)) (by decide) hO
  have hheap : ∀ x, IN ≤ x → x < m HP → m₁ x = m x := fun x hx hx' => hag.heap hV' x hx hx'
  refine ⟨⟨Ctx.of_agree hctx hag (fun x hx => (hV x hx).1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hG7, hG8, hO', hheap⟩
  · rw [hG7]; exact h1
  · rw [hG7, hheap _ h1 (by omega)]; exact le_trans h2 hag.2
  · rw [hG8]; exact h3
  · rw [hG8, hheap _ h3 (by omega)]; exact le_trans h4 hag.2
  · rw [hO']; exact h5
  · rw [hO', hheap _ h5 (by omega)]; exact le_trans h6 hag.2
  · rw [hG7, hheap _ h1 (by omega)]; exact h7'

theorem idxTest_spec (n : ℕ) :
    TestSpec idxTest [G_ 11, G_ 12, G_ 13, G_ 14, FLAG] 24 (fun m => IdxPre n m ∧ m (X_ 2) < m (G_ 9))
      (fun m => if m (X_ 2) < m (m (G_ 8)) then
        decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + m (X_ 2))) 0 =
          (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + m (X_ 2))) 0)
        else false) := by
  have hsG : ∀ i, i < 60 → ∀ x, x ∈ [G_ i] → 5 ≤ x ∧ x < IN := fun i hi x hx => by
    simp at hx; subst hx; exact ⟨(safeVars_G i hi).1, (safeVars_G i hi).2.1⟩
  -- the then-branch
  let Pre0 : Mem → Prop := fun m => (IdxPre n m ∧ m (X_ 2) < m (G_ 9)) ∧ m (X_ 2) < m (G_ 10)
  have hstab : ∀ {V : List ℕ}, (∀ x, x ∈ V → 5 ≤ x ∧ x < IN) → G_ 7 ∉ V → G_ 8 ∉ V → OUT_ 0 ∉ V →
      G_ 9 ∉ V → G_ 10 ∉ V → X_ 2 ∉ V → ∀ m m₁, Agree m m₁ V → Pre0 m →
      Pre0 m₁ ∧ m₁ (G_ 7) = m (G_ 7) ∧ m₁ (G_ 8) = m (G_ 8) ∧ m₁ (OUT_ 0) = m (OUT_ 0) ∧
        m₁ (X_ 2) = m (X_ 2) ∧ (∀ x, IN ≤ x → x < m HP → m₁ x = m x) := by
    intro V hV h7 h8 hO h9 h10 hX m m₁ hag hm
    have hhp : 200 ≤ m HP := hm.1.1.1.1.2.2
    obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable hV h7 h8 hO hag hm.1.1.1
    have hG9 : m₁ (G_ 9) = m (G_ 9) := hag.var (G_ 9) (lt_hp hhp (by decide)) (by decide) h9
    have hG10 : m₁ (G_ 10) = m (G_ 10) := hag.var (G_ 10) (lt_hp hhp (by decide)) (by decide) h10
    have hX' : m₁ (X_ 2) = m (X_ 2) := hag.var (X_ 2) (lt_hp hhp (by decide)) (by decide) hX
    obtain ⟨⟨⟨hA0, hq9, hq10⟩, hlt9⟩, hlt10⟩ := hm
    obtain ⟨_, hq7, hq7', hq8, hq8', _⟩ := hA0
    refine ⟨⟨⟨⟨hA, ?_, ?_⟩, ?_⟩, ?_⟩, hG7, hG8, hO', hX', hheap⟩
    · rw [hG9, hG7, hheap _ hq7 (by omega)]; exact hq9
    · rw [hG10, hG8, hheap _ hq8 (by omega)]; exact hq10
    · rw [hX', hG9]; exact hlt9
    · rw [hX', hG10]; exact hlt10
  have e1 := elemM_spec (G_ 7) (X_ 2) (G_ 11) (by constructor <;> addr3) (by decide) (by decide) Pre0
    (fun m hm => hm.1.1.1.1) (fun m hm => hm.1.1.1.2.1)
  let Pre1 : Mem → Prop := fun m => Pre0 m ∧ m (G_ 11) = m (m (G_ 7) + 1 + m (X_ 2))
  have e2 := getDM_spec (OUT_ 0) (G_ 11) (G_ 12) (by constructor <;> addr3) (by decide) (by decide) Pre1
    (fun m hm => hm.1.1.1.1.1) (fun m hm => hm.1.1.1.1.2.2.2.2.2.1)
  let Pre2 : Mem → Prop := fun m => Pre1 m ∧ m (G_ 12) = (arrAt m (m (OUT_ 0))).getD (m (G_ 11)) 0
  have e3 := elemM_spec (G_ 8) (X_ 2) (G_ 13) (by constructor <;> addr3) (by decide) (by decide) Pre2
    (fun m hm => hm.1.1.1.1.1.1) (fun m hm => hm.1.1.1.1.1.2.2.2.1)
  let Pre3 : Mem → Prop := fun m => Pre2 m ∧ m (G_ 13) = m (m (G_ 8) + 1 + m (X_ 2))
  have e4 := getDM_spec (OUT_ 0) (G_ 13) (G_ 14) (by constructor <;> addr3) (by decide) (by decide) Pre3
    (fun m hm => hm.1.1.1.1.1.1.1) (fun m hm => hm.1.1.1.1.1.1.2.2.2.2.2.1)
  have t4 := TestSpec.after e4 (eqTest_spec (G_ 12) (G_ 14) (fun _ => True))
    (Q := fun m => decide (m (G_ 12) = (arrAt m (m (OUT_ 0))).getD (m (G_ 13)) 0))
    (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.1.1.2.2
      dsimp only
      rw [hp.1, hag.var (G_ 12) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t3 := TestSpec.after e3 t4
    (Q := fun m => decide (m (G_ 12) = (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + m (X_ 2))) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hG7, hG8, hO', hX', hheap⟩ := hstab (hsG 13 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m₁ hag hm.1.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.1.2.2
      obtain ⟨_, _, _, _, _, hO1, hO2, _⟩ := hm.1.1.1.1.1
      have hG11 : m₁ (G_ 11) = m (G_ 11) := hag.var (G_ 11) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG12 : m₁ (G_ 12) = m (G_ 12) := hag.var (G_ 12) (lt_hp hhp (by decide)) (by decide) (by decide)
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) :=
        hag.arrAt (fun x hx => ((hsG 13 (by norm_num)) x hx).2) _ hO1 hO2
      refine ⟨⟨⟨hp0, ?_⟩, ?_⟩, ?_⟩
      · rw [hG11, hG7, hX', hheap _ (by have := hm.1.1.1.1.1.2.1; omega) (by
          have := hm.1.1.1.1.1.2.2.1; have := hm.1.1.1.2; have := hm.1.1.1.1.2.1; omega)]
        exact hm.1.2
      · rw [hG12, hG11, hO', harr]; exact hm.2
      · have hq10 := hm.1.1.1.1.2.2
        have hlt10 := hm.1.1.2
        rw [hp.1, hG8, hX', hheap (m (G_ 8) + 1 + m (X_ 2)) (by have := hm.1.1.1.1.1.2.2.2.1; omega) (by
          have := hm.1.1.1.1.1.2.2.2.2.1; omega)])
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hG7, hG8, hO', hX', hheap⟩ := hstab (hsG 13 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m₁ hag hm.1.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.1.2.2
      obtain ⟨_, _, _, _, _, hO1, hO2, _⟩ := hm.1.1.1.1.1
      have hG12 : m₁ (G_ 12) = m (G_ 12) := hag.var (G_ 12) (lt_hp hhp (by decide)) (by decide) (by decide)
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) :=
        hag.arrAt (fun x hx => ((hsG 13 (by norm_num)) x hx).2) _ hO1 hO2
      dsimp only
      rw [hp.1, hG12, hO', harr])
  have t2 := TestSpec.after e2 t3
    (Q := fun m => decide ((arrAt m (m (OUT_ 0))).getD (m (G_ 11)) 0 =
      (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + m (X_ 2))) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hG7, hG8, hO', hX', hheap⟩ := hstab (hsG 12 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m₁ hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.2.2
      obtain ⟨_, _, _, _, _, hO1, hO2, _⟩ := hm.1.1.1.1
      have hG11 : m₁ (G_ 11) = m (G_ 11) := hag.var (G_ 11) (lt_hp hhp (by decide)) (by decide) (by decide)
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) :=
        hag.arrAt (fun x hx => ((hsG 12 (by norm_num)) x hx).2) _ hO1 hO2
      refine ⟨⟨hp0, ?_⟩, ?_⟩
      · rw [hG11, hG7, hX', hheap _ (by have := hm.1.1.1.1.2.1; omega) (by
          have := hm.1.1.1.1.2.2.1; have := hm.1.1.2; have := hm.1.1.1.2.1; omega)]
        exact hm.2
      · rw [hp.1, hG11, hO', harr])
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hG7, hG8, hO', hX', hheap⟩ := hstab (hsG 12 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m₁ hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.2.2
      obtain ⟨_, _, _, hq8, hq8', hO1, hO2, _⟩ := hm.1.1.1.1
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) :=
        hag.arrAt (fun x hx => ((hsG 12 (by norm_num)) x hx).2) _ hO1 hO2
      dsimp only
      rw [hp.1, hO', harr, hG8, hX', hheap (m (G_ 8) + 1 + m (X_ 2)) (by omega) (by
        have := hm.1.2; have := hm.1.1.1.2.2; omega)])
  have t1 := TestSpec.after e1 t2
    (Q := fun m => decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + m (X_ 2))) 0 =
      (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + m (X_ 2))) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hG7, hG8, hO', hX', hheap⟩ := hstab (hsG 11 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m₁ hag hm
      obtain ⟨_, hq7, hq7', hq8, hq8', hO1, hO2, _⟩ := hm.1.1.1
      have hq9 := hm.1.1.2.1
      have hlt9 := hm.1.2
      exact ⟨hp0, by rw [hp.1, hG7, hX', hheap (m (G_ 7) + 1 + m (X_ 2)) (by omega) (by omega)]⟩)
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hG7, hG8, hO', hX', hheap⟩ := hstab (hsG 11 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m₁ hag hm
      obtain ⟨_, hq7, hq7', hq8, hq8', hO1, hO2, _⟩ := hm.1.1.1
      have hq10 := hm.1.1.2.2
      have hlt10 := hm.2
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) :=
        hag.arrAt (fun x hx => ((hsG 11 (by norm_num)) x hx).2) _ hO1 hO2
      dsimp only
      rw [hp.1, hO', harr, hG8, hX', hheap (m (G_ 8) + 1 + m (X_ 2)) (by omega) (by omega)])
  have tt := TestSpec.iteLt' (X_ 2) (G_ 10) t1
    (falseTest_spec (fun m => (IdxPre n m ∧ m (X_ 2) < m (G_ 9)) ∧ ¬ m (X_ 2) < m (G_ 10)))
  unfold idxTest
  refine (tt.mono (V' := [G_ 11, G_ 12, G_ 13, G_ 14, FLAG]) (fun x hx => by simp at hx ⊢; tauto) (by omega)
    (fun m hm => hm)).congr (fun m hm => ?_)
  dsimp only
  rw [hm.1.2.2]

/-- `args₁.map getD = args₂.map getD` (given equal lengths), as a scan of the first. -/
def argsEqTest : Cmd :=
  .seq (load (G_ 9) (G_ 7)) (.seq (load (G_ 10) (G_ 8)) (allRangeM 2 (G_ 9) idxTest))

def argsEqV : List ℕ :=
  [G_ 9] ++ ([G_ 10] ++ (FLAG :: (rangeV 2 ++ FLAG :: (FLAG :: [G_ 11, G_ 12, G_ 13, G_ 14, FLAG]))))

theorem argsEqV_safe : SafeVars argsEqV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_rangeV 2 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (SafeVars.cons safeVars_FLAG (safeVars_of_decide _ (by decide)))))))

theorem arrAt_write_lo (m : Mem) (a x v : ℕ) (hx : x < IN) (ha : IN ≤ a) :
    arrAt (m.write x v) a = arrAt m a :=
  arrAt_congr (fun y h1 _ => Mem.write_ne _ _ (by omega))

/-- The value of `idxTest` at index `i`, with `X_ 2 := i` substituted away. -/
theorem idxP_write (m : Mem) (i : ℕ) (h7 : IN ≤ m (G_ 7)) (h8 : IN ≤ m (G_ 8)) (hO : IN ≤ m (OUT_ 0)) :
    (if (m.write (X_ 2) i) (X_ 2) < (m.write (X_ 2) i) ((m.write (X_ 2) i) (G_ 8)) then
      decide ((arrAt (m.write (X_ 2) i) ((m.write (X_ 2) i) (OUT_ 0))).getD
          ((m.write (X_ 2) i) ((m.write (X_ 2) i) (G_ 7) + 1 + (m.write (X_ 2) i) (X_ 2))) 0 =
        (arrAt (m.write (X_ 2) i) ((m.write (X_ 2) i) (OUT_ 0))).getD
          ((m.write (X_ 2) i) ((m.write (X_ 2) i) (G_ 8) + 1 + (m.write (X_ 2) i) (X_ 2))) 0)
      else false) =
    (if i < m (m (G_ 8)) then
      decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + i)) 0 =
        (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + i)) 0) else false) := by
  rw [Mem.write_same, Mem.write_ne _ _ (show G_ 8 ≠ X_ 2 by decide), Mem.write_ne _ _ (show G_ 7 ≠ X_ 2 by decide),
    Mem.write_ne _ _ (show OUT_ 0 ≠ X_ 2 by decide), Mem.write_ne _ _ (show m (G_ 8) ≠ X_ 2 by addr3),
    Mem.write_ne _ _ (show m (G_ 7) + 1 + i ≠ X_ 2 by addr3), Mem.write_ne _ _ (show m (G_ 8) + 1 + i ≠ X_ 2 by addr3),
    arrAt_write_lo _ _ _ _ (by addr3) hO]

theorem argsEqTest_spec (n : ℕ) :
    TestSpec argsEqTest argsEqV (n * (24 + 12) + n * 6 + 23) (ArgsPre2 n)
      (fun m => (List.range (m (m (G_ 7)))).all (fun idx => if idx < m (m (G_ 8)) then
        decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + idx)) 0 =
          (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + idx)) 0) else false)) := by
  have hs11 : SafeVars [G_ 11, G_ 12, G_ 13, G_ 14, FLAG] := safeVars_of_decide _ (by decide)
  have hall := allRangeM_spec 2 (G_ 9) n (by norm_num) (idxTest_spec n)
    (fun x hx => ⟨(hs11 x hx).1, (hs11 x hx).2.1⟩) (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun m hm => hm.1.1)
    (fun m hm => by rw [hm.2.1]; exact hm.1.2.2.2.2.2.2.2)
    (by
      intro m m' hm hag
      have hV : SafeVars (rangeV 2 ++ FLAG :: [G_ 11, G_ 12, G_ 13, G_ 14, FLAG]) :=
        SafeVars.append (safeVars_rangeV 2 (by norm_num)) (SafeVars.cons safeVars_FLAG hs11)
      have hhp : 200 ≤ m HP := hm.1.1.2.2
      obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable (fun x hx => ⟨(hV x hx).1, (hV x hx).2.1⟩)
        (by decide) (by decide) (by decide) hag hm.1
      refine ⟨hA, ?_, ?_⟩
      · rw [hag.var (G_ 9) (lt_hp hhp (by decide)) (by decide) (by decide), hG7,
          hheap _ hm.1.2.1 (by have := hm.1.2.2.1; omega)]; exact hm.2.1
      · rw [hag.var (G_ 10) (lt_hp hhp (by decide)) (by decide) (by decide), hG8,
          hheap _ hm.1.2.2.2.1 (by have := hm.1.2.2.2.2.1; omega)]; exact hm.2.2)
    (by
      intro m m' hm hag
      have hV : SafeVars (LvarsX 2 ++ FLAG :: [G_ 11, G_ 12, G_ 13, G_ 14, FLAG] ++ rangeVX 2) :=
        SafeVars.append (SafeVars.append (safeVars_LvarsX 2 (by norm_num)) (SafeVars.cons safeVars_FLAG hs11))
          (SafeVars.append (safeVars_Lvars 3 (by norm_num)) (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
            (fun x hx => by simp at hx)))
      have hhp : 200 ≤ m HP := hm.1.1.1.2.2
      obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable (fun x hx => ⟨(hV x hx).1, (hV x hx).2.1⟩)
        (by decide) (by decide) (by decide) hag hm.1.1
      obtain ⟨_, hq7, hq7', hq8, hq8', hO1, hO2, _⟩ := hm.1.1
      have hX' : m' (X_ 2) = m (X_ 2) := hag.var (X_ 2) (lt_hp hhp (by decide)) (by decide) (by decide)
      have harr : arrAt m' (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) :=
        hag.arrAt (fun x hx => (hV x hx).2.1) _ hO1 hO2
      have hlt : m (X_ 2) < m (m (G_ 7)) := by rw [← hm.1.2.1]; exact hm.2
      dsimp only
      rw [hX', hG8, hheap _ hq8 (by omega)]
      by_cases hlt8 : m (X_ 2) < m (m (G_ 8))
      · rw [if_pos hlt8, if_pos hlt8, hO', harr, hG7, hheap (m (G_ 7) + 1 + m (X_ 2)) (by omega) (by omega),
          hheap (m (G_ 8) + 1 + m (X_ 2)) (by omega) (by omega)]
      · rw [if_neg hlt8, if_neg hlt8])
  have hall' := hall.congr (Q := fun m => (List.range (m (m (G_ 7)))).all (fun idx => if idx < m (m (G_ 8)) then
        decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + idx)) 0 =
          (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + idx)) 0) else false))
    (fun m hm => by
      dsimp only
      rw [hm.2.1]
      apply all_congr_mem
      intro i _
      exact idxP_write m i hm.1.2.1 hm.1.2.2.2.1 hm.1.2.2.2.2.2.1)
  have e1 := loadM_spec (G_ 7) (G_ 9) (by constructor <;> addr3) (ArgsPre2 n)
  have e2 := loadM_spec (G_ 8) (G_ 10) (by constructor <;> addr3) (fun m => ArgsPre2 n m ∧ m (G_ 9) = m (m (G_ 7)))
  have t2 := TestSpec.after e2 hall'
    (Q := fun m => (List.range (m (m (G_ 7)))).all (fun idx => if idx < m (m (G_ 8)) then
        decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + idx)) 0 =
          (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + idx)) 0) else false))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.2.2
      obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable (fun x hx => by simp at hx; subst hx; constructor <;> addr3)
        (by decide) (by decide) (by decide) hag hm.1
      refine ⟨hA, ?_, ?_⟩
      · rw [hag.var (G_ 9) (lt_hp hhp (by decide)) (by decide) (by decide), hG7,
          hheap _ hm.1.2.1 (by have := hm.1.2.2.1; omega)]; exact hm.2
      · rw [hp.1, hG8, hheap _ hm.1.2.2.2.1 (by have := hm.1.2.2.2.2.1; omega)])
    (fun m m₁ hm hag hp => by
      have hV : ∀ x, x ∈ [G_ 10] → x < IN := fun x hx => by simp at hx; subst hx; addr3
      have hhp : 200 ≤ m HP := hm.1.1.2.2
      obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable (fun x hx => by simp at hx; subst hx; constructor <;> addr3)
        (by decide) (by decide) (by decide) hag hm.1
      obtain ⟨_, hq7, hq7', hq8, hq8', hO1, hO2, _⟩ := hm.1
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := hag.arrAt hV _ hO1 hO2
      dsimp only
      rw [hG7, hG8, hO', harr, hheap _ hq7 (by omega), hheap _ hq8 (by omega)]
      apply all_congr_mem
      intro idx hidx
      rw [List.mem_range] at hidx
      by_cases hlt8 : idx < m (m (G_ 8))
      · rw [if_pos hlt8, if_pos hlt8, hheap (m (G_ 7) + 1 + idx) (by omega) (by omega),
          hheap (m (G_ 8) + 1 + idx) (by omega) (by omega)]
      · rw [if_neg hlt8, if_neg hlt8])
  have t1 := TestSpec.after e1 t2
    (Q := fun m => (List.range (m (m (G_ 7)))).all (fun idx => if idx < m (m (G_ 8)) then
        decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + idx)) 0 =
          (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + idx)) 0) else false))
    (fun m m₁ hm hag hp => by
      obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable (fun x hx => by simp at hx; subst hx; constructor <;> addr3)
        (by decide) (by decide) (by decide) hag hm
      exact ⟨hA, by rw [hp.1, hG7, hheap _ hm.2.1 (by have := hm.2.2.1; omega)]⟩)
    (fun m m₁ hm hag hp => by
      have hV : ∀ x, x ∈ [G_ 9] → x < IN := fun x hx => by simp at hx; subst hx; addr3
      obtain ⟨hA, hG7, hG8, hO', hheap⟩ := ArgsPre2.stable (fun x hx => by simp at hx; subst hx; constructor <;> addr3)
        (by decide) (by decide) (by decide) hag hm
      obtain ⟨_, hq7, hq7', hq8, hq8', hO1, hO2, _⟩ := hm
      have harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := hag.arrAt hV _ hO1 hO2
      dsimp only
      rw [hG7, hG8, hO', harr, hheap _ hq7 (by omega), hheap _ hq8 (by omega)]
      apply all_congr_mem
      intro idx hidx
      rw [List.mem_range] at hidx
      by_cases hlt8 : idx < m (m (G_ 8))
      · rw [if_pos hlt8, if_pos hlt8, hheap (m (G_ 7) + 1 + idx) (by omega) (by omega),
          hheap (m (G_ 8) + 1 + idx) (by omega) (by omega)]
      · rw [if_neg hlt8, if_neg hlt8])
  unfold argsEqTest
  exact t1.mono (fun x hx => hx) (by omega) (fun m hm => hm)


/-! ### The signature test -/

/-- The context of the canonicalisation body: instance context, current index `I_ 0 < |nodes|`,
identifier prefix at `OUT_ 0` in the heap. -/
def CPre (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  InstCtx k g m ∧ m (I_ 0) < m NN ∧ IN ≤ m (OUT_ 0) ∧ m (OUT_ 0) + 1 + m (m (OUT_ 0)) ≤ m HP

/-- The precondition of the signature test: additionally `X_ 1 < I_ 0`. -/
def SPre (k : ℕ) (g : GInstance) (m : Mem) : Prop := CPre k g m ∧ m (X_ 1) < m (I_ 0)

theorem SPre.stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hI : I_ 0 ∉ V)
    (hO : OUT_ 0 ∉ V) (hX : X_ 1 ∉ V) {m m₁ : Mem} (hag : Agree m m₁ V) (h : SPre k g m) :
    SPre k g m₁ ∧ m₁ (I_ 0) = m (I_ 0) ∧ m₁ (OUT_ 0) = m (OUT_ 0) ∧ m₁ (X_ 1) = m (X_ 1) ∧
      m₁ NODES = m NODES ∧ (∀ x, IN ≤ x → x < m HP → m₁ x = m x) ∧
      arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := by
  obtain ⟨⟨hm, hj, hO1, hO2⟩, hx⟩ := h
  have hhp : 200 ≤ m HP := hm.ctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2.1
  have hI' : m₁ (I_ 0) = m (I_ 0) := hag.var (I_ 0) (lt_hp hhp (by decide)) (by decide) hI
  have hO' : m₁ (OUT_ 0) = m (OUT_ 0) := hag.var (OUT_ 0) (lt_hp hhp (by decide)) (by decide) hO
  have hX' : m₁ (X_ 1) = m (X_ 1) := hag.var (X_ 1) (lt_hp hhp (by decide)) (by decide) hX
  have hheap : ∀ x, IN ≤ x → x < m HP → m₁ x = m x := fun x h1 h2 => hag.heap hV' x h1 h2
  refine ⟨⟨⟨hm.of_agree hag hV, ?_, ?_, ?_⟩, ?_⟩, hI', hO', hX',
    hag.var NODES (lt_hp hhp (by decide)) (by decide) (fun h => (hV NODES h).2.2 (by decide)), hheap,
    hag.arrAt hV' _ hO1 hO2⟩
  · rw [hI', hag.var NN (lt_hp hhp (by decide)) (by decide) (fun h => (hV NN h).2.2 (by decide))]; exact hj
  · rw [hO']; exact hO1
  · rw [hO', hheap _ hO1 (by omega)]; exact le_trans hO2 hag.2
  · rw [hX', hI']; exact hx

/-- The node records of `X_ 1` and `I_ 0`. -/
theorem SPre.nodes {k : ℕ} {g : GInstance} {m : Mem} (h : SPre k g m) :
    (IN ≤ m NODES + 1 + m (X_ 1) ∧ m NODES + 1 + m (X_ 1) < m HP ∧ IN ≤ m (m NODES + 1 + m (X_ 1)) ∧
      m (m NODES + 1 + m (X_ 1)) + 2 ≤ m HP ∧
      RepNode m IN (m HP) (m (m NODES + 1 + m (X_ 1))) (g.base.nodes.getD (m (X_ 1)) (.src 0))) ∧
    (IN ≤ m NODES + 1 + m (I_ 0) ∧ m NODES + 1 + m (I_ 0) < m HP ∧ IN ≤ m (m NODES + 1 + m (I_ 0)) ∧
      m (m NODES + 1 + m (I_ 0)) + 2 ≤ m HP ∧
      RepNode m IN (m HP) (m (m NODES + 1 + m (I_ 0))) (g.base.nodes.getD (m (I_ 0)) (.src 0))) := by
  obtain ⟨⟨hm, hj, _, _⟩, hx⟩ := h
  have hj' : m (I_ 0) < g.base.nodes.length := by rw [← hm.nn]; exact hj
  have hx' : m (X_ 1) < g.base.nodes.length := by omega
  obtain ⟨a1, a2, a3, a4⟩ := hm.node_rec _ hx'
  obtain ⟨b1, b2, b3, b4⟩ := hm.node_rec _ hj'
  refine ⟨⟨a1, a2, a3, repNode_size a4, ?_⟩, ⟨b1, b2, b3, repNode_size b4, ?_⟩⟩
  · rw [List.getD_eq_getElem _ _ hx']; exact a4
  · rw [List.getD_eq_getElem _ _ hj']; exact b4

/-- Sources: compare the source indices. -/
def srcSigTest : Cmd := .seq (field1M (G_ 1) (G_ 5)) (.seq (field1M (G_ 2) (G_ 6)) (eqTest (G_ 5) (G_ 6)))

/-- Compare the lengths of the argument arrays at `G_ 7`, `G_ 8`. -/
def lenEqTest : Cmd := .seq (load (G_ 9) (G_ 7)) (.seq (load (G_ 10) (G_ 8)) (eqTest (G_ 9) (G_ 10)))

/-- Applications: same symbol, same number of arguments, same identifiers of the arguments. -/
def appSigTest : Cmd :=
  .seq (field1M (G_ 1) (G_ 5)) (.seq (field1M (G_ 2) (G_ 6)) (.seq (field2M (G_ 1) (G_ 7))
    (.seq (field2M (G_ 2) (G_ 8)) (andM (andM (eqTest (G_ 5) (G_ 6)) lenEqTest) argsEqTest))))

/-- `sigWith ids nodes[X_ 1] = sigWith ids nodes[I_ 0]`. -/
def sigEqTest : Cmd :=
  .seq (elemM NODES (X_ 1) (G_ 1)) (.seq (elemM NODES (I_ 0) (G_ 2)) (.seq (load (G_ 3) (G_ 1))
    (.seq (load (G_ 4) (G_ 2)) (.ite (.eq (G_ 3) (G_ 4)) (.ite (.eq (G_ 3) ZERO) srcSigTest appSigTest)
      (setc FLAG 0)))))

/-- The state after the node pointers and tags are loaded. -/
def SPre4 (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  SPre k g m ∧ m (G_ 1) = m (m NODES + 1 + m (X_ 1)) ∧ m (G_ 2) = m (m NODES + 1 + m (I_ 0)) ∧
    m (G_ 3) = m (m (G_ 1)) ∧ m (G_ 4) = m (m (G_ 2))

theorem SPre4.stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hI : I_ 0 ∉ V)
    (hO : OUT_ 0 ∉ V) (hX : X_ 1 ∉ V) (h1 : G_ 1 ∉ V) (h2 : G_ 2 ∉ V) (h3 : G_ 3 ∉ V) (h4 : G_ 4 ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : SPre4 k g m) :
    SPre4 k g m₁ ∧ m₁ (G_ 1) = m (G_ 1) ∧ m₁ (G_ 2) = m (G_ 2) ∧ m₁ (G_ 3) = m (G_ 3) ∧ m₁ (G_ 4) = m (G_ 4) ∧
      m₁ (OUT_ 0) = m (OUT_ 0) ∧ (∀ x, IN ≤ x → x < m HP → m₁ x = m x) ∧
      arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := by
  obtain ⟨hs, hg1, hg2, hg3, hg4⟩ := h
  have hhp : 200 ≤ m HP := hs.1.1.ctx.2.2
  obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g hV hI hO hX hag hs
  obtain ⟨⟨a1, a2, a3, a4, _⟩, ⟨b1, b2, b3, b4, _⟩⟩ := hs.nodes
  have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) h1
  have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) h2
  have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) h3
  have hG4 : m₁ (G_ 4) = m (G_ 4) := hag.var (G_ 4) (lt_hp hhp (by decide)) (by decide) h4
  refine ⟨⟨hs', ?_, ?_, ?_, ?_⟩, hG1, hG2, hG3, hG4, hO', hheap, harr⟩
  · rw [hG1, hN', hX', hheap _ a1 a2]; exact hg1
  · rw [hG2, hN', hI', hheap _ b1 b2]; exact hg2
  · rw [hG3, hG1, hheap _ (by rw [hg1]; exact a3) (by rw [hg1]; omega)]; exact hg3
  · rw [hG4, hG2, hheap _ (by rw [hg2]; exact b3) (by rw [hg2]; omega)]; exact hg4

theorem SPre4.recs {k : ℕ} {g : GInstance} {m : Mem} (h : SPre4 k g m) :
    IN ≤ m (G_ 1) ∧ m (G_ 1) + 2 ≤ m HP ∧ IN ≤ m (G_ 2) ∧ m (G_ 2) + 2 ≤ m HP ∧
      RepNode m IN (m HP) (m (G_ 1)) (g.base.nodes.getD (m (X_ 1)) (.src 0)) ∧
      RepNode m IN (m HP) (m (G_ 2)) (g.base.nodes.getD (m (I_ 0)) (.src 0)) := by
  obtain ⟨hs, hg1, hg2, _, _⟩ := h
  obtain ⟨⟨_, _, a3, a4, a5⟩, ⟨_, _, b3, b4, b5⟩⟩ := hs.nodes
  rw [hg1, hg2]
  exact ⟨a3, a4, b3, b4, a5, b5⟩

/-- The value of the signature test in terms of the record cells. -/
def sigVal (m : Mem) (p₁ p₂ : ℕ) : Bool :=
  if m p₁ = m p₂ then
    (if m p₁ = 0 then decide (m (p₁ + 1) = m (p₂ + 1))
     else (decide (m (p₁ + 1) = m (p₂ + 1)) && decide (m (m (p₁ + 2)) = m (m (p₂ + 2)))) &&
       (List.range (m (m (p₁ + 2)))).all (fun idx => if idx < m (m (p₂ + 2)) then
         decide ((arrAt m (m (OUT_ 0))).getD (m (m (p₁ + 2) + 1 + idx)) 0 =
           (arrAt m (m (OUT_ 0))).getD (m (m (p₂ + 2) + 1 + idx)) 0)
         else false))
  else false

theorem srcSigTest_spec (k : ℕ) (g : GInstance) :
    TestSpec srcSigTest [G_ 5, G_ 6, FLAG] 7 (fun m => (SPre4 k g m ∧ m (G_ 3) = m (G_ 4)) ∧ m (G_ 3) = m ZERO)
      (fun m => decide (m (m (G_ 1) + 1) = m (m (G_ 2) + 1))) := by
  have hs5 : SafeVars [G_ 5] := safeVars_of_decide _ (by decide)
  have hs6 : SafeVars [G_ 6] := safeVars_of_decide _ (by decide)
  let Pre0 : Mem → Prop := fun m => (SPre4 k g m ∧ m (G_ 3) = m (G_ 4)) ∧ m (G_ 3) = m ZERO
  have e1 := field1M_spec (G_ 1) (G_ 5) (by constructor <;> addr3) (by decide) Pre0 (fun m hm => hm.1.1.1.1.1.ctx)
    (fun m hm => hm.1.1.recs.1)
  let Pre1 : Mem → Prop := fun m => Pre0 m ∧ m (G_ 5) = m (m (G_ 1) + 1)
  have e2 := field1M_spec (G_ 2) (G_ 6) (by constructor <;> addr3) (by decide) Pre1 (fun m hm => hm.1.1.1.1.1.1.ctx)
    (fun m hm => hm.1.1.1.recs.2.2.1)
  have t2 := TestSpec.after e2 (eqTest_spec (G_ 5) (G_ 6) (fun _ => True))
    (Q := fun m => decide (m (G_ 5) = m (m (G_ 2) + 1))) (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.1.ctx.2.2
      dsimp only
      rw [hp.1, hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t1 := TestSpec.after e1 t2 (Q := fun m => decide (m (m (G_ 1) + 1) = m (m (G_ 2) + 1)))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      obtain ⟨h4, hG1, hG2, hG3, hG4, _, hheap, _⟩ := SPre4.stable k g hs5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hag hm.1.1
      obtain ⟨a3, a4, _, _, _, _⟩ := hm.1.1.recs
      refine ⟨⟨⟨h4, by rw [hG3, hG4]; exact hm.1.2⟩, by
        rw [hG3, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2⟩, by
        rw [hp.1, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)]⟩)
    (fun m m₁ hm hag hp => by
      obtain ⟨h4, hG1, hG2, hG3, hG4, _, hheap, _⟩ := SPre4.stable k g hs5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hag hm.1.1
      obtain ⟨_, _, b3, b4, _, _⟩ := hm.1.1.recs
      dsimp only
      rw [hp.1, hG2, hheap (m (G_ 2) + 1) (by omega) (by omega)])
  unfold srcSigTest
  exact t1.mono (fun x hx => by simp at hx ⊢; tauto) (by omega) (fun m hm => hm)


/-- The precondition of `lenEqTest`: two heap pointers in `G_ 7`, `G_ 8`. -/
def LenPre (m : Mem) : Prop := Ctx m ∧ IN ≤ m (G_ 7) ∧ m (G_ 7) < m HP ∧ IN ≤ m (G_ 8) ∧ m (G_ 8) < m HP

theorem LenPre.stable {V : List ℕ} (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (h7 : G_ 7 ∉ V) (h8 : G_ 8 ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : LenPre m) :
    LenPre m₁ ∧ m₁ (G_ 7) = m (G_ 7) ∧ m₁ (G_ 8) = m (G_ 8) ∧ m₁ (m (G_ 7)) = m (m (G_ 7)) ∧
      m₁ (m (G_ 8)) = m (m (G_ 8)) := by
  obtain ⟨hctx, h1, h2, h3, h4⟩ := h
  have hhp : 200 ≤ m HP := hctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2
  have hG7 : m₁ (G_ 7) = m (G_ 7) := hag.var (G_ 7) (lt_hp hhp (by decide)) (by decide) h7
  have hG8 : m₁ (G_ 8) = m (G_ 8) := hag.var (G_ 8) (lt_hp hhp (by decide)) (by decide) h8
  refine ⟨⟨Ctx.of_agree hctx hag (fun x hx => (hV x hx).1), by rw [hG7]; exact h1,
    by rw [hG7]; exact lt_of_lt_of_le h2 hag.2, by rw [hG8]; exact h3, by rw [hG8]; exact lt_of_lt_of_le h4 hag.2⟩,
    hG7, hG8, hag.heap hV' _ h1 h2, hag.heap hV' _ h3 h4⟩

theorem lenEqTest_spec :
    TestSpec lenEqTest [G_ 9, G_ 10, FLAG] 5 LenPre (fun m => decide (m (m (G_ 7)) = m (m (G_ 8)))) := by
  have hs9 : ∀ x, x ∈ [G_ 9] → 5 ≤ x ∧ x < IN := fun x hx => by simp at hx; subst hx; constructor <;> addr3
  have hs10 : ∀ x, x ∈ [G_ 10] → 5 ≤ x ∧ x < IN := fun x hx => by simp at hx; subst hx; constructor <;> addr3
  have e1 := loadM_spec (G_ 7) (G_ 9) (by constructor <;> addr3) LenPre
  have e2 := loadM_spec (G_ 8) (G_ 10) (by constructor <;> addr3) (fun m => LenPre m ∧ m (G_ 9) = m (m (G_ 7)))
  have t2 := TestSpec.after e2 (eqTest_spec (G_ 9) (G_ 10) (fun _ => True))
    (Q := fun m => decide (m (G_ 9) = m (m (G_ 8)))) (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.2.2
      dsimp only
      rw [hp.1, hag.var (G_ 9) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t1 := TestSpec.after e1 t2 (Q := fun m => decide (m (m (G_ 7)) = m (m (G_ 8))))
    (fun m m₁ hm hag hp => by
      obtain ⟨hL, hG7, hG8, hc7, hc8⟩ := LenPre.stable hs9 (by decide) (by decide) hag hm
      exact ⟨hL, by rw [hp.1, hG7, hc7]⟩)
    (fun m m₁ hm hag hp => by
      obtain ⟨hL, hG7, hG8, hc7, hc8⟩ := LenPre.stable hs9 (by decide) (by decide) hag hm
      dsimp only
      rw [hp.1, hG8, hc8])
  unfold lenEqTest
  exact t1.mono (fun x hx => by simp at hx ⊢; tauto) (by omega) (fun m hm => hm)


/-- The precondition of `appSigTest`: both tags equal and nonzero. -/
def APre (k : ℕ) (g : GInstance) (m : Mem) : Prop := (SPre4 k g m ∧ m (G_ 3) = m (G_ 4)) ∧ m (G_ 3) ≠ m ZERO

theorem APre.ctx {k : ℕ} {g : GInstance} {m : Mem} (h : APre k g m) : Ctx m := h.1.1.1.1.1.ctx
theorem APre.inst {k : ℕ} {g : GInstance} {m : Mem} (h : APre k g m) : InstCtx k g m := h.1.1.1.1.1

theorem APre.stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hI : I_ 0 ∉ V)
    (hO : OUT_ 0 ∉ V) (hX : X_ 1 ∉ V) (h1 : G_ 1 ∉ V) (h2 : G_ 2 ∉ V) (h3 : G_ 3 ∉ V) (h4 : G_ 4 ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : APre k g m) :
    APre k g m₁ ∧ m₁ (G_ 1) = m (G_ 1) ∧ m₁ (G_ 2) = m (G_ 2) ∧ m₁ (OUT_ 0) = m (OUT_ 0) ∧
      (∀ x, IN ≤ x → x < m HP → m₁ x = m x) ∧ arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := by
  obtain ⟨⟨h4', h34⟩, hz⟩ := h
  have hhp : 200 ≤ m HP := h4'.1.1.1.ctx.2.2
  obtain ⟨hs', hG1, hG2, hG3, hG4, hO', hheap, harr⟩ := SPre4.stable k g hV hI hO hX h1 h2 h3 h4 hag h4'
  refine ⟨⟨⟨hs', by rw [hG3, hG4]; exact h34⟩, ?_⟩, hG1, hG2, hO', hheap, harr⟩
  rw [hG3, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (fun h => by have := (hV ZERO h).1; addr3)]
  exact hz

/-- Under `APre`, both nodes are applications. -/
theorem APre.apps {k : ℕ} {g : GInstance} {m : Mem} (h : APre k g m) :
    ∃ f₁ a₁ f₂ a₂, g.base.nodes.getD (m (X_ 1)) (.src 0) = .app f₁ a₁ ∧
      g.base.nodes.getD (m (I_ 0)) (.src 0) = .app f₂ a₂ ∧
      m (m (G_ 1) + 1) = f₁ ∧ RepArr m IN (m HP) (m (m (G_ 1) + 2)) a₁ ∧ m (G_ 1) + 3 ≤ m HP ∧
      m (m (G_ 2) + 1) = f₂ ∧ RepArr m IN (m HP) (m (m (G_ 2) + 2)) a₂ ∧ m (G_ 2) + 3 ≤ m HP := by
  obtain ⟨⟨h4, h34⟩, hz⟩ := h
  have hz0 := h4.1.1.1.ctx.2.1
  obtain ⟨_, _, _, _, r1, r2⟩ := h4.recs
  have ht1 : m (m (G_ 1)) ≠ 0 := by rw [← h4.2.2.2.1, ← hz0]; exact hz
  have ht2 : m (m (G_ 2)) ≠ 0 := by rw [← h4.2.2.2.2, ← h34, ← hz0]; exact hz
  rcases repNode_cases r1 with ⟨t1, _⟩ | ⟨t1, f₁, a₁, e1, c1, ra1⟩
  · exact absurd t1 ht1
  rcases repNode_cases r2 with ⟨t2, _⟩ | ⟨t2, f₂, a₂, e2, c2, ra2⟩
  · exact absurd t2 ht2
  refine ⟨f₁, a₁, f₂, a₂, e1, e2, c1, ra1, ?_, c2, ra2, ?_⟩
  · rw [e1] at r1; exact r1.2.1
  · rw [e2] at r2; exact r2.2.1

/-- The argument bounds under `APre` (without the size bound). -/
theorem APre.bounds {k : ℕ} {g : GInstance} {m : Mem} (h : APre k g m) :
    IN ≤ m (G_ 1) ∧ m (G_ 1) + 3 ≤ m HP ∧ IN ≤ m (G_ 2) ∧ m (G_ 2) + 3 ≤ m HP ∧
      IN ≤ m (m (G_ 1) + 2) ∧ m (m (G_ 1) + 2) + 1 + m (m (m (G_ 1) + 2)) ≤ m HP ∧
      IN ≤ m (m (G_ 2) + 2) ∧ m (m (G_ 2) + 2) + 1 + m (m (m (G_ 2) + 2)) ≤ m HP := by
  obtain ⟨_, _, _, _, _, _, _, ra1, b1, _, ra2, b2⟩ := h.apps
  obtain ⟨g1, g1'⟩ := repArr_bounds ra1
  obtain ⟨g2, g2'⟩ := repArr_bounds ra2
  obtain ⟨a3, _, b3, _, _, _⟩ := h.1.1.recs
  exact ⟨a3, b1, b3, b2, g1, g1', g2, g2'⟩

/-- The length of the first argument list is bounded by the size. -/
theorem APre.len_le {k : ℕ} {g : GInstance} {n : ℕ} (hn : Sized n g) {m : Mem} (h : APre k g m) :
    m (m (m (G_ 1) + 2)) ≤ n := by
  obtain ⟨f₁, a₁, _, _, e1, _, _, ra1, _⟩ := h.apps
  have hx : m (X_ 1) < g.base.nodes.length := by
    have := h.1.1.1.1.1.nn; have := h.1.1.1.1.2.1; have := h.1.1.1.2; omega
  rw [ra1.2.2.1]
  exact hn.args_getD _ hx f₁ a₁ e1

/-- The state after the four field loads of `appSigTest`. -/
def APre4 (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  APre k g m ∧ m (G_ 5) = m (m (G_ 1) + 1) ∧ m (G_ 6) = m (m (G_ 2) + 1) ∧ m (G_ 7) = m (m (G_ 1) + 2) ∧
    m (G_ 8) = m (m (G_ 2) + 2)

theorem APre4.stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hI : I_ 0 ∉ V)
    (hO : OUT_ 0 ∉ V) (hX : X_ 1 ∉ V) (h1 : G_ 1 ∉ V) (h2 : G_ 2 ∉ V) (h3 : G_ 3 ∉ V) (h4 : G_ 4 ∉ V)
    (h5 : G_ 5 ∉ V) (h6 : G_ 6 ∉ V) (h7 : G_ 7 ∉ V) (h8 : G_ 8 ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : APre4 k g m) :
    APre4 k g m₁ ∧ m₁ (G_ 1) = m (G_ 1) ∧ m₁ (G_ 2) = m (G_ 2) ∧ m₁ (G_ 5) = m (G_ 5) ∧ m₁ (G_ 6) = m (G_ 6) ∧
      m₁ (G_ 7) = m (G_ 7) ∧ m₁ (G_ 8) = m (G_ 8) ∧ m₁ (OUT_ 0) = m (OUT_ 0) ∧
      (∀ x, IN ≤ x → x < m HP → m₁ x = m x) ∧ arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := by
  obtain ⟨ha, hg5, hg6, hg7, hg8⟩ := h
  have hhp : 200 ≤ m HP := ha.1.1.1.1.1.ctx.2.2
  obtain ⟨a1, a2, b1, b2, _⟩ := ha.bounds
  obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g hV hI hO hX h1 h2 h3 h4 hag ha
  have hG5 : m₁ (G_ 5) = m (G_ 5) := hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) h5
  have hG6 : m₁ (G_ 6) = m (G_ 6) := hag.var (G_ 6) (lt_hp hhp (by decide)) (by decide) h6
  have hG7 : m₁ (G_ 7) = m (G_ 7) := hag.var (G_ 7) (lt_hp hhp (by decide)) (by decide) h7
  have hG8 : m₁ (G_ 8) = m (G_ 8) := hag.var (G_ 8) (lt_hp hhp (by decide)) (by decide) h8
  refine ⟨⟨ha', ?_, ?_, ?_, ?_⟩, hG1, hG2, hG5, hG6, hG7, hG8, hO', hheap, harr⟩
  · rw [hG5, hG1, hheap _ (by omega) (by omega)]; exact hg5
  · rw [hG6, hG2, hheap _ (by omega) (by omega)]; exact hg6
  · rw [hG7, hG1, hheap _ (by omega) (by omega)]; exact hg7
  · rw [hG8, hG2, hheap _ (by omega) (by omega)]; exact hg8

theorem APre4.argsPre {k : ℕ} {g : GInstance} {n : ℕ} (hn : Sized n g) {m : Mem} (h : APre4 k g m) :
    ArgsPre2 n m ∧ LenPre m := by
  obtain ⟨ha, _, _, hg7, hg8⟩ := h
  obtain ⟨_, _, _, _, g1, g1', g2, g2'⟩ := ha.bounds
  have hlen := ha.len_le hn
  obtain ⟨_, _, hO1, hO2⟩ := ha.1.1.1.1
  rw [← hg7] at g1 g1' hlen
  rw [← hg8] at g2 g2'
  exact ⟨⟨ha.1.1.1.1.1.ctx, g1, g1', g2, g2', hO1, hO2, hlen⟩, ha.1.1.1.1.1.ctx, g1, by omega, g2, by omega⟩

/-- The value of `appSigTest` in terms of the record cells. -/
def appVal (m : Mem) (p₁ p₂ : ℕ) : Bool :=
  (decide (m (p₁ + 1) = m (p₂ + 1)) && decide (m (m (p₁ + 2)) = m (m (p₂ + 2)))) &&
    (List.range (m (m (p₁ + 2)))).all (fun idx => if idx < m (m (p₂ + 2)) then
      decide ((arrAt m (m (OUT_ 0))).getD (m (m (p₁ + 2) + 1 + idx)) 0 =
        (arrAt m (m (OUT_ 0))).getD (m (m (p₂ + 2) + 1 + idx)) 0)
      else false)

def appSigV : List ℕ := [G_ 5] ++ ([G_ 6] ++ ([G_ 7] ++ ([G_ 8] ++ (([FLAG] ++ [G_ 9, G_ 10, FLAG]) ++ argsEqV))))

theorem appSigV_safe : SafeVars appSigV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
      (SafeVars.append (SafeVars.append (safeVars_of_decide _ (by decide)) (safeVars_of_decide _ (by decide)))
        argsEqV_safe))))

/-- `appVal` only depends on `OUT_ 0` and the heap below the heap pointer. -/
theorem appVal_stable' {m m₁ : Mem} {p₁ p₂ : ℕ}
    (hO : m₁ (OUT_ 0) = m (OUT_ 0)) (harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)))
    (hheap : ∀ x, IN ≤ x → x < m HP → m₁ x = m x)
    (hb : IN ≤ p₁ ∧ p₁ + 3 ≤ m HP ∧ IN ≤ p₂ ∧ p₂ + 3 ≤ m HP ∧
      IN ≤ m (p₁ + 2) ∧ m (p₁ + 2) + 1 + m (m (p₁ + 2)) ≤ m HP ∧
      IN ≤ m (p₂ + 2) ∧ m (p₂ + 2) + 1 + m (m (p₂ + 2)) ≤ m HP) :
    appVal m₁ p₁ p₂ = appVal m p₁ p₂ := by
  obtain ⟨a1, a2, b1, b2, g1, g1', g2, g2'⟩ := hb
  unfold appVal
  rw [hO, harr, hheap (p₁ + 1) (by omega) (by omega), hheap (p₂ + 1) (by omega) (by omega),
    hheap (p₁ + 2) (by omega) (by omega), hheap (p₂ + 2) (by omega) (by omega),
    hheap (m (p₁ + 2)) g1 (by omega), hheap (m (p₂ + 2)) g2 (by omega)]
  congr 1
  apply all_congr_mem
  intro idx hidx
  rw [List.mem_range] at hidx
  by_cases hlt : idx < m (m (p₂ + 2))
  · rw [if_pos hlt, if_pos hlt, hheap (m (p₁ + 2) + 1 + idx) (by omega) (by omega),
      hheap (m (p₂ + 2) + 1 + idx) (by omega) (by omega)]
  · rw [if_neg hlt, if_neg hlt]

theorem appVal_stable {m m₁ : Mem} (hG1 : m₁ (G_ 1) = m (G_ 1)) (hG2 : m₁ (G_ 2) = m (G_ 2))
    (hO : m₁ (OUT_ 0) = m (OUT_ 0)) (harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)))
    (hheap : ∀ x, IN ≤ x → x < m HP → m₁ x = m x)
    (hb : IN ≤ m (G_ 1) ∧ m (G_ 1) + 3 ≤ m HP ∧ IN ≤ m (G_ 2) ∧ m (G_ 2) + 3 ≤ m HP ∧
      IN ≤ m (m (G_ 1) + 2) ∧ m (m (G_ 1) + 2) + 1 + m (m (m (G_ 1) + 2)) ≤ m HP ∧
      IN ≤ m (m (G_ 2) + 2) ∧ m (m (G_ 2) + 2) + 1 + m (m (m (G_ 2) + 2)) ≤ m HP) :
    appVal m₁ (m₁ (G_ 1)) (m₁ (G_ 2)) = appVal m (m (G_ 1)) (m (G_ 2)) := by
  rw [hG1, hG2]; exact appVal_stable' hO harr hheap hb

theorem appSigTest_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec appSigTest appSigV (2 + 2 + 3 + 3 + ((3 + 5 + 3) + (n * (24 + 12) + n * 6 + 23) + 3)) (APre k g)
      (fun m => appVal m (m (G_ 1)) (m (G_ 2))) := by
  have hsG : ∀ i, i < 60 → SafeVars [G_ i] := fun i hi x hx => by simp at hx; subst hx; exact safeVars_G i hi
  have hsF : SafeVars [FLAG] := fun x hx => by simp at hx; subst hx; exact safeVars_FLAG
  have hs910 : SafeVars ([FLAG] ++ [G_ 9, G_ 10, FLAG]) := safeVars_of_decide _ (by decide)
  -- the conjunction
  have tf := eqTest_spec (G_ 5) (G_ 6) (APre4 k g)
  have tl := lenEqTest_spec.mono (fun x hx => hx) le_rfl (fun m (hm : APre4 k g m) => (hm.argsPre hn).2)
  have ta := (argsEqTest_spec n).mono (fun x hx => hx) le_rfl (fun m (hm : APre4 k g m) => (hm.argsPre hn).1)
  have tand1 := andM_spec tf tl (fun x hx => (hsF x hx).1) (fun m hm => hm.1.ctx)
    (fun m m₁ hm hag => (APre4.stable k g hsF (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hag hm).1)
    (fun m m₁ hm hag => by
      obtain ⟨_, _, _, _, _, hG7, hG8, _, hheap, _⟩ := APre4.stable k g hsF (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hag hm
      obtain ⟨⟨_, g1, g1', g2, g2', _⟩, _⟩ := hm.argsPre hn
      show decide (m₁ (m₁ (G_ 7)) = m₁ (m₁ (G_ 8))) = decide (m (m (G_ 7)) = m (m (G_ 8)))
      rw [hG7, hG8, hheap _ g1 (by omega), hheap _ g2 (by omega)])
  have tand2 := andM_spec tand1 ta (fun x hx => (hs910 x hx).1) (fun m hm => hm.1.ctx)
    (fun m m₁ hm hag => (APre4.stable k g hs910 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hag hm).1)
    (fun m m₁ hm hag => by
      obtain ⟨_, _, _, _, _, hG7, hG8, hO', hheap, harr⟩ := APre4.stable k g hs910 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hag hm
      obtain ⟨⟨_, g1, g1', g2, g2', _⟩, _⟩ := hm.argsPre hn
      show (List.range (m₁ (m₁ (G_ 7)))).all (fun idx => if idx < m₁ (m₁ (G_ 8)) then
          decide ((arrAt m₁ (m₁ (OUT_ 0))).getD (m₁ (m₁ (G_ 7) + 1 + idx)) 0 =
            (arrAt m₁ (m₁ (OUT_ 0))).getD (m₁ (m₁ (G_ 8) + 1 + idx)) 0) else false) =
        (List.range (m (m (G_ 7)))).all (fun idx => if idx < m (m (G_ 8)) then
          decide ((arrAt m (m (OUT_ 0))).getD (m (m (G_ 7) + 1 + idx)) 0 =
            (arrAt m (m (OUT_ 0))).getD (m (m (G_ 8) + 1 + idx)) 0) else false)
      rw [hG7, hG8, hO', harr, hheap _ g1 (by omega), hheap _ g2 (by omega)]
      apply all_congr_mem
      intro idx hidx
      rw [List.mem_range] at hidx
      by_cases hlt : idx < m (m (G_ 8))
      · rw [if_pos hlt, if_pos hlt, hheap (m (G_ 7) + 1 + idx) (by omega) (by omega),
          hheap (m (G_ 8) + 1 + idx) (by omega) (by omega)]
      · rw [if_neg hlt, if_neg hlt])
  -- the field loads
  have e4 := field2M_spec (G_ 2) (G_ 8) (by constructor <;> addr3) (by decide)
    (fun m => (APre k g m ∧ m (G_ 5) = m (m (G_ 1) + 1) ∧ m (G_ 6) = m (m (G_ 2) + 1)) ∧ m (G_ 7) = m (m (G_ 1) + 2))
    (fun m hm => hm.1.1.ctx) (fun m hm => hm.1.1.bounds.2.2.1)
  have t4 := TestSpec.after e4 tand2 (Q := fun m => appVal m (m (G_ 1)) (m (G_ 2)))
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 8 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm.1.1
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨a1, a2, b1, b2, _⟩ := hm.1.1.bounds
      have hG5 : m₁ (G_ 5) = m (G_ 5) := hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG6 : m₁ (G_ 6) = m (G_ 6) := hag.var (G_ 6) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG7 : m₁ (G_ 7) = m (G_ 7) := hag.var (G_ 7) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro ha' (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · rw [hG5, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)]; exact hm.1.2.1
      · rw [hG6, hG2, hheap (m (G_ 2) + 1) (by omega) (by omega)]; exact hm.1.2.2
      · rw [hG7, hG1, hheap (m (G_ 1) + 2) (by omega) (by omega)]; exact hm.2
      · rw [hp.1, hG2, hheap (m (G_ 2) + 2) (by omega) (by omega)])
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 8 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm.1.1
      obtain ⟨a1, a2, b1, b2, g1, g1', g2, g2'⟩ := hm.1.1.bounds
      have hG5 : m₁ (G_ 5) = m (G_ 5) := hag.var (G_ 5) (lt_hp hm.1.1.ctx.2.2 (by decide)) (by decide) (by decide)
      have hG6 : m₁ (G_ 6) = m (G_ 6) := hag.var (G_ 6) (lt_hp hm.1.1.ctx.2.2 (by decide)) (by decide) (by decide)
      have hG7 : m₁ (G_ 7) = m (G_ 7) := hag.var (G_ 7) (lt_hp hm.1.1.ctx.2.2 (by decide)) (by decide) (by decide)
      show ((decide (m₁ (G_ 5) = m₁ (G_ 6)) && decide (m₁ (m₁ (G_ 7)) = m₁ (m₁ (G_ 8)))) &&
        (List.range (m₁ (m₁ (G_ 7)))).all (fun idx => if idx < m₁ (m₁ (G_ 8)) then
          decide ((arrAt m₁ (m₁ (OUT_ 0))).getD (m₁ (m₁ (G_ 7) + 1 + idx)) 0 =
            (arrAt m₁ (m₁ (OUT_ 0))).getD (m₁ (m₁ (G_ 8) + 1 + idx)) 0) else false)) = appVal m (m (G_ 1)) (m (G_ 2))
      unfold appVal
      rw [hG5, hG6, hG7, hp.1, hO', harr, hm.1.2.1, hm.1.2.2, hm.2, hheap (m (m (G_ 1) + 2)) g1 (by omega),
        hheap (m (m (G_ 2) + 2)) g2 (by omega)]
      congr 1
      apply all_congr_mem
      intro idx hidx
      rw [List.mem_range] at hidx
      by_cases hlt : idx < m (m (m (G_ 2) + 2))
      · rw [if_pos hlt, if_pos hlt, hheap (m (m (G_ 1) + 2) + 1 + idx) (by omega) (by omega),
          hheap (m (m (G_ 2) + 2) + 1 + idx) (by omega) (by omega)]
      · rw [if_neg hlt, if_neg hlt])
  have e3 := field2M_spec (G_ 1) (G_ 7) (by constructor <;> addr3) (by decide)
    (fun m => APre k g m ∧ m (G_ 5) = m (m (G_ 1) + 1) ∧ m (G_ 6) = m (m (G_ 2) + 1))
    (fun m hm => hm.1.ctx) (fun m hm => hm.1.bounds.1)
  have t3 := TestSpec.after e3 t4 (Q := fun m => appVal m (m (G_ 1)) (m (G_ 2)))
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 7 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm.1
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      obtain ⟨a1, a2, b1, b2, _⟩ := hm.1.bounds
      have hG5 : m₁ (G_ 5) = m (G_ 5) := hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG6 : m₁ (G_ 6) = m (G_ 6) := hag.var (G_ 6) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro (And.intro ha' (And.intro ?_ ?_)) ?_
      · rw [hG5, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)]; exact hm.2.1
      · rw [hG6, hG2, hheap (m (G_ 2) + 1) (by omega) (by omega)]; exact hm.2.2
      · rw [hp.1, hG1, hheap (m (G_ 1) + 2) (by omega) (by omega)])
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 7 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm.1
      exact appVal_stable hG1 hG2 hO' harr hheap hm.1.bounds)
  have e2 := field1M_spec (G_ 2) (G_ 6) (by constructor <;> addr3) (by decide)
    (fun m => APre k g m ∧ m (G_ 5) = m (m (G_ 1) + 1)) (fun m hm => hm.1.ctx) (fun m hm => hm.1.bounds.2.2.1)
  have t2 := TestSpec.after e2 t3 (Q := fun m => appVal m (m (G_ 1)) (m (G_ 2)))
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 6 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm.1
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      obtain ⟨a1, a2, b1, b2, _⟩ := hm.1.bounds
      have hG5 : m₁ (G_ 5) = m (G_ 5) := hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro ha' (And.intro ?_ ?_)
      · rw [hG5, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)]; exact hm.2
      · rw [hp.1, hG2, hheap (m (G_ 2) + 1) (by omega) (by omega)])
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 6 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm.1
      exact appVal_stable hG1 hG2 hO' harr hheap hm.1.bounds)
  have e1 := field1M_spec (G_ 1) (G_ 5) (by constructor <;> addr3) (by decide) (APre k g)
    (fun m hm => hm.ctx) (fun m hm => hm.bounds.1)
  have t1 := TestSpec.after e1 t2 (Q := fun m => appVal m (m (G_ 1)) (m (G_ 2)))
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 5 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm
      obtain ⟨a1, a2, b1, b2, _⟩ := hm.bounds
      exact And.intro ha' (by rw [hp.1, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)]))
    (fun m m₁ hm hag hp => by
      obtain ⟨ha', hG1, hG2, hO', hheap, harr⟩ := APre.stable k g (hsG 5 (by norm_num)) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hag hm
      exact appVal_stable hG1 hG2 hO' harr hheap hm.bounds)
  unfold appSigTest
  exact t1.mono (fun x hx => hx) (by omega) (fun m hm => hm)


theorem sigVal_eq (m : Mem) (p₁ p₂ : ℕ) : sigVal m p₁ p₂ =
    (if m p₁ = m p₂ then (if m p₁ = 0 then decide (m (p₁ + 1) = m (p₂ + 1)) else appVal m p₁ p₂) else false) := rfl

/-- `sigVal` at two node pointers only depends on the record cells below the heap pointer. -/
theorem sigVal_stable {m m₁ : Mem} {p₁ p₂ : ℕ} {nd₁ nd₂ : Node} (r1 : RepNode m IN (m HP) p₁ nd₁)
    (r2 : RepNode m IN (m HP) p₂ nd₂) (hO : m₁ (OUT_ 0) = m (OUT_ 0))
    (harr : arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0))) (hheap : ∀ x, IN ≤ x → x < m HP → m₁ x = m x) :
    sigVal m₁ p₁ p₂ = sigVal m p₁ p₂ := by
  have a3 := r1.1
  have a4 := repNode_size r1
  have b3 := r2.1
  have b4 := repNode_size r2
  rw [sigVal_eq, sigVal_eq, hheap p₁ a3 (by omega), hheap p₂ b3 (by omega)]
  rcases repNode_cases r1 with ⟨t1, _⟩ | ⟨t1, f₁, a₁, e1, _, ra1⟩ <;>
  rcases repNode_cases r2 with ⟨t2, _⟩ | ⟨t2, f₂, a₂, e2, _, ra2⟩
  · rw [t1, t2]; simp only [↓reduceIte]
    rw [hheap (p₁ + 1) (by omega) (by omega), hheap (p₂ + 1) (by omega) (by omega)]
  · rw [t1, t2]; simp
  · rw [t1, t2]; simp
  · rw [t1, t2]; simp only [↓reduceIte, Nat.one_ne_zero, if_false]
    rw [e1] at r1; rw [e2] at r2
    obtain ⟨g1, g1'⟩ := repArr_bounds ra1
    obtain ⟨g2, g2'⟩ := repArr_bounds ra2
    exact appVal_stable' hO harr hheap ⟨a3, r1.2.1, b3, r2.2.1, g1, g1', g2, g2'⟩

def sigV : List ℕ := [G_ 1] ++ ([G_ 2] ++ ([G_ 3] ++ ([G_ 4] ++ (([G_ 5, G_ 6, FLAG] ++ appSigV) ++ [FLAG]))))

theorem sigV_safe : SafeVars sigV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
      (SafeVars.append (SafeVars.append (safeVars_of_decide _ (by decide)) appSigV_safe)
        (safeVars_of_decide _ (by decide))))))

/-- The step bound of `sigEqTest`. -/
def sigB (n : ℕ) : ℕ := 3 + 3 + 1 + 1 + ((7 + (2 + 2 + 3 + 3 + ((3 + 5 + 3) + (n * (24 + 12) + n * 6 + 23) + 3)) + 2) + 1 + 2)

theorem sigEqTest_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec sigEqTest sigV (sigB n) (SPre k g)
      (fun m => decide (Instance.sigWith (arrAt m (m (OUT_ 0))) (g.base.nodes.getD (m (X_ 1)) (.src 0)) =
        Instance.sigWith (arrAt m (m (OUT_ 0))) (g.base.nodes.getD (m (I_ 0)) (.src 0)))) := by
  have hsG : ∀ i, i < 60 → SafeVars [G_ i] := fun i hi x hx => by simp at hx; subst hx; exact safeVars_G i hi
  -- the conditional on the tags
  have tsrc := srcSigTest_spec k g
  have tapp := appSigTest_spec k g n hn
  have tin := TestSpec.ite' (G_ 3) ZERO tsrc tapp
  have tout := TestSpec.ite' (G_ 3) (G_ 4) tin (falseTest_spec (fun m => SPre4 k g m ∧ m (G_ 3) ≠ m (G_ 4)))
  have tout' := tout.congr (Q := fun m => sigVal m (m (G_ 1)) (m (G_ 2))) (fun m hm => by
    dsimp only
    rw [sigVal_eq, ← hm.2.2.2.1, ← hm.2.2.2.2, hm.1.1.1.ctx.2.1])
  -- the loads
  let Pre0 : Mem → Prop := fun m => SPre k g m ∧ m (G_ 1) = m (m NODES + 1 + m (X_ 1))
  let Pre1 : Mem → Prop := fun m => Pre0 m ∧ m (G_ 2) = m (m NODES + 1 + m (I_ 0))
  let Pre2 : Mem → Prop := fun m => Pre1 m ∧ m (G_ 3) = m (m (G_ 1))
  have e3 := loadM_spec (G_ 2) (G_ 4) (by constructor <;> addr3) Pre2
  have t3 := TestSpec.after e3 tout' (Q := fun m => sigVal m (m (G_ 1)) (m (G_ 2)))
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 4 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm.1.1.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      obtain ⟨⟨a1, a2, a3, a4, _⟩, ⟨b1, b2, b3, b4, _⟩⟩ := hm.1.1.1.nodes
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine ⟨hs', ?_, ?_, ?_, ?_⟩
      · rw [hG1, hN', hX', hheap _ a1 a2]; exact hm.1.1.2
      · rw [hG2, hN', hI', hheap _ b1 b2]; exact hm.1.2
      · rw [hG3, hG1, hheap (m (G_ 1)) (by rw [hm.1.1.2]; exact a3) (by rw [hm.1.1.2]; omega)]; exact hm.2
      · rw [hp.1, hG2, hheap (m (G_ 2)) (by rw [hm.1.2]; exact b3) (by rw [hm.1.2]; omega)])
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 4 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm.1.1.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      obtain ⟨⟨_, _, _, _, r1⟩, ⟨_, _, _, _, r2⟩⟩ := hm.1.1.1.nodes
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) (by decide)
      dsimp only
      rw [hG1, hG2, hm.1.1.2, hm.1.2]
      exact sigVal_stable r1 r2 hO' harr hheap)
  have e2 := loadM_spec (G_ 1) (G_ 3) (by constructor <;> addr3) Pre1
  have t2 := TestSpec.after e2 t3 (Q := fun m => sigVal m (m (G_ 1)) (m (G_ 2)))
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 3 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm.1.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      obtain ⟨⟨a1, a2, a3, a4, _⟩, ⟨b1, b2, b3, b4, _⟩⟩ := hm.1.1.nodes
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro (And.intro (And.intro hs' ?_) ?_) ?_
      · rw [hG1, hN', hX', hheap _ a1 a2]; exact hm.1.2
      · rw [hG2, hN', hI', hheap _ b1 b2]; exact hm.2
      · rw [hp.1, hG1, hheap (m (G_ 1)) (by rw [hm.1.2]; exact a3) (by rw [hm.1.2]; omega)])
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 3 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm.1.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      obtain ⟨⟨_, _, _, _, r1⟩, ⟨_, _, _, _, r2⟩⟩ := hm.1.1.nodes
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) (by decide)
      dsimp only
      rw [hG1, hG2, hm.1.2, hm.2]
      exact sigVal_stable r1 r2 hO' harr hheap)
  have e1 := elemM_spec NODES (I_ 0) (G_ 2) (by constructor <;> addr3) (by decide) (by decide) Pre0
    (fun m hm => hm.1.1.1.ctx) (fun m hm => hm.1.1.1.arr_nodes.1)
  have t1 := TestSpec.after e1 t2 (Q := fun m => sigVal m (m (G_ 1)) (m (m NODES + 1 + m (I_ 0))))
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 2 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      obtain ⟨⟨a1, a2, a3, a4, _⟩, ⟨b1, b2, b3, b4, _⟩⟩ := hm.1.nodes
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro (And.intro hs' ?_) ?_
      · rw [hG1, hN', hX', hheap _ a1 a2]; exact hm.2
      · rw [hp.1, hN', hI', hheap _ b1 b2])
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 2 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      obtain ⟨⟨_, _, _, _, r1⟩, ⟨b1, b2, _, _, r2⟩⟩ := hm.1.nodes
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      dsimp only
      rw [hG1, hp.1, hm.2]
      exact sigVal_stable r1 r2 hO' harr hheap)
  have e0 := elemM_spec NODES (X_ 1) (G_ 1) (by constructor <;> addr3) (by decide) (by decide) (SPre k g)
    (fun m hm => hm.1.1.ctx) (fun m hm => hm.1.1.arr_nodes.1)
  have t0 := TestSpec.after e0 t1
    (Q := fun m => sigVal m (m (m NODES + 1 + m (X_ 1))) (m (m NODES + 1 + m (I_ 0))))
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 1 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm
      obtain ⟨⟨a1, a2, _⟩, _⟩ := hm.nodes
      exact And.intro hs' (by rw [hp.1, hN', hX', hheap _ a1 a2]))
    (fun m m₁ hm hag hp => by
      obtain ⟨hs', hI', hO', hX', hN', hheap, harr⟩ := SPre.stable k g (hsG 1 (by norm_num)) (by decide)
        (by decide) (by decide) hag hm
      obtain ⟨⟨_, _, _, _, r1⟩, ⟨b1, b2, _, _, r2⟩⟩ := hm.nodes
      dsimp only
      rw [hp.1, hN', hI', hheap _ b1 b2]
      exact sigVal_stable r1 r2 hO' harr hheap)
  unfold sigEqTest
  refine (t0.mono (V' := sigV) (fun x hx => hx) (by unfold sigB; omega) (fun m hm => hm)).congr (fun m hm => ?_)
  dsimp only
  obtain ⟨⟨_, _, _, _, r1⟩, ⟨_, _, _, _, r2⟩⟩ := hm.nodes
  rw [sigEq_cells _ r1 r2]
  rfl


/-! ### `canonStep` and `canonIds` -/

theorem CPre.stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hI : I_ 0 ∉ V)
    (hO : OUT_ 0 ∉ V) {m m₁ : Mem} (hag : Agree m m₁ V) (h : CPre k g m) :
    CPre k g m₁ ∧ m₁ (I_ 0) = m (I_ 0) ∧ m₁ (OUT_ 0) = m (OUT_ 0) ∧
      arrAt m₁ (m (OUT_ 0)) = arrAt m (m (OUT_ 0)) := by
  obtain ⟨hm, hj, hO1, hO2⟩ := h
  have hhp : 200 ≤ m HP := hm.ctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2.1
  have hI' : m₁ (I_ 0) = m (I_ 0) := hag.var (I_ 0) (lt_hp hhp (by decide)) (by decide) hI
  have hO' : m₁ (OUT_ 0) = m (OUT_ 0) := hag.var (OUT_ 0) (lt_hp hhp (by decide)) (by decide) hO
  refine ⟨⟨hm.of_agree hag hV, ?_, ?_, ?_⟩, hI', hO', hag.arrAt hV' _ hO1 hO2⟩
  · rw [hI', hag.var NN (lt_hp hhp (by decide)) (by decide) (fun h => (hV NN h).2.2 (by decide))]; exact hj
  · rw [hO']; exact hO1
  · rw [hO', hag.heap hV' _ hO1 (by omega)]; exact le_trans hO2 hag.2

/-- `VAL := canonStep ids I_ 0` (with `ids` the array at `OUT_ 0`, of length `I_ 0`). -/
def canonStepM : Cmd :=
  .seq (firstIndexM 1 (G_ 20) (I_ 0) sigEqTest)
    (.ite (.lt (G_ 20) (I_ 0)) (getDM (OUT_ 0) (G_ 20) VAL) (mov VAL (I_ 0)))

def canonV : List ℕ := fiV 1 (G_ 20) sigV ++ [VAL]

theorem canonV_safe : SafeVars canonV :=
  SafeVars.append (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
    (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
      (SafeVars.cons safeVars_FLAG sigV_safe))))) (safeVars_of_decide _ (by decide))

/-- The step bound of `canonStepM`. -/
def canonB (n : ℕ) : ℕ := n * (sigB n + 9) + 5 + (2 + 6)

theorem canonStepM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec canonStepM canonV (canonB n) (CPre k g)
      (fun m m' => m' VAL = g.base.canonStep (arrAt m (m (OUT_ 0))) (m (I_ 0))) := by
  have hfi := firstIndexM_spec 1 (G_ 20) (I_ 0) n (by norm_num) (sigEqTest_spec k g n hn)
    (fun x hx => ⟨(sigV_safe x hx).1, (sigV_safe x hx).2.1⟩) (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide)
    (fun m hm => hm.1.ctx) (fun m hm => by have := hm.1.nn; have := hm.2.1; have := hn.nodes; omega)
    (fun m m₁ hm hag => (CPre.stable k g (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
      (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
      (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons safeVars_FLAG sigV_safe)))))
      (by decide) (by decide) hag hm).1)
    (fun m m₁ hm hag => by
      obtain ⟨_, hI', hO', hX', _, _, harr⟩ := SPre.stable k g (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
        (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
        (SafeVars.cons safeVars_FLAG sigV_safe)))) (by decide) (by decide) (by decide) hag hm
      show decide (Instance.sigWith (arrAt m₁ (m₁ (OUT_ 0))) (g.base.nodes.getD (m₁ (X_ 1)) (.src 0)) =
        Instance.sigWith (arrAt m₁ (m₁ (OUT_ 0))) (g.base.nodes.getD (m₁ (I_ 0)) (.src 0))) =
        decide (Instance.sigWith (arrAt m (m (OUT_ 0))) (g.base.nodes.getD (m (X_ 1)) (.src 0)) =
        Instance.sigWith (arrAt m (m (OUT_ 0))) (g.base.nodes.getD (m (I_ 0)) (.src 0)))
      rw [hI', hO', hX', harr])
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hm0.1.ctx
  obtain ⟨m1, k1, e1, hk1, ag1, hr⟩ := hfi m0 hm0
  obtain ⟨hc1, hI1, hO1, harr1⟩ := CPre.stable k g (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
    (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
    (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons safeVars_FLAG sigV_safe)))))
    (by decide) (by decide) ag1 hm0
  -- the abstract predicate is `canonStep`'s
  have hp : (fun i => decide (Instance.sigWith (arrAt (m0.write (X_ 1) i) ((m0.write (X_ 1) i) (OUT_ 0)))
      (g.base.nodes.getD ((m0.write (X_ 1) i) (X_ 1)) (.src 0)) =
      Instance.sigWith (arrAt (m0.write (X_ 1) i) ((m0.write (X_ 1) i) (OUT_ 0)))
      (g.base.nodes.getD ((m0.write (X_ 1) i) (I_ 0)) (.src 0)))) =
      (fun i => decide (Instance.sigWith (arrAt m0 (m0 (OUT_ 0))) (g.base.nodes.getD i (.src 0)) =
        Instance.sigWith (arrAt m0 (m0 (OUT_ 0))) (g.base.nodes.getD (m0 (I_ 0)) (.src 0)))) := by
    funext i
    rw [Mem.write_same, Mem.write_ne _ _ (show OUT_ 0 ≠ X_ 1 by decide), Mem.write_ne _ _ (show I_ 0 ≠ X_ 1 by decide),
      arrAt_write_lo _ _ _ _ (by addr3) hm0.2.2.1]
  rw [hp] at hr
  have hval : g.base.canonStep (arrAt m0 (m0 (OUT_ 0))) (m0 (I_ 0)) =
      (if m1 (G_ 20) < m0 (I_ 0) then (arrAt m0 (m0 (OUT_ 0))).getD (m1 (G_ 20)) 0 else m0 (I_ 0)) := by
    rw [hr]; rfl
  have m1one : m1 ONE = 1 := by
    rw [ag1.var ONE (lt_hp hhp0 (by decide)) (by decide) (by decide), hone0]
  have m1zero : m1 ZERO = 0 := by
    rw [ag1.var ZERO (lt_hp hhp0 (by decide)) (by decide) (by decide), hzero0]
  by_cases hlt : m1 (G_ 20) < m0 (I_ 0)
  · have hc : (Cond.lt (G_ 20) (I_ 0)).eval m1 = true := by simp [Cond.eval, hI1, hlt]
    obtain ⟨m2, k2, e2, hk2, ag2, hv2, _⟩ := getDM_spec (OUT_ 0) (G_ 20) VAL (by constructor <;> addr3)
      (by decide) (by decide) (fun m => Ctx m ∧ IN ≤ m (OUT_ 0)) (fun _ h => h.1) (fun _ h => h.2) m1
      ⟨hc1.1.ctx, hc1.2.2.1⟩
    refine ⟨m2, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc e2), by unfold canonB; omega, ?_, ?_⟩
    · exact (ag1.trans ag2).mono (fun x hx => by unfold canonV; exact hx)
    · rw [hv2, hval, if_pos hlt, hO1, harr1]
  · have hc : (Cond.lt (G_ 20) (I_ 0)).eval m1 = false := by simp [Cond.eval, hI1, hlt]
    refine ⟨m1.write VAL (m1 (I_ 0)), _, Cmd.Exec.seq e1 (Cmd.Exec.ite_false hc (Exec.mov _ _ _)),
      by unfold canonB; omega, ?_, ?_⟩
    · exact (ag1.trans (Agree.write m1 VAL _ (by addr3))).mono (fun x hx => by unfold canonV; exact hx)
    · rw [Mem.write_same, hval, if_neg hlt, hI1]


/-- `IDS := canonIds` (a fresh array). -/
def canonIdsM : Cmd := .seq (buildM 0 NN canonStepM) (mov IDS (OUT_ 0))

def canonIdsV : List ℕ := Lvars 0 ++ canonV ++ [IDS]

theorem canonIdsV_safe : SafeVars canonIdsV :=
  SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) canonV_safe) (safeVars_of_decide _ (by decide))

/-- The instance context extended by the identifier table. -/
def IdsCtx (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  InstCtx k g m ∧ IN ≤ m IDS ∧ m IDS + 1 + m (m IDS) ≤ m HP ∧ arrAt m (m IDS) = g.base.canonIds

theorem IdsCtx.stable {k : ℕ} {g : GInstance} {V : List ℕ} (hV : SafeVars V) (hI : IDS ∉ V) {m m₁ : Mem}
    (hag : Agree m m₁ V) (h : IdsCtx k g m) : IdsCtx k g m₁ ∧ m₁ IDS = m IDS ∧ (∀ x, IN ≤ x → x < m HP → m₁ x = m x) := by
  obtain ⟨hm, h1, h2, h3⟩ := h
  have hhp : 200 ≤ m HP := hm.ctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2.1
  have hI' : m₁ IDS = m IDS := hag.var IDS (lt_hp hhp (by decide)) (by decide) hI
  refine ⟨⟨hm.of_agree hag hV, by rw [hI']; exact h1, ?_, ?_⟩, hI', fun x hx hx' => hag.heap hV' x hx hx'⟩
  · rw [hI', hag.heap hV' _ h1 (by omega)]; exact le_trans h2 hag.2
  · rw [hI', hag.arrAt hV' _ h1 h2]; exact h3

theorem IdsCtx.stableP {k : ℕ} {g : GInstance} {V : List ℕ} (hV : SafeVars V) (hI : IDS ∉ V) :
    StableP (IdsCtx k g) V := fun m m₁ hm hag => (IdsCtx.stable hV hI hag hm).1

theorem canonIdsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec canonIdsM canonIdsV (n * (canonB n + 8) + 8 + 1) (InstCtx k g) (fun m m' => IdsCtx k g m') := by
  have hb := buildM_spec (F := g.base.canonStep) 0 NN n
    (fun m j hm hi hj hO1 hO2 harr => by
      have hlen : m (m (OUT_ 0)) = j := by
        have := congrArg List.length harr; rw [arrAt_length, buildList_length] at this; exact this
      have hc : CPre k g m := ⟨hm, by rw [hi]; exact hj, hO1, by rw [hlen]; omega⟩
      obtain ⟨m', k', e, hk, ag, hv⟩ := canonStepM_spec k g n hn m hc
      exact ⟨m', k', e, hk, ag, by rw [hv, harr, hi]⟩)
    (by norm_num) (fun x hx => ⟨(canonV_safe x hx).1, (canonV_safe x hx).2.1⟩) (by constructor <;> addr3)
    (by decide) (by decide) (by decide) (fun m hm => hm.ctx) (fun m hm => by rw [hm.nn]; exact hn.nodes)
    (InstCtx.stableP (SafeVars.append (safeVars_Lvars 0 (by norm_num)) canonV_safe))
  intro m0 hm0
  obtain ⟨m1, k1, e1, hk1, ag1, hO1, harr1, hroom1⟩ := hb m0 hm0
  have hsafe : SafeVars (Lvars 0 ++ canonV) := SafeVars.append (safeVars_Lvars 0 (by norm_num)) canonV_safe
  have hm1 : InstCtx k g m1 := hm0.of_agree ag1 hsafe
  have hhp0 : 200 ≤ m0 HP := hm0.ctx.2.2
  refine ⟨m1.write IDS (m1 (OUT_ 0)), _, Cmd.Exec.seq e1 (Exec.mov _ _ _), by omega, ?_, ?_⟩
  · exact (ag1.trans (Agree.write m1 IDS _ (by addr3))).mono (fun x hx => by unfold canonIdsV; exact hx)
  · have hsI : SafeVars [IDS] := safeVars_of_decide _ (by decide)
    have hag2 : Agree m1 (m1.write IDS (m1 (OUT_ 0))) [IDS] := Agree.write m1 IDS _ (by addr3)
    refine ⟨hm1.of_agree hag2 hsI, ?_, ?_, ?_⟩
    · rw [Mem.write_same, hO1]; exact hhp0
    · rw [Mem.write_same, hO1, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]
      have := congrArg List.length harr1; rw [arrAt_length, buildList_length] at this
      rw [this]; exact hroom1
    · rw [Mem.write_same, hO1, arrAt_write_lo _ _ _ _ (by addr3) hhp0, harr1, hm0.nn]; rfl

/-! ### `testsDistinct` -/

/-- `ids.getD i 0 ≠ ids.getD j 0` for the test record at `X_ 0`. -/
def distinctTest : Cmd :=
  .seq (load (G_ 1) (X_ 0)) (.seq (field1M (X_ 0) (G_ 2)) (.seq (getDM IDS (G_ 1) (G_ 3))
    (.seq (getDM IDS (G_ 2) (G_ 4)) (notM (eqTest (G_ 3) (G_ 4))))))

/-- `tests.all distinctTest`. -/
def testsDistinctM : Cmd := allM 0 TESTS distinctTest

def dtV : List ℕ := [G_ 1] ++ ([G_ 2] ++ ([G_ 3] ++ ([G_ 4] ++ (FLAG :: [FLAG]))))

theorem dtV_safe : SafeVars dtV := safeVars_of_decide _ (by decide)

/-- The test-record precondition over the identifier context. -/
theorem testPreI_stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hX : X_ 0 ∉ V) (hI : IDS ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : IdsCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)) :
    (IdsCtx k g m₁ ∧ m₁ (X_ 0) ∈ arrAt m₁ (m₁ TESTS)) ∧ m₁ (X_ 0) = m (X_ 0) ∧
      m₁ (m (X_ 0)) = m (m (X_ 0)) ∧ m₁ (m (X_ 0) + 1) = m (m (X_ 0) + 1) ∧ m₁ IDS = m IDS ∧
      arrAt m₁ (m IDS) = arrAt m (m IDS) := by
  obtain ⟨hi, hx⟩ := h
  obtain ⟨hi', hI', hheap⟩ := IdsCtx.stable hV hI hag hi
  obtain ⟨hpre, hX', hc0, hc1⟩ := testPre_stable k g hV hX hag ⟨hi.1, hx⟩
  exact ⟨⟨hi', hpre.2⟩, hX', hc0, hc1, hI', hag.arrAt (fun x hx => (hV x hx).2.1) _ hi.2.1 hi.2.2.1⟩

theorem distinctTest_spec (k : ℕ) (g : GInstance) :
    TestSpec distinctTest dtV 20 (fun m => IdsCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS))
      (fun m => !(g.base.canonIds.getD (m (m (X_ 0))) 0 == g.base.canonIds.getD (m (m (X_ 0) + 1)) 0)) := by
  have hsG : ∀ i, i < 60 → SafeVars [G_ i] := fun i hi x hx => by simp at hx; subst hx; exact safeVars_G i hi
  have hsF : SafeVars [FLAG] := fun x hx => by simp at hx; subst hx; exact safeVars_FLAG
  have hq : ∀ m, IdsCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS) → IN ≤ m (X_ 0) ∧ m (X_ 0) + 2 ≤ m HP :=
    fun m hm => ⟨(hm.1.1.test_rec _ hm.2).1, (hm.1.1.test_rec _ hm.2).2.1⟩
  let Pre0 : Mem → Prop := fun m => IdsCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)
  let Pre1 : Mem → Prop := fun m => Pre0 m ∧ m (G_ 1) = m (m (X_ 0))
  let Pre2 : Mem → Prop := fun m => Pre1 m ∧ m (G_ 2) = m (m (X_ 0) + 1)
  let Pre3 : Mem → Prop := fun m => Pre2 m ∧ m (G_ 3) = g.base.canonIds.getD (m (G_ 1)) 0
  have e1 := loadM_spec (X_ 0) (G_ 1) (by constructor <;> addr3) Pre0
  have e2 := field1M_spec (X_ 0) (G_ 2) (by constructor <;> addr3) (by decide) Pre1 (fun m hm => hm.1.1.1.ctx)
    (fun m hm => (hq m hm.1).1)
  have e3 := getDM_spec IDS (G_ 1) (G_ 3) (by constructor <;> addr3) (by decide) (by decide) Pre2
    (fun m hm => hm.1.1.1.1.ctx) (fun m hm => hm.1.1.1.2.1)
  have e4 := getDM_spec IDS (G_ 2) (G_ 4) (by constructor <;> addr3) (by decide) (by decide) Pre3
    (fun m hm => hm.1.1.1.1.1.ctx) (fun m hm => hm.1.1.1.1.2.1)
  let Pre4 : Mem → Prop := fun m => Pre3 m ∧ m (G_ 4) = g.base.canonIds.getD (m (G_ 2)) 0
  have tn := notM_spec (eqTest_spec (G_ 3) (G_ 4) Pre4) (fun x hx => by simp at hx; subst hx; addr3)
    (fun m hm => hm.1.1.1.1.1.1.ctx)
  -- stability of the loaded values
  have hstab : ∀ {V : List ℕ}, SafeVars V → X_ 0 ∉ V → IDS ∉ V → G_ 1 ∉ V → G_ 2 ∉ V → ∀ m m₁, Agree m m₁ V →
      Pre2 m → Pre2 m₁ ∧ m₁ (G_ 1) = m (G_ 1) ∧ m₁ (G_ 2) = m (G_ 2) ∧ m₁ IDS = m IDS ∧
        arrAt m₁ (m IDS) = arrAt m (m IDS) := by
    intro V hV hX hI h1 h2 m m₁ hag hm
    have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
    obtain ⟨hp0, hX', hc0, hc1, hI', harr⟩ := testPreI_stable k g hV hX hI hag hm.1.1
    have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) h1
    have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) h2
    refine ⟨⟨⟨hp0, ?_⟩, ?_⟩, hG1, hG2, hI', harr⟩
    · rw [hG1, hX', hc0]; exact hm.1.2
    · rw [hG2, hX', hc1]; exact hm.2
  have t4 := TestSpec.after e4 tn (Q := fun m => !decide (m (G_ 3) = g.base.canonIds.getD (m (G_ 2)) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp2, hG1, hG2, hI', harr⟩ := hstab (hsG 4 (by norm_num)) (by decide) (by decide) (by decide) (by decide)
        m m₁ hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro (And.intro hp2 ?_) ?_
      · rw [hG3, hG1]; exact hm.2
      · rw [hp.1, hG2, hm.1.1.1.1.2.2.2])
    (fun m m₁ hm hag hp => by
      obtain ⟨hp2, hG1, hG2, hI', harr⟩ := hstab (hsG 4 (by norm_num)) (by decide) (by decide) (by decide) (by decide)
        m m₁ hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide)
      dsimp only
      rw [hp.1, hG3, hm.1.1.1.1.2.2.2])
  have t3 := TestSpec.after e3 t4
    (Q := fun m => !decide (g.base.canonIds.getD (m (G_ 1)) 0 = g.base.canonIds.getD (m (G_ 2)) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp2, hG1, hG2, hI', harr⟩ := hstab (hsG 3 (by norm_num)) (by decide) (by decide) (by decide) (by decide)
        m m₁ hag hm
      exact And.intro hp2 (by rw [hp.1, hG1, hm.1.1.1.2.2.2]))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp2, hG1, hG2, hI', harr⟩ := hstab (hsG 3 (by norm_num)) (by decide) (by decide) (by decide) (by decide)
        m m₁ hag hm
      dsimp only
      rw [hp.1, hG2, hm.1.1.1.2.2.2])
  have t2 := TestSpec.after e2 t3
    (Q := fun m => !decide (g.base.canonIds.getD (m (G_ 1)) 0 = g.base.canonIds.getD (m (m (X_ 0) + 1)) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hX', hc0, hc1, hI', harr⟩ := testPreI_stable k g (hsG 2 (by norm_num)) (by decide) (by decide)
        hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine And.intro (And.intro hp0 ?_) ?_
      · rw [hG1, hX', hc0]; exact hm.2
      · rw [hp.1, hX', hc1])
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hX', hc0, hc1, hI', harr⟩ := testPreI_stable k g (hsG 2 (by norm_num)) (by decide) (by decide)
        hag hm.1
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      dsimp only
      rw [hp.1, hG1])
  have t1 := TestSpec.after e1 t2
    (Q := fun m => !decide (g.base.canonIds.getD (m (m (X_ 0))) 0 = g.base.canonIds.getD (m (m (X_ 0) + 1)) 0))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hX', hc0, hc1, hI', harr⟩ := testPreI_stable k g (hsG 1 (by norm_num)) (by decide) (by decide)
        hag hm
      exact And.intro hp0 (by rw [hp.1, hX', hc0]))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hX', hc0, hc1, hI', harr⟩ := testPreI_stable k g (hsG 1 (by norm_num)) (by decide) (by decide)
        hag hm
      dsimp only
      rw [hp.1, hX', hc1])
  unfold distinctTest
  refine (t1.mono (V' := dtV) (fun x hx => hx) (by omega) (fun m hm => hm)).congr (fun m hm => ?_)
  dsimp only
  rw [Bool.beq_eq_decide_eq]

theorem testsDistinctM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec testsDistinctM (FLAG :: (Lvars 0 ++ FLAG :: (FLAG :: dtV))) (n * (20 + 12) + 11) (IdsCtx k g)
      (fun _ => g.base.testsDistinct g.base.canonIds) := by
  have hall := allM_spec 0 TESTS n (distinctTest_spec k g) (by norm_num)
    (fun x hx => ⟨(dtV_safe x hx).1, (dtV_safe x hx).2.1⟩) (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (fun m hm => hm.1.ctx)
    (fun m hm => ⟨hm.1.tests_wf.1, hm.1.tests_wf.2.1, by
      have := hm.1.arr_tests.2.2.1; rw [arrAt_length] at this; rw [this]; exact hn.tests⟩)
    (IdsCtx.stableP (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG dtV_safe))
      (by decide))
    (by
      intro m m' hm hx hag
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      have hV : SafeVars (LvarsX 0 ++ FLAG :: dtV) :=
        SafeVars.append (safeVars_LvarsX 0 (by norm_num)) (SafeVars.cons safeVars_FLAG dtV_safe)
      obtain ⟨_, hX', hc0, hc1, _, _⟩ := testPreI_stable k g hV (by decide) (by decide) hag ⟨hm, hx⟩
      dsimp only
      rw [hX', hc0, hc1])
  unfold testsDistinctM
  refine hall.congr (fun m hm => ?_)
  dsimp only
  unfold Instance.testsDistinct
  rw [← hm.1.pairs_tests]
  unfold pairsAt
  rw [List.all_map]
  apply all_congr_mem
  intro q hq
  simp only [Function.comp, Mem.write_same]
  obtain ⟨_, _, hrec⟩ := hm.1.tests_wf
  obtain ⟨hq1, hq2⟩ := hrec q hq
  rw [Mem.write_ne _ _ (show q ≠ X_ 0 by addr3), Mem.write_ne _ _ (show q + 1 ≠ X_ 0 by addr3)]


end DisequalityDispersion.Machine
