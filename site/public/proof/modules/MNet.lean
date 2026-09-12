import MCanon
import FlowCut

/-! # The split network on the machine

The lists `repsL`, `netNodesL`, `nodeArcsL`, `edgeArcsL`, `srcArcsL`, `snkArcsL` of `FlowCut`
are built as arrays (of values, or of pointers to two-cell records).  The only new combinator
is `mapArrM`: a map whose body allocates a fresh structure per element and returns its address. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Maps producing fresh structures -/

/-- A routine allocating a fresh structure (in the heap, above the old heap pointer) and returning
its address in `VAL`; `Post x m' q` describes the structure at `q` in terms of the element `x`. -/
def AllocSpec (c : Cmd) (V : List ℕ) (B : ℕ) (Pre : Mem → Prop) (X : ℕ) (Post : ℕ → Mem → ℕ → Prop) :
    Prop :=
  ∀ m, Pre m → ∃ m' k, Cmd.Exec c m m' k ∧ k ≤ B ∧ Agree m m' V ∧ m HP ≤ m' VAL ∧ m' VAL < m' HP ∧
    Post (m X) m' (m' VAL)

/-- `Post` only depends on the cells from `q` up to the heap pointer (and survives heap growth). -/
def PostStable (Post : ℕ → Mem → ℕ → Prop) : Prop :=
  ∀ x m₂ m₃ q, Post x m₂ q → (∀ y, q ≤ y → y < m₂ HP → m₃ y = m₂ y) → m₂ HP ≤ m₃ HP → Post x m₃ q

/-- The loop invariant of `mapM` with an allocating body. -/
structure MapArrInv (L : ℕ) (V : List ℕ) (Pre : Mem → Prop) (Post : ℕ → Mem → ℕ → Prop) (m0 : Mem)
    (l : List ℕ) (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ V)
  pre : Pre m
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = m0 HP
  hdr : m (m0 HP) = l.length
  cells : ∀ i, (h : i < l.length) → i < j →
    m0 HP + 1 + l.length ≤ m (m0 HP + 1 + i) ∧ m (m0 HP + 1 + i) < m HP ∧ Post l[i] m (m (m0 HP + 1 + i))
  room : m0 HP + 1 + l.length ≤ m HP

theorem mapArrM_spec {c : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {Post : ℕ → Mem → ℕ → Prop}
    (L SRC n : ℕ)
    (hc : AllocSpec c V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) (X_ L) Post) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L)
    (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ V)) (hPost : PostStable Post) :
    RSpec (mapM L SRC c) (Lvars L ++ V) (n * (B + 9) + 9) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧ m' (m HP) = m (m SRC) ∧
        (∀ i, (h : i < (arrAt m (m SRC)).length) →
          m HP + 1 + (arrAt m (m SRC)).length ≤ m' (m HP + 1 + i) ∧ m' (m HP + 1 + i) < m' HP ∧
          Post (arrAt m (m SRC))[i] m' (m' (m HP + 1 + i))) ∧
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
  have main := forEachM_spec L SRC hL hSRC.2 hSL
    (.seq c (.seq (add (PTR_ L) (OUT_ L) (I_ L)) (.seq (add (PTR_ L) (PTR_ L) ONE) (store (PTR_ L) VAL))))
    (MapArrInv L V Pre Post m0 l) (m0 SRC) hsrc0 l (B + 3) ?_ ?_ ?_ m5
    (by rw [q5 SRC (by addr') hSC (by addr') hSO]) (by
      rw [q5 (m0 SRC) (by addr') (by addr') (by omega) (by addr'), hlen]) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 e)))), ?_, inv'.agree, ?_⟩
    · have h1 : l.length * (B + 3 + 6) ≤ n * (B + 9) := Nat.mul_le_mul_right _ (by omega)
      omega
    · refine ⟨inv'.out, by rw [inv'.hdr, hlen], ?_, by rw [← hlen]; exact inv'.room⟩
      intro i hi
      subst hl
      exact inv'.cells i hi hi
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
    have hwHP : ((m.write (PTR_ L) v).write (X_ L) w) HP = m HP := by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · exact hsub x h),
      hPre m _ hpre (hag'.mono hsub), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout]
    · rw [hw _ (by omega), hhdr']
    · intro i hi1 hi2
      obtain ⟨c1, c2, c3⟩ := hcells i hi1 hi2
      rw [hw (m0 HP + 1 + i) (by omega), hwHP]
      exact ⟨c1, c2, hPost _ _ _ _ c3 (fun y hy _ => hw y (by omega)) (by rw [hwHP])⟩
    · rw [hwHP]; exact hroom
  · -- hbody
    intro j m hj hm hx hptr
    obtain ⟨hag, hpre, hi, hcnt, hout, hhdr', hcells, hroom⟩ := hm
    have hhp : m0 HP ≤ m HP := hag.2
    have hmem : m (X_ L) ∈ arrAt m (m SRC) := by
      rw [hx, hag.var SRC (by addr') (by addr') (by
        simp only [List.mem_append, not_or]; exact ⟨hSL, hSV⟩),
        hag.arrAt hVlt (m0 SRC) hsrc0 harr0, hl]
      exact List.getElem_mem hj
    obtain ⟨n1, k1, f1, hk1, agree1, hq1, hq2, hpost1⟩ := hc m ⟨hpre, hmem⟩
    rw [hx] at hpost1
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
    obtain ⟨q, hq⟩ : ∃ q, q = n1 VAL := ⟨_, rfl⟩
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
    obtain ⟨n4, hn4⟩ : ∃ n4, n4 = n3.write (hdr + 1 + j) q := ⟨_, rfl⟩
    have f4 : Cmd.Exec (store (PTR_ L) VAL) n3 n4 1 := by
      have := Exec.store (PTR_ L) VAL n3
      rw [hn3, Mem.write_same, Mem.write_ne _ _ (by addr'), ← hq] at this
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
    have hw : ∀ x, IN ≤ x → (n4.write (I_ L) (j + 1)) x = n4 x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr')]
    have hwHP : (n4.write (I_ L) (j + 1)) HP = n1 HP := by rw [Mem.write_ne _ _ (by addr'), n4HP]
    refine ⟨agree', hPre m0 _ hm0 agree', by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), q4 _ (by addr') (by addr'), n1C]
    · rw [Mem.write_ne _ _ (by addr'), q4 _ (by addr') (by addr'), n1O, hhdr]
    · rw [hw _ (by omega), ← hhdr, q4 _ (by addr') (by omega), hheap1 _ hhdrIN (by omega), hhdr, hhdr']
    · intro i hi1 hi2
      rw [hw (m0 HP + 1 + i) (by omega), hwHP, ← hhdr]
      by_cases hij : i = j
      · subst hij
        have n4slot : n4 (hdr + 1 + i) = q := by rw [hn4, Mem.write_same]
        rw [n4slot]
        rw [← hq] at hpost1
        refine ⟨by omega, by rw [hq]; exact hq2, ?_⟩
        refine hPost _ n1 _ q hpost1 (fun y hy hy' => ?_) (by rw [hwHP])
        rw [hw y (by omega), q4 y (by addr') (by omega)]
      · have hslot : n4 (hdr + 1 + i) = m (hdr + 1 + i) := by
          rw [q4 _ (by addr') (by omega), hheap1 _ (by omega) (by omega)]
        obtain ⟨c1, c2, c3⟩ := hcells i hi1 (by omega)
        rw [← hhdr] at c1 c2 c3
        rw [hslot]
        refine ⟨c1, by omega, ?_⟩
        refine hPost _ _ _ _ c3 (fun y hy hy' => ?_) (by rw [hwHP]; omega)
        rw [hw y (by omega), q4 y (by addr') (by omega), hheap1 y (by omega) hy']
    · rw [hwHP]; omega
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


/-! ### Arrays held in global variables -/

/-- The variable `P` points to an array in the heap holding `l`. -/
def ArrIs (m : Mem) (P : ℕ) (l : List ℕ) : Prop :=
  IN ≤ m P ∧ m P + 1 + m (m P) ≤ m HP ∧ arrAt m (m P) = l

/-- The variable `P` points to an array of pointers to two-cell records in the heap, holding `l`. -/
def PArrIs (m : Mem) (P : ℕ) (l : List (ℕ × ℕ)) : Prop := PairsWF m (m P) ∧ pairsAt m (m P) = l

theorem ArrIs.len {m : Mem} {P : ℕ} {l : List ℕ} (h : ArrIs m P l) : m (m P) = l.length := by
  rw [← h.2.2, arrAt_length]

theorem PArrIs.len {m : Mem} {P : ℕ} {l : List (ℕ × ℕ)} (h : PArrIs m P l) : m (m P) = l.length := by
  rw [← h.2, pairsAt, List.length_map, arrAt_length]

theorem ArrIs.stable {m m' : Mem} {V : List ℕ} {P : ℕ} {l : List ℕ} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (hP : P < IN) (hPH : P ≠ HP) (hPV : P ∉ V) (h : ArrIs m P l) :
    ArrIs m' P l := by
  obtain ⟨h1, h2, h3⟩ := h
  have hhp : IN ≤ m HP := by omega
  have hP' : m' P = m P := hag.var P (by omega) hPH hPV
  refine ⟨by rw [hP']; exact h1, ?_, by rw [hP', hag.arrAt hV _ h1 h2]; exact h3⟩
  rw [hP', hag.heap hV _ h1 (by omega)]; exact le_trans h2 hag.2

theorem PArrIs.stable {m m' : Mem} {V : List ℕ} {P : ℕ} {l : List (ℕ × ℕ)} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (hP : P < IN) (hPH : P ≠ HP) (hPV : P ∉ V) (h : PArrIs m P l) :
    PArrIs m' P l := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  have hhp : IN ≤ m HP := by omega
  have hP' : m' P = m P := hag.var P (by omega) hPH hPV
  refine ⟨⟨by rw [hP']; exact h1, ?_, ?_⟩, by rw [hP', hag.pairsAt hV _ h1 h2 h3]; exact h4⟩
  · rw [hP', hag.heap hV _ h1 (by omega)]; exact le_trans h2 hag.2
  · rw [hP']; exact (RecsIn.of_agree hag hV h1 h2 h3).mono le_rfl hag.2

/-- Composition of routines whose postconditions only constrain the final state. -/
theorem RSpec.seqP {c₁ c₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {P₁ P₂ P₃ : Mem → Prop}
    (h₁ : RSpec c₁ V₁ B₁ P₁ (fun _ m' => P₂ m')) (h₂ : RSpec c₂ V₂ B₂ P₂ (fun _ m' => P₃ m')) :
    RSpec (.seq c₁ c₂) (V₁ ++ V₂) (B₁ + B₂) P₁ (fun _ m' => P₃ m') := by
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp₁⟩ := h₁ m hm
  obtain ⟨m₂, k₂, e₂, hk₂, ag₂, hp₂⟩ := h₂ m₁ hp₁
  exact ⟨m₂, _, Cmd.Exec.seq e₁ e₂, by omega, ag₁.trans ag₂, hp₂⟩

theorem RSpec.mono' {c : Cmd} {V V' : List ℕ} {B B' : ℕ} {Pre Pre' : Mem → Prop} {Post Post' : Mem → Mem → Prop}
    (h : RSpec c V B Pre Post) (hV : ∀ x, x ∈ V → x ∈ V') (hB : B ≤ B') (hPre : ∀ m, Pre' m → Pre m)
    (hPost : ∀ m m', Pre' m → Agree m m' V → Post m m' → Post' m m') : RSpec c V' B' Pre' Post' := by
  intro m hm
  obtain ⟨m', k, e, hk, ag, hp⟩ := h m (hPre m hm)
  exact ⟨m', k, e, le_trans hk hB, ag.mono hV, hPost m m' hm ag hp⟩

/-- Store the fresh array's address into the global `P`. -/
theorem RSpec.seq_mov {c : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {R : Mem → Mem → Prop} (L P : ℕ)
    (hP : 5 ≤ P ∧ P < IN) (h : RSpec c V B Pre (fun m m' => m' (OUT_ L) = m HP ∧ R m m'))
    (hR : ∀ m m' v, Pre m → R m m' → R m (m'.write P v)) :
    RSpec (.seq c (mov P (OUT_ L))) (V ++ [P]) (B + 1) Pre (fun m m' => m' P = m HP ∧ R m m') := by
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hO, hr⟩ := h m hm
  refine ⟨m₁.write P (m₁ (OUT_ L)), _, Cmd.Exec.seq e₁ (Exec.mov _ _ _), by omega,
    ag₁.trans (Agree.write m₁ P _ (by addr3)), by rw [Mem.write_same, hO], hR m m₁ _ hm hr⟩

/-- Fresh arrays: the standard postcondition of the array producers gives `ArrIs`. -/
theorem ArrIs.of_out {m m' : Mem} {P : ℕ} {l : List ℕ} (hhp : IN ≤ m HP) (hP : m' P = m HP)
    (harr : arrAt m' (m HP) = l) (hroom : m HP + 1 + l.length ≤ m' HP) : ArrIs m' P l := by
  refine ⟨by rw [hP]; exact hhp, ?_, by rw [hP]; exact harr⟩
  rw [hP]
  have := congrArg List.length harr; rw [arrAt_length] at this; rw [this]; exact hroom

theorem PArrIs.of_out {m m' : Mem} {P : ℕ} {l : List (ℕ × ℕ)} (hhp : IN ≤ m HP) (hP : m' P = m HP)
    (harr : pairsAt m' (m HP) = l) (hrec : RecsIn m' (m HP) (m HP + 1 + l.length) (m' HP))
    (hroom : m HP + 1 + l.length ≤ m' HP) : PArrIs m' P l := by
  have hlen : m' (m HP) = l.length := by rw [← harr, pairsAt, List.length_map, arrAt_length]
  refine ⟨⟨by rw [hP]; exact hhp, by rw [hP, hlen]; exact hroom, ?_⟩, by rw [hP]; exact harr⟩
  rw [hP]; exact hrec.mono (by omega) le_rfl

/-! ### The global variables of the network -/

def NETS : ℕ := 115
def NETT : ℕ := 116
def NETN : ℕ := 117
def ARCS : ℕ := 118
def REPS : ℕ := 119
def RNGN : ℕ := 114   -- `RESV`, unused so far

theorem NETS_eq : NETS = 115 := rfl
theorem NETT_eq : NETT = 116 := rfl
theorem NETN_eq : NETN = 117 := rfl
theorem ARCS_eq : ARCS = 118 := rfl
theorem REPS_eq : REPS = 119 := rfl
theorem RNGN_eq : RNGN = 114 := rfl

/-- `addr3` extended with the network globals. -/
macro "addrn" : tactic => `(tactic| (first | omega | (simp only [A_, NEL, JJ, CC, I_, CNT_, PTR_,
  CONT_, X_, OUT_, RNG, G_, FLAG_eq, V2_eq, IN_eq', HP_eq', ONE_eq', POS_eq, OK_eq, VAL_eq, TMP_eq,
  N_eq, INB_eq, ZERO_eq, CNT_eq, POW_eq, PTR_eq, LAST_eq, BIT_eq, J_eq, CONT_eq, KV_eq, BASE_eq,
  SRCS_eq, SYMS_eq, NODES_eq, XV_eq, YV_eq, TV_eq, TESTS_eq, OUTS_eq, NN_eq, KK_eq, MM_eq, IDS_eq,
  RESV_eq, NETS_eq, NETT_eq, NETN_eq, ARCS_eq, REPS_eq, RNGN_eq] at * <;> omega)))

/-! ### The range array and the representatives -/

/-- `RNGN := range |nodes|`. -/
def rangeNM : Cmd := .seq (rangeM 0 NN) (mov RNGN (OUT_ 0))

theorem rangeNM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec rangeNM (Lvars 0 ++ [RNGN]) (n * 6 + 8 + 1) (IdsCtx k g)
      (fun _ m' => IdsCtx k g m' ∧ ArrIs m' RNGN (List.range g.base.nodes.length)) := by
  have h := RSpec.seq_mov 0 RNGN (by constructor <;> addrn)
    (rangeM_spec 0 NN n (by norm_num) (by constructor <;> addr3) (by decide) (IdsCtx k g)
      (fun m hm => hm.1.ctx) (fun m hm => by rw [hm.1.nn]; exact hn.nodes))
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ (by addrn) hm.1.ctx.2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addrn)]; exact hr.2⟩)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP, harr, hroom⟩ := hp
  rw [hm.1.nn] at harr hroom
  exact ⟨(IdsCtx.stable (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (by decide) hag hm).1, ArrIs.of_out hm.1.ctx.2.2 hP harr (by rw [List.length_range]; exact hroom)⟩


/-- `ids.getD j 0 = j` for `j = X_ 0`. -/
def repTest : Cmd := .seq (getDM IDS (X_ 0) (G_ 1)) (eqTest (G_ 1) (X_ 0))

theorem repTest_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → IdsCtx k g m)
    (hstab : StableP Pre [G_ 1]) :
    TestSpec repTest [G_ 1, FLAG] 9 Pre (fun m => decide (g.base.canonIds.getD (m (X_ 0)) 0 = m (X_ 0))) := by
  have e1 := getDM_spec IDS (X_ 0) (G_ 1) (by constructor <;> addr3) (by decide) (by decide) Pre
    (fun m hm => (hctx m hm).1.ctx) (fun m hm => (hctx m hm).2.1)
  have t := TestSpec.after e1 (eqTest_spec (G_ 1) (X_ 0) Pre)
    (Q := fun m => decide (g.base.canonIds.getD (m (X_ 0)) 0 = m (X_ 0)))
    (fun m m₁ hm hag _ => hstab m m₁ hm hag)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm).1.ctx.2.2
      dsimp only
      rw [hp.1, hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide), (hctx m hm).2.2.2])
  unfold repTest
  exact t.mono (fun x hx => hx) (by omega) (fun m hm => hm)

/-- `REPS := repsL ids`. -/
def repsM : Cmd := .seq (filterM 0 RNGN repTest) (mov REPS (OUT_ 0))

def repsV : List ℕ := (Lvars 0 ++ FLAG :: [G_ 1, FLAG]) ++ [REPS]

theorem repsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec repsM repsV (n * (9 + 14) + 9 + 1)
      (fun m => IdsCtx k g m ∧ ArrIs m RNGN (List.range g.base.nodes.length))
      (fun _ m' => (IdsCtx k g m' ∧ ArrIs m' RNGN (List.range g.base.nodes.length)) ∧
        ArrIs m' REPS (g.repsL g.base.canonIds)) := by
  have hsafe : SafeVars (Lvars 0 ++ FLAG :: [G_ 1, FLAG]) :=
    SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hsafe' : SafeVars repsV := SafeVars.append hsafe (safeVars_of_decide _ (by decide))
  have hV' : ∀ x, x ∈ Lvars 0 ++ FLAG :: [G_ 1, FLAG] → x < IN := fun x hx => (hsafe x hx).2.1
  have hf := filterM_spec 0 RNGN n (repTest_spec k g
      (fun m => (IdsCtx k g m ∧ ArrIs m RNGN (List.range g.base.nodes.length)) ∧ m (X_ 0) ∈ arrAt m (m RNGN))
      (fun m hm => hm.1.1) (fun m m₁ hm hag => by
        have hs1 : SafeVars [G_ 1] := safeVars_of_decide _ (by decide)
        have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
        refine ⟨⟨(IdsCtx.stable hs1 (by decide) hag hm.1.1).1,
          hm.1.2.stable hag (fun x hx => (hs1 x hx).2.1) (by addrn) (by addrn) (by decide)⟩, ?_⟩
        rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var RNGN (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.arrAt (fun x hx => (hs1 x hx).2.1) _ hm.1.2.1 hm.1.2.2.1]
        exact hm.2))
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> constructor <;> addr3)
    (by constructor <;> addrn) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun m hm => hm.1.1.ctx) (fun m hm => ⟨hm.2.1, hm.2.2.1, by rw [hm.2.len, List.length_range]; exact hn.nodes⟩)
    (fun m m₁ hm hag => ⟨(IdsCtx.stable hsafe (by decide) hag hm.1).1,
      hm.2.stable hag hV' (by addrn) (by addrn) (by decide)⟩)
    (fun m m₁ hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      show decide (g.base.canonIds.getD (m₁ (X_ 0)) 0 = m₁ (X_ 0)) =
        decide (g.base.canonIds.getD (m (X_ 0)) 0 = m (X_ 0))
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have h := RSpec.seq_mov 0 REPS (by constructor <;> addrn) hf
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ (by addrn) hm.1.1.ctx.2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addrn)]; exact hr.2⟩)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP, harr, hroom⟩ := hp
  have hV'' : ∀ x, x ∈ repsV → x < IN := fun x hx => (hsafe' x hx).2.1
  refine ⟨⟨(IdsCtx.stable hsafe' (by decide) hag hm.1).1, hm.2.stable hag hV'' (by addrn) (by addrn) (by decide)⟩,
    ArrIs.of_out hm.1.1.ctx.2.2 hP ?_ ?_⟩
  · rw [harr, hm.2.2.2]
    unfold GInstance.repsL
    apply List.filter_congr
    intro j _
    rw [Mem.write_same, Bool.beq_eq_decide_eq]
  · have h1 : (g.repsL g.base.canonIds).length ≤ g.base.nodes.length := by
      unfold GInstance.repsL; exact le_trans (List.length_filter_le _ _) (by rw [List.length_range])
    rw [hm.2.len, List.length_range] at hroom; omega


/-! ### Array producers storing their result in a global -/

theorem mapM_arr_spec {c : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {F : Mem → ℕ} (L SRC P n : ℕ)
    (l : List ℕ) (G : ℕ → ℕ)
    (hc : FunSpec c V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) F) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hP : 5 ≤ P ∧ P < IN)
    (hctx : ∀ m, Pre m → Ctx m) (harr : ∀ m, Pre m → ArrIs m SRC l) (hn : l.length ≤ n)
    (hPre : StableP Pre (Lvars L ++ V)) (hF : StableX Pre SRC L F (LvarsX L ++ V))
    (hG : ∀ m x, Pre m → x ∈ l → F (m.write (X_ L) x) = G x) :
    RSpec (.seq (mapM L SRC c) (mov P (OUT_ L))) (Lvars L ++ V ++ [P]) (n * (B + 9) + 9 + 1) Pre
      (fun _ m' => ArrIs m' P (l.map G)) := by
  have hm := mapM_spec L SRC n hc hL hV hSRC hSV hSL hVL hctx
    (fun m hm => ⟨(harr m hm).1, (harr m hm).2.1, by rw [(harr m hm).len]; exact hn⟩) hPre hF
  have h := RSpec.seq_mov L P hP hm
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ hP.2 (hctx m hm).2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP', harr', hroom⟩ := hp
  have hl := harr m hm
  rw [hl.2.2] at harr'
  refine ArrIs.of_out (hctx m hm).2.2 hP' ?_ (by rw [List.length_map, ← hl.len]; exact hroom)
  rw [harr']
  apply List.map_congr_left
  intro x hx
  exact hG m x hm hx

theorem filterM_arr_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool} (L SRC Q n : ℕ)
    (l : List ℕ) (G : ℕ → Bool)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) P) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hSF : SRC ≠ FLAG) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hXV : X_ L ∉ V)
    (hQ : 5 ≤ Q ∧ Q < IN)
    (hctx : ∀ m, Pre m → Ctx m) (harr : ∀ m, Pre m → ArrIs m SRC l) (hn : l.length ≤ n)
    (hPre : StableP Pre (Lvars L ++ FLAG :: V)) (hP : StableX Pre SRC L P (LvarsX L ++ FLAG :: V))
    (hG : ∀ m x, Pre m → x ∈ l → P (m.write (X_ L) x) = G x) :
    RSpec (.seq (filterM L SRC t) (mov Q (OUT_ L))) (Lvars L ++ FLAG :: V ++ [Q]) (n * (B + 14) + 9 + 1) Pre
      (fun _ m' => ArrIs m' Q (l.filter G)) := by
  have hf := filterM_spec L SRC n ht hL hV hSRC hSV hSL hSF hVL hXV hctx
    (fun m hm => ⟨(harr m hm).1, (harr m hm).2.1, by rw [(harr m hm).len]; exact hn⟩) hPre hP
  have h := RSpec.seq_mov L Q hQ hf
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ hQ.2 (hctx m hm).2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP', harr', hroom⟩ := hp
  have hl := harr m hm
  rw [hl.2.2] at harr'
  refine ArrIs.of_out (hctx m hm).2.2 hP' ?_ (by
    have := List.length_filter_le G l; rw [← hl.len] at this; omega)
  rw [harr']
  apply List.filter_congr
  intro x hx
  exact hG m x hm hx

theorem mapPairM_parr_spec {c : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {F : Mem → ℕ × ℕ}
    (L SRC P n : ℕ) (l : List ℕ) (G : ℕ → ℕ × ℕ)
    (hc : FunSpec2 c V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) F) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hP : 5 ≤ P ∧ P < IN)
    (hctx : ∀ m, Pre m → Ctx m) (harr : ∀ m, Pre m → ArrIs m SRC l) (hn : l.length ≤ n)
    (hPre : StableP Pre (Lvars L ++ V)) (hF : StableX Pre SRC L F (LvarsX L ++ V))
    (hG : ∀ m x, Pre m → x ∈ l → F (m.write (X_ L) x) = G x) :
    RSpec (.seq (mapPairM L SRC c) (mov P (OUT_ L))) (Lvars L ++ V ++ [P]) (n * (B + 14) + 9 + 1) Pre
      (fun _ m' => PArrIs m' P (l.map G)) := by
  have hm := mapPairM_spec L SRC n hc hL hV hSRC hSV hSL hVL hctx
    (fun m hm => ⟨(harr m hm).1, (harr m hm).2.1, by rw [(harr m hm).len]; exact hn⟩) hPre hF
  have h := RSpec.seq_mov L P hP hm
    (fun m m' v hm hr => by
      have hhp := (hctx m hm).2.2
      refine ⟨?_, ?_, by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2.2⟩
      · rw [← hr.1]
        apply pairsAt_congr (arrAt_write_lo _ _ _ _ hP.2 hhp)
        intro q hq
        obtain ⟨hq1, _⟩ := hr.2.1 q hq
        rw [Mem.write_ne _ _ (by omega), Mem.write_ne _ _ (by omega)]
        exact ⟨rfl, rfl⟩
      · intro q hq
        rw [arrAt_write_lo _ _ _ _ hP.2 hhp] at hq
        rw [Mem.write_ne _ _ (by addr3)]
        exact hr.2.1 q hq)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP', harr', hrec, hroom⟩ := hp
  have hl := harr m hm
  rw [hl.2.2] at harr'
  have hmap : (arrAt m (m SRC)).map (fun x => F (m.write (X_ L) x)) = l.map G := by
    rw [hl.2.2]; apply List.map_congr_left; intro x hx; exact hG m x hm hx
  rw [hl.2.2] at hmap
  refine PArrIs.of_out (hctx m hm).2.2 hP' (by rw [harr', hmap]) ?_ (by rw [List.length_map, ← hl.len]; exact hroom)
  rw [List.length_map, ← hl.len]; exact hrec

theorem appendM_arr_spec (L A B P n : ℕ) (la lb : List ℕ) (hL : L ≤ 9) (hA : 5 ≤ A ∧ A < IN)
    (hB : 5 ≤ B ∧ B < IN) (hAL : A ∉ Lvars L) (hBL : B ∉ Lvars L) (hP : 5 ≤ P ∧ P < IN)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (harrA : ∀ m, Pre m → ArrIs m A la) (harrB : ∀ m, Pre m → ArrIs m B lb) (hn : la.length ≤ n ∧ lb.length ≤ n) :
    RSpec (.seq (appendM L A B) (mov P (OUT_ L))) (Lvars L ++ [P]) (2 * n * 12 + 15 + 1) Pre
      (fun _ m' => ArrIs m' P (la ++ lb)) := by
  have ha := appendM_spec L A B n hL hA hB hAL hBL Pre hctx
    (fun m hm => ⟨(harrA m hm).1, (harrA m hm).2.1, by rw [(harrA m hm).len]; exact hn.1⟩)
    (fun m hm => ⟨(harrB m hm).1, (harrB m hm).2.1, by rw [(harrB m hm).len]; exact hn.2⟩)
  have h := RSpec.seq_mov L P hP ha
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ hP.2 (hctx m hm).2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP', harr', hroom⟩ := hp
  have hla := harrA m hm
  have hlb := harrB m hm
  rw [hla.2.2, hlb.2.2] at harr'
  refine ArrIs.of_out (hctx m hm).2.2 hP' harr' ?_
  rw [List.length_append, ← hla.len, ← hlb.len]; omega

theorem pairsAt_append {m : Mem} {a b : ℕ} {l : List ℕ} (h : arrAt m a = l) (h' : arrAt m b = l) :
    pairsAt m a = pairsAt m b := by unfold pairsAt; rw [h, h']

/-- Appending two arrays of record pointers appends the pairs. -/
theorem appendM_parr_spec (L A B P n : ℕ) (la lb : List (ℕ × ℕ)) (hL : L ≤ 9) (hA : 5 ≤ A ∧ A < IN)
    (hB : 5 ≤ B ∧ B < IN) (hAL : A ∉ Lvars L) (hBL : B ∉ Lvars L) (hP : 5 ≤ P ∧ P < IN)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (harrA : ∀ m, Pre m → PArrIs m A la) (harrB : ∀ m, Pre m → PArrIs m B lb) (hn : la.length ≤ n ∧ lb.length ≤ n) :
    RSpec (.seq (appendM L A B) (mov P (OUT_ L))) (Lvars L ++ [P]) (2 * n * 12 + 15 + 1) Pre
      (fun _ m' => PArrIs m' P (la ++ lb)) := by
  have ha := appendM_spec L A B n hL hA hB hAL hBL Pre hctx
    (fun m hm => ⟨(harrA m hm).1.1, (harrA m hm).1.2.1, by rw [(harrA m hm).len]; exact hn.1⟩)
    (fun m hm => ⟨(harrB m hm).1.1, (harrB m hm).1.2.1, by rw [(harrB m hm).len]; exact hn.2⟩)
  have h := RSpec.seq_mov L P hP ha
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ hP.2 (hctx m hm).2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  obtain ⟨hP', harr', hroom⟩ := hp
  have hla := harrA m hm
  have hlb := harrB m hm
  have hhp := (hctx m hm).2.2
  have hV' : ∀ x, x ∈ Lvars L ++ [P] → x < IN := fun x hx => by
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h | rfl
    · exact (Lvars_range L hL x h).2
    · exact hP.2
  -- the records survive
  have hrecA := hla.1.2.2
  have hrecB := hlb.1.2.2
  have hcells : ∀ q, q ∈ arrAt m (m A) ++ arrAt m (m B) → IN ≤ q ∧ q + 2 ≤ m HP ∧
      m' q = m q ∧ m' (q + 1) = m (q + 1) := by
    intro q hq
    rw [List.mem_append] at hq
    have hb : IN ≤ q ∧ q + 2 ≤ m HP := by
      rcases hq with h | h
      · exact hrecA q h
      · exact hrecB q h
    exact ⟨hb.1, hb.2, hag.heap hV' q hb.1 (by omega), hag.heap hV' (q + 1) (by omega) (by omega)⟩
  have hlen : m' (m HP) = la.length + lb.length := by
    have := congrArg List.length harr'
    simp only [arrAt_length, List.length_append] at this
    rw [this, hla.len, hlb.len]
  refine ⟨⟨by rw [hP']; exact hhp, by rw [hP', hlen]; rw [← hla.len, ← hlb.len]; omega, ?_⟩, ?_⟩
  · intro q hq
    rw [hP', harr'] at hq
    obtain ⟨h1, h2, _⟩ := hcells q hq
    exact ⟨h1, le_trans h2 hag.2⟩
  · rw [hP']
    unfold pairsAt
    rw [harr', List.map_append]
    rw [← hla.2, ← hlb.2]
    unfold pairsAt
    congr 1
    · apply List.map_congr_left; intro q hq
      obtain ⟨_, _, h3, h4⟩ := hcells q (List.mem_append_left _ hq); rw [h3, h4]
    · apply List.map_congr_left; intro q hq
      obtain ⟨_, _, h3, h4⟩ := hcells q (List.mem_append_right _ hq); rw [h3, h4]

theorem dedupM_parr_spec (L SRC P n : ℕ) (l : List (ℕ × ℕ)) (hL : L + 2 ≤ 9) (hSRC : 5 ≤ SRC ∧ SRC < IN)
    (hSd : SRC ∉ dedupV L) (hP : 5 ≤ P ∧ P < IN) (hPd : P ∉ dedupV L)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (harr : ∀ m, Pre m → PArrIs m SRC l) (hn : l.length ≤ n) :
    RSpec (.seq (dedupM L SRC) (mov P (OUT_ L))) (dedupV L ++ [P]) (23 * n * n + 23 * n + 8 + 1) Pre
      (fun _ m' => PArrIs m' P (dedupList l)) := by
  have hd := dedupM_spec L SRC n hL hSRC hSd Pre hctx
    (fun m hm => ⟨(harr m hm).1, by rw [(harr m hm).len]; exact hn⟩)
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp₁, hwf, _, _⟩ := hd m hm
  have hhp := (hctx m hm).2.2
  refine ⟨m₁.write P (m₁ (OUT_ L)), _, Cmd.Exec.seq e₁ (Exec.mov _ _ _), by omega,
    ag₁.trans (Agree.write m₁ P _ (by addr3)), ?_⟩
  have hhp1 : IN ≤ m₁ HP := le_trans hhp ag₁.2
  obtain ⟨w1, w2, w3⟩ := hwf
  refine ⟨⟨by rw [Mem.write_same]; exact w1, ?_, ?_⟩, ?_⟩
  · rw [Mem.write_same, Mem.write_ne _ _ (by omega), Mem.write_ne _ _ (by addr3)]; exact w2
  · rw [Mem.write_same, Mem.write_ne _ _ (by addr3)]
    intro q hq
    rw [arrAt_write_lo _ _ _ _ hP.2 w1] at hq
    exact w3 q hq
  · rw [Mem.write_same, ← (harr m hm).2, ← hp₁]
    apply pairsAt_congr (arrAt_write_lo _ _ _ _ hP.2 w1)
    intro q hq
    obtain ⟨hq1, _⟩ := w3 q hq
    rw [Mem.write_ne _ _ (by omega), Mem.write_ne _ _ (by omega)]
    exact ⟨rfl, rfl⟩


/-! ### Carrying facts through steps -/

theorem RSpec.carry {c : Cmd} {V : List ℕ} {B : ℕ} {Pre Q : Mem → Prop}
    (h : RSpec c V B Pre (fun _ m' => Q m')) (hstab : StableP Pre V) :
    RSpec c V B Pre (fun _ m' => Pre m' ∧ Q m') :=
  h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hq => ⟨hstab m m' hm hag, hq⟩)

theorem StableP.and {P Q : Mem → Prop} {V : List ℕ} (hP : StableP P V) (hQ : StableP Q V) :
    StableP (fun m => P m ∧ Q m) V := fun m m' hm hag => ⟨hP m m' hm.1 hag, hQ m m' hm.2 hag⟩

theorem ArrIs.stableP {V : List ℕ} {P : ℕ} {l : List ℕ} (hV : ∀ x, x ∈ V → x < IN) (hP : P < IN) (hPH : P ≠ HP)
    (hPV : P ∉ V) : StableP (fun m => ArrIs m P l) V := fun m m' hm hag => hm.stable hag hV hP hPH hPV

theorem PArrIs.stableP {V : List ℕ} {P : ℕ} {l : List (ℕ × ℕ)} (hV : ∀ x, x ∈ V → x < IN) (hP : P < IN)
    (hPH : P ≠ HP) (hPV : P ∉ V) : StableP (fun m => PArrIs m P l) V :=
  fun m m' hm hag => hm.stable hag hV hP hPH hPV

/-! ### The node list -/

/-- `VAL := 2 * X_ 0`. -/
def dblM : Cmd := add VAL (X_ 0) (X_ 0)

/-- `VAL := 2 * X_ 0 + 1`. -/
def dbl1M : Cmd := .seq (add VAL (X_ 0) (X_ 0)) (add VAL VAL ONE)

theorem dblM_spec (Pre : Mem → Prop) : FunSpec dblM [VAL] 1 Pre (fun m => m (X_ 0) + m (X_ 0)) :=
  fun m _ => ⟨m.write VAL (m (X_ 0) + m (X_ 0)), 1, Exec.add _ _ _ _, le_rfl, Agree.write m VAL _ (by addr3),
    Mem.write_same _ _ _⟩

theorem dbl1M_spec (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) :
    FunSpec dbl1M [VAL] 2 Pre (fun m => m (X_ 0) + m (X_ 0) + 1) := by
  intro m hm
  have hone := (hctx m hm).1
  have e2 : Cmd.Exec (add VAL VAL ONE) (m.write VAL (m (X_ 0) + m (X_ 0)))
      ((m.write VAL (m (X_ 0) + m (X_ 0))).write VAL (m (X_ 0) + m (X_ 0) + 1)) 1 := by
    have := Exec.add VAL VAL ONE (m.write VAL (m (X_ 0) + m (X_ 0)))
    rwa [Mem.write_same, Mem.write_ne _ _ (by addr3), hone] at this
  refine ⟨(m.write VAL (m (X_ 0) + m (X_ 0))).write VAL (m (X_ 0) + m (X_ 0) + 1), 1 + 1,
    Cmd.Exec.seq (Exec.add _ _ _ _) e2, le_rfl, ?_, Mem.write_same _ _ _⟩
  rw [Mem.write_write]; exact Agree.write m VAL _ (by addr3)

/-- The two-element array `[M[A], M[B]]` at `OUT_ 0`. -/
def arr2M (A B : ℕ) : Cmd :=
  .seq (mov (OUT_ 0) HP) (.seq (setc (CNT_ 0) 2) (.seq (store (OUT_ 0) (CNT_ 0)) (.seq (add HP HP ONE)
    (.seq (store HP A) (.seq (add HP HP ONE) (.seq (store HP B) (add HP HP ONE)))))))

theorem arr2M_spec (A B : ℕ) (hA : 5 ≤ A ∧ A < IN) (hB : 5 ≤ B ∧ B < IN) (hAL : A ∉ Lvars 0) (hBL : B ∉ Lvars 0)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) :
    RSpec (arr2M A B) (Lvars 0) 8 Pre
      (fun m m' => m' (OUT_ 0) = m HP ∧ arrAt m' (m HP) = [m A, m B] ∧ m HP + 1 + 2 ≤ m' HP) := by
  intro m0 hm0
  obtain ⟨hone, _, hhp⟩ := hctx m0 hm0
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  have hAO : A ≠ OUT_ 0 := fun h => hAL (by rw [h]; simp [Lvars])
  have hAC : A ≠ CNT_ 0 := fun h => hAL (by rw [h]; simp [Lvars])
  have hBO : B ≠ OUT_ 0 := fun h => hBL (by rw [h]; simp [Lvars])
  have hBC : B ≠ CNT_ 0 := fun h => hBL (by rw [h]; simp [Lvars])
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ 0) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ 0) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ 0) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (CNT_ 0) 2 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (setc (CNT_ 0) 2) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write hdr 2 := ⟨_, rfl⟩
  have e3 : Cmd.Exec (store (OUT_ 0) (CNT_ 0)) m2 m3 1 := by
    have := Exec.store (OUT_ 0) (CNT_ 0) m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr3), hm1, Mem.write_same] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + 1) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP ONE) m3 m4 1 := by
    have := Exec.add HP HP ONE m3
    rw [hm3, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by addr3),
      Mem.write_ne _ _ (by addr3), hm1, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hone,
      ← hhdr] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (hdr + 1) (m0 A) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (store HP A) m4 m5 1 := by
    have := Exec.store HP A m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr3), hm3, Mem.write_ne _ _ (by addr3), hm2,
      Mem.write_ne _ _ hAC, hm1, Mem.write_ne _ _ hAO] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write HP (hdr + 2) := ⟨_, rfl⟩
  have e6 : Cmd.Exec (add HP HP ONE) m5 m6 1 := by
    have := Exec.add HP HP ONE m5
    rw [hm5, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm4, Mem.write_same,
      Mem.write_ne _ _ (by addr3), hm3, Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by addr3), hm1,
      Mem.write_ne _ _ (by addr3), hone] at this
    rw [hm6, hm5, hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m7, hm7⟩ : ∃ m7, m7 = m6.write (hdr + 2) (m0 B) := ⟨_, rfl⟩
  have e7 : Cmd.Exec (store HP B) m6 m7 1 := by
    have := Exec.store HP B m6
    rw [hm6, Mem.write_same, Mem.write_ne _ _ (by addr3), hm5, Mem.write_ne _ _ (by addr3), hm4,
      Mem.write_ne _ _ (by addr3), hm3, Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ hBC, hm1,
      Mem.write_ne _ _ hBO] at this
    rw [hm7, hm6, hm5, hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m8, hm8⟩ : ∃ m8, m8 = m7.write HP (hdr + 3) := ⟨_, rfl⟩
  have e8 : Cmd.Exec (add HP HP ONE) m7 m8 1 := by
    have := Exec.add HP HP ONE m7
    rw [hm7, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm6, Mem.write_same,
      Mem.write_ne _ _ (by addr3), hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_ne _ _ (by addr3), hm3,
      Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by addr3), hm1, Mem.write_ne _ _ (by addr3), hone] at this
    rw [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]; exact this
  have q8 : ∀ x, x ≠ HP → x ≠ hdr → x ≠ hdr + 1 → x ≠ hdr + 2 → x ≠ CNT_ 0 → x ≠ OUT_ 0 → m8 x = m0 x :=
    fun x h1 h2 h3 h4 h5 h6 => by
      rw [hm8, Mem.write_ne _ _ h1, hm7, Mem.write_ne _ _ h4, hm6, Mem.write_ne _ _ h1, hm5,
        Mem.write_ne _ _ h3, hm4, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h2, hm2, Mem.write_ne _ _ h5,
        hm1, Mem.write_ne _ _ h6]
  have m8HP : m8 HP = hdr + 3 := by rw [hm8, Mem.write_same]
  have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp
  have m8O : m8 (OUT_ 0) = hdr := by
    rw [hm8, Mem.write_ne _ _ (by addr3), hm7, Mem.write_ne _ _ (by addr3), hm6, Mem.write_ne _ _ (by addr3),
      hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_ne _ _ (by addr3), hm3, Mem.write_ne _ _ (by addr3),
      hm2, Mem.write_ne _ _ (by addr3), hm1, Mem.write_same]
  have m8hdr : m8 hdr = 2 := by
    rw [hm8, Mem.write_ne _ _ (by addr3), hm7, Mem.write_ne _ _ (by omega), hm6, Mem.write_ne _ _ (by addr3),
      hm5, Mem.write_ne _ _ (by omega), hm4, Mem.write_ne _ _ (by addr3), hm3, Mem.write_same]
  have m8h1 : m8 (hdr + 1) = m0 A := by
    rw [hm8, Mem.write_ne _ _ (by addr3), hm7, Mem.write_ne _ _ (by omega), hm6, Mem.write_ne _ _ (by addr3),
      hm5, Mem.write_same]
  have m8h2 : m8 (hdr + 2) = m0 B := by rw [hm8, Mem.write_ne _ _ (by addr3), hm7, Mem.write_same]
  refine ⟨m8, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5
    (Cmd.Exec.seq e6 (Cmd.Exec.seq e7 e8)))))), by omega, ?_, by rw [m8O, hhdr], ?_, by rw [m8HP, hhdr]⟩
  · refine ⟨fun x hx hxV => ?_, by rw [m8HP]; omega⟩
    simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hxV
    exact q8 x hxV.1 (by omega) (by omega) (by omega) hxV.2.2.1 hxV.2.2.2.2.2.2
  · rw [← hhdr]
    show (List.range (m8 hdr)).map (fun i => m8 (hdr + 1 + i)) = _
    rw [m8hdr, show List.range 2 = [0, 1] from rfl]
    simp only [List.map_cons, List.map_nil, Nat.add_zero, m8h1, show hdr + 1 + 1 = hdr + 2 by omega, m8h2]



/-- The context after the representatives are computed. -/
def NC0 (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  IdsCtx k g m ∧ ArrIs m RNGN (List.range g.base.nodes.length) ∧ ArrIs m REPS (g.repsL g.base.canonIds)

theorem NC0.stableP {k : ℕ} {g : GInstance} {V : List ℕ} (hV : SafeVars V) (hI : IDS ∉ V) (hR : RNGN ∉ V)
    (hP : REPS ∉ V) : StableP (NC0 k g) V :=
  (IdsCtx.stableP hV hI).and ((ArrIs.stableP (fun x hx => (hV x hx).2.1) (by addrn) (by addrn) hR).and
    (ArrIs.stableP (fun x hx => (hV x hx).2.1) (by addrn) (by addrn) hP))

theorem NC0.ctx {k : ℕ} {g : GInstance} {m : Mem} (h : NC0 k g m) : Ctx m := h.1.1.ctx

/-- `NETS := 2 |nodes|`, `NETT := NETS + 1`. -/
def stM : Cmd := .seq (add NETS NN NN) (add NETT NETS ONE)

theorem stM_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → InstCtx k g m) :
    RSpec stM [NETS, NETT] 2 Pre (fun _ m' => m' NETS = g.netS ∧ m' NETT = g.netT) := by
  intro m hm
  have hone := (hctx m hm).ctx.1
  have hnn := (hctx m hm).nn
  have e2 : Cmd.Exec (add NETT NETS ONE) (m.write NETS (m NN + m NN))
      ((m.write NETS (m NN + m NN)).write NETT (m NN + m NN + 1)) 1 := by
    have := Exec.add NETT NETS ONE (m.write NETS (m NN + m NN))
    rwa [Mem.write_same, Mem.write_ne _ _ (by addrn), hone] at this
  refine ⟨_, 1 + 1, Cmd.Exec.seq (Exec.add _ _ _ _) e2, le_rfl,
    (Agree.write m NETS _ (by addrn)).trans (Agree.write _ NETT _ (by addrn)), ?_, ?_⟩
  · rw [Mem.write_ne _ _ (by addrn), Mem.write_same, hnn]; unfold GInstance.netS; omega
  · rw [Mem.write_same, hnn]; unfold GInstance.netT; omega

/-- `NETN := netNodesL ids`. -/
def netNodesM : Cmd :=
  .seq (.seq (mapM 0 REPS dblM) (mov (G_ 40) (OUT_ 0)))
  (.seq (.seq (mapM 0 REPS dbl1M) (mov (G_ 41) (OUT_ 0)))
  (.seq (.seq (appendM 0 (G_ 40) (G_ 41)) (mov (G_ 42) (OUT_ 0)))
  (.seq stM
  (.seq (.seq (arr2M NETS NETT) (mov (G_ 43) (OUT_ 0)))
        (.seq (appendM 0 (G_ 42) (G_ 43)) (mov NETN (OUT_ 0)))))))

def netNodesV : List ℕ :=
  (Lvars 0 ++ [VAL] ++ [G_ 40]) ++ ((Lvars 0 ++ [VAL] ++ [G_ 41]) ++ ((Lvars 0 ++ [G_ 42]) ++
    ([NETS, NETT] ++ ((Lvars 0 ++ [G_ 43]) ++ (Lvars 0 ++ [NETN])))))

theorem netNodesV_safe : SafeVars netNodesV :=
  SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (safeVars_of_decide _ (by decide)))
  (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (safeVars_of_decide _ (by decide)))
  (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
  (SafeVars.append (safeVars_of_decide _ (by decide))
  (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))))))

theorem repsL_length_le (g : GInstance) (ids : List ℕ) : (g.repsL ids).length ≤ g.base.nodes.length := by
  unfold GInstance.repsL; exact le_trans (List.length_filter_le _ _) (by rw [List.length_range])

/-- The context after the node list is computed. -/
def NC1 (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  NC0 k g m ∧ m NETS = g.netS ∧ m NETT = g.netT ∧ ArrIs m NETN (g.netNodesL g.base.canonIds)

theorem NC1.stableP {k : ℕ} {g : GInstance} {V : List ℕ} (hV : SafeVars V) (hI : IDS ∉ V) (hR : RNGN ∉ V)
    (hP : REPS ∉ V) (hS : NETS ∉ V) (hT : NETT ∉ V) (hN : NETN ∉ V) : StableP (NC1 k g) V := by
  intro m m' hm hag
  have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
  refine ⟨NC0.stableP hV hI hR hP m m' hm.1 hag, ?_, ?_,
    hm.2.2.2.stable hag (fun x hx => (hV x hx).2.1) (by addrn) (by addrn) hN⟩
  · rw [hag.var NETS (lt_hp hhp (by decide)) (by decide) hS]; exact hm.2.1
  · rw [hag.var NETT (lt_hp hhp (by decide)) (by decide) hT]; exact hm.2.2.1

theorem netNodesM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec netNodesM netNodesV
      ((n * (1 + 9) + 9 + 1) + ((n * (2 + 9) + 9 + 1) + ((2 * n * 12 + 15 + 1) + (2 + ((8 + 1) + (2 * (2 * n + 2) * 12 + 15 + 1))))))
      (NC0 k g) (fun _ m' => NC1 k g m') := by
  have hrep : (g.repsL g.base.canonIds).length ≤ n := le_trans (repsL_length_le g _) hn.nodes
  have hsL : SafeVars (Lvars 0 ++ [VAL]) := SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hV1 : ∀ x, x ∈ [VAL] → 5 ≤ x ∧ x < IN := fun x hx => by simp at hx; subst hx; constructor <;> addr3
  -- C1
  have s1 := (mapM_arr_spec 0 REPS (G_ 40) n (g.repsL g.base.canonIds) (fun r => 2 * r)
    (dblM_spec (fun m => NC0 k g m ∧ m (X_ 0) ∈ arrAt m (m REPS))) (by norm_num) hV1 (by constructor <;> addrn)
    (by decide) (by decide) (by decide) (by constructor <;> addr3) (fun m hm => hm.ctx) (fun m hm => hm.2.2) hrep
    (NC0.stableP hsL (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.ctx.2.2
      show m' (X_ 0) + m' (X_ 0) = m (X_ 0) + m (X_ 0)
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x _ _ => by simp only [Mem.write_same]; omega)).carry
    (NC0.stableP (SafeVars.append hsL (safeVars_of_decide _ (by decide))) (by decide) (by decide) (by decide))
  -- C2
  have s2 := (mapM_arr_spec 0 REPS (G_ 41) n (g.repsL g.base.canonIds) (fun r => 2 * r + 1)
    (dbl1M_spec (fun m => (NC0 k g m ∧ ArrIs m (G_ 40) ((g.repsL g.base.canonIds).map (fun r => 2 * r))) ∧
      m (X_ 0) ∈ arrAt m (m REPS)) (fun m hm => hm.1.1.ctx)) (by norm_num) hV1 (by constructor <;> addrn)
    (by decide) (by decide) (by decide) (by constructor <;> addr3) (fun m hm => hm.1.ctx) (fun m hm => hm.1.2.2) hrep
    ((NC0.stableP hsL (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 40) (fun x hx => (hsL x hx).2.1) (by addr3) (by addr3) (by decide)))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show m' (X_ 0) + m' (X_ 0) + 1 = m (X_ 0) + m (X_ 0) + 1
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x _ _ => by simp only [Mem.write_same]; omega)).carry
    ((NC0.stableP (SafeVars.append hsL (safeVars_of_decide _ (by decide))) (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 40) (fun x hx => ((SafeVars.append hsL (safeVars_of_decide _ (by decide))) x hx).2.1)
        (by addr3) (by addr3) (by decide)))
  -- C3
  have hs0 : SafeVars (Lvars 0) := safeVars_Lvars 0 (by norm_num)
  have hs42 : SafeVars (Lvars 0 ++ [G_ 42]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have s3 := (appendM_arr_spec 0 (G_ 40) (G_ 41) (G_ 42) n _ _ (by norm_num) (by constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addr3)
    (fun m => (NC0 k g m ∧ ArrIs m (G_ 40) ((g.repsL g.base.canonIds).map (fun r => 2 * r))) ∧
      ArrIs m (G_ 41) ((g.repsL g.base.canonIds).map (fun r => 2 * r + 1)))
    (fun m hm => hm.1.1.ctx) (fun m hm => hm.1.2) (fun m hm => hm.2)
    ⟨by rw [List.length_map]; exact hrep, by rw [List.length_map]; exact hrep⟩).carry
    (((NC0.stableP hs42 (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 40) (fun x hx => (hs42 x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 41) (fun x hx => (hs42 x hx).2.1) (by addr3) (by addr3) (by decide)))
  -- C4
  let P3 : Mem → Prop := fun m => ((NC0 k g m ∧ ArrIs m (G_ 40) ((g.repsL g.base.canonIds).map (fun r => 2 * r))) ∧
    ArrIs m (G_ 41) ((g.repsL g.base.canonIds).map (fun r => 2 * r + 1))) ∧
    ArrIs m (G_ 42) ((g.repsL g.base.canonIds).map (fun r => 2 * r) ++ (g.repsL g.base.canonIds).map (fun r => 2 * r + 1))
  have hsST : SafeVars [NETS, NETT] := safeVars_of_decide _ (by decide)
  have s4 := (stM_spec k g P3 (fun m hm => hm.1.1.1.1.1)).carry
    ((((NC0.stableP hsST (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 40) (fun x hx => (hsST x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 41) (fun x hx => (hsST x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 42) (fun x hx => (hsST x hx).2.1) (by addr3) (by addr3) (by decide)))
  -- C5
  let P4 : Mem → Prop := fun m => P3 m ∧ m NETS = g.netS ∧ m NETT = g.netT
  have hs43 : SafeVars (Lvars 0 ++ [G_ 43]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have hP4 : StableP P4 (Lvars 0 ++ [G_ 43]) := by
    intro m m' hm hag
    have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
    refine ⟨(((NC0.stableP hs43 (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 40) (fun x hx => (hs43 x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 41) (fun x hx => (hs43 x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 42) (fun x hx => (hs43 x hx).2.1) (by addr3) (by addr3) (by decide)) m m' hm.1 hag, ?_, ?_⟩
    · rw [hag.var NETS (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2.1
    · rw [hag.var NETT (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2.2
  have ha2 := RSpec.seq_mov 0 (G_ 43) (by constructor <;> addr3)
    (arr2M_spec NETS NETT (by constructor <;> addrn) (by constructor <;> addrn) (by decide) (by decide) P4
      (fun m hm => hm.1.1.1.1.ctx))
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ (by addr3) hm.1.1.1.1.ctx.2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)
  have s5 := (ha2.mono' (Post' := fun _ m' => ArrIs m' (G_ 43) [g.netS, g.netT]) (fun x hx => hx) le_rfl
    (fun m hm => hm) (fun m m' hm hag hp => by
      obtain ⟨hP', harr, hroom⟩ := hp
      exact ArrIs.of_out hm.1.1.1.1.ctx.2.2 hP' (by rw [harr, hm.2.1, hm.2.2]) hroom)).carry hP4
  -- C6
  let P5 : Mem → Prop := fun m => P4 m ∧ ArrIs m (G_ 43) [g.netS, g.netT]
  have hsN : SafeVars (Lvars 0 ++ [NETN]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have s6 := appendM_arr_spec 0 (G_ 42) (G_ 43) NETN (2 * n + 2) _ _ (by norm_num) (by constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addrn) P5
    (fun m hm => hm.1.1.1.1.1.ctx) (fun m hm => hm.1.1.2) (fun m hm => hm.2)
    ⟨by rw [List.length_append, List.length_map, List.length_map]; omega, by simp⟩
  have hP5 : StableP P5 (Lvars 0 ++ [NETN]) := by
    intro m m' hm hag
    have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
    refine ⟨⟨(((NC0.stableP hsN (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 40) (fun x hx => (hsN x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 41) (fun x hx => (hsN x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (ArrIs.stableP (P := G_ 42) (fun x hx => (hsN x hx).2.1) (by addr3) (by addr3) (by decide)) m m' hm.1.1 hag,
      ?_, ?_⟩, hm.2.stable hag (fun x hx => (hsN x hx).2.1) (by addr3) (by addr3) (by decide)⟩
    · rw [hag.var NETS (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.1.2.1
    · rw [hag.var NETT (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.1.2.2
  -- assembly
  have hall := (s1.seqP (s2.seqP (s3.seqP (s4.seqP (s5.seqP (s6.carry hP5))))))
  unfold netNodesM netNodesV
  refine hall.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  exact ⟨hp.1.1.1.1.1.1, hp.1.1.2.1, hp.1.1.2.2, hp.2⟩


/-! ### Node arcs -/

/-- `(VAL, V2) := (2 X_ 0, 2 X_ 0 + 1)`. -/
def pairDblM : Cmd := .seq (add VAL (X_ 0) (X_ 0)) (add V2 VAL ONE)

theorem pairDblM_spec (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) :
    FunSpec2 pairDblM [VAL, V2] 2 Pre (fun m => (m (X_ 0) + m (X_ 0), m (X_ 0) + m (X_ 0) + 1)) := by
  intro m hm
  have hone := (hctx m hm).1
  have e2 : Cmd.Exec (add V2 VAL ONE) (m.write VAL (m (X_ 0) + m (X_ 0)))
      ((m.write VAL (m (X_ 0) + m (X_ 0))).write V2 (m (X_ 0) + m (X_ 0) + 1)) 1 := by
    have := Exec.add V2 VAL ONE (m.write VAL (m (X_ 0) + m (X_ 0)))
    rwa [Mem.write_same, Mem.write_ne _ _ (by addr3), hone] at this
  refine ⟨_, 1 + 1, Cmd.Exec.seq (Exec.add _ _ _ _) e2, le_rfl,
    (Agree.write m VAL _ (by addr3)).trans (Agree.write _ V2 _ (by addr3)), ?_⟩
  show ((_ : Mem) VAL, (_ : Mem) V2) = _
  rw [Mem.write_same, Mem.write_ne _ _ (by addr3), Mem.write_same]

/-- `G_ 44 := nodeArcsL ids`. -/
def nodeArcsM : Cmd := .seq (mapPairM 0 REPS pairDblM) (mov (G_ 44) (OUT_ 0))

def nodeArcsV : List ℕ := Lvars 0 ++ [VAL, V2] ++ [G_ 44]

theorem nodeArcsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec nodeArcsM nodeArcsV (n * (2 + 14) + 9 + 1) (NC1 k g)
      (fun _ m' => NC1 k g m' ∧ PArrIs m' (G_ 44) (g.nodeArcsL g.base.canonIds)) := by
  have hrep : (g.repsL g.base.canonIds).length ≤ n := le_trans (repsL_length_le g _) hn.nodes
  have hsL : SafeVars (Lvars 0 ++ [VAL, V2]) :=
    SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hsV : SafeVars nodeArcsV := SafeVars.append hsL (safeVars_of_decide _ (by decide))
  exact (mapPairM_parr_spec 0 REPS (G_ 44) n (g.repsL g.base.canonIds) (fun r => (2 * r, 2 * r + 1))
    (pairDblM_spec (fun m => NC1 k g m ∧ m (X_ 0) ∈ arrAt m (m REPS)) (fun m hm => hm.1.1.ctx))
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> constructor <;> addr3)
    (by constructor <;> addrn) (by decide) (by decide) (by decide) (by constructor <;> addr3)
    (fun m hm => hm.1.ctx) (fun m hm => hm.1.2.2) hrep
    (NC1.stableP hsL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show (m' (X_ 0) + m' (X_ 0), m' (X_ 0) + m' (X_ 0) + 1) = (m (X_ 0) + m (X_ 0), m (X_ 0) + m (X_ 0) + 1)
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x _ _ => by simp only [Mem.write_same, Prod.mk.injEq]; omega)).carry
    (NC1.stableP hsV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

/-! ### Edge arcs -/

/-- A fresh empty array; its address in `D`. -/
def emptyArrM (D : ℕ) : Cmd := .seq (mov D HP) (.seq (store D ZERO) (add HP HP ONE))

theorem emptyArrM_spec (D : ℕ) (hD : 5 ≤ D ∧ D < IN) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) :
    RSpec (emptyArrM D) [D] 3 Pre (fun m m' => m' D = m HP ∧ m' (m HP) = 0 ∧ m' HP = m HP + 1) := by
  intro m hm
  obtain ⟨hone, hzero, hhp⟩ := hctx m hm
  have hDH : D ≠ HP := by addr3
  have e2 : Cmd.Exec (store D ZERO) (m.write D (m HP)) ((m.write D (m HP)).write (m HP) 0) 1 := by
    have := Exec.store D ZERO (m.write D (m HP))
    rwa [Mem.write_same, Mem.write_ne _ _ (by addr3), hzero] at this
  have e3 : Cmd.Exec (add HP HP ONE) ((m.write D (m HP)).write (m HP) 0)
      (((m.write D (m HP)).write (m HP) 0).write HP (m HP + 1)) 1 := by
    have := Exec.add HP HP ONE ((m.write D (m HP)).write (m HP) 0)
    rwa [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (Ne.symm hDH), Mem.write_ne _ _ (by addr3),
      Mem.write_ne _ _ (by addr3), hone] at this
  refine ⟨_, 1 + (1 + 1), Cmd.Exec.seq (Exec.mov _ _ _) (Cmd.Exec.seq e2 e3), le_rfl, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x hx hxV => ?_, by rw [Mem.write_same]; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
    rw [Mem.write_ne _ _ hxV.1, Mem.write_ne _ _ (by omega), Mem.write_ne _ _ hxV.2]
  · rw [Mem.write_ne _ _ hDH, Mem.write_ne _ _ (by addr3), Mem.write_same]
  · rw [Mem.write_ne _ _ (by addr3), Mem.write_same]
  · rw [Mem.write_same]

/-- `G_ 31 := ` the argument array of node `X_ 0` (a fresh empty array for a source). -/
def argsPtrM : Cmd :=
  .seq (elemM NODES (X_ 0) (G_ 30)) (.seq (load (G_ 32) (G_ 30))
    (.ite (.eq (G_ 32) ZERO) (emptyArrM (G_ 31)) (field2M (G_ 30) (G_ 31))))

theorem argsPtrM_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → InstCtx k g m)
    (hj : ∀ m, Pre m → m (X_ 0) < g.base.nodes.length) :
    RSpec argsPtrM [G_ 30, G_ 32, G_ 31] 9 Pre
      (fun m m' => ArrIs m' (G_ 31) (g.argsOf (m (X_ 0))) ∧ m' (X_ 0) = m (X_ 0)) := by
  intro m hm
  have hi := hctx m hm
  have hhp : 200 ≤ m HP := hi.ctx.2.2
  have hj' := hj m hm
  obtain ⟨a1, a2, a3, a4⟩ := hi.node_rec _ hj'
  obtain ⟨m1, k1, e1, hk1, ag1, hv1, hHP1⟩ := elemM_spec NODES (X_ 0) (G_ 30) (by constructor <;> addr3)
    (by decide) (by decide) Pre (fun m hm => (hctx m hm).ctx) (fun m hm => (hctx m hm).arr_nodes.1) m hm
  have hV30 : ∀ x, x ∈ [G_ 30] → x < IN := fun x hx => by simp at hx; subst hx; addr3
  have hX1 : m1 (X_ 0) = m (X_ 0) := ag1.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)
  have hheap1 : ∀ x, IN ≤ x → x < m HP → m1 x = m x := fun x h1 h2 => ag1.heap hV30 x h1 h2
  obtain ⟨p, hp⟩ : ∃ p, p = m (m NODES + 1 + m (X_ 0)) := ⟨_, rfl⟩
  rw [← hp] at hv1 a3 a4
  have hsz := repNode_size a4
  -- the tag
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (G_ 32) (m p) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (load (G_ 32) (G_ 30)) m1 m2 1 := by
    have := Exec.load (G_ 32) (G_ 30) m1
    rwa [hv1, hheap1 p a3 (by omega), ← hm2] at this
  have q2 : ∀ x, x ≠ G_ 32 → m2 x = m1 x := fun x hx => by rw [hm2, Mem.write_ne _ _ hx]
  have hG32 : m2 (G_ 32) = m p := by rw [hm2, Mem.write_same]
  have hz2 : m2 ZERO = 0 := by rw [q2 _ (by addr3), ag1.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hi.ctx.2.1
  have ag2 : Agree m m2 [G_ 30, G_ 32] := by
    refine ⟨fun x hx hxV => ?_, by rw [q2 _ (by addr3), hHP1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
    rw [q2 _ hxV.2.2]
    exact ag1.var x hx hxV.1 (by simp; exact hxV.2.1)
  have hV32 : ∀ x, x ∈ [G_ 30, G_ 32] → x < IN := fun x hx => by
    simp at hx; rcases hx with rfl | rfl <;> addr3
  have hheap2 : ∀ x, IN ≤ x → x < m HP → m2 x = m x := fun x h1 h2 => ag2.heap hV32 x h1 h2
  have hX2 : m2 (X_ 0) = m (X_ 0) := ag2.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)
  have hctx2 : Ctx m2 := Ctx.of_agree hi.ctx ag2 (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> addr3)
  have hG30 : m2 (G_ 30) = p := by rw [q2 _ (by addr3), hv1]
  have hHP2 : m2 HP = m HP := by rw [q2 _ (by addr3), hHP1]
  have hnode : g.base.nodes.getD (m (X_ 0)) (.src 0) = g.base.nodes[m (X_ 0)] := List.getD_eq_getElem _ _ hj'
  rcases repNode_cases a4 with ⟨t0, i, hsrc, _⟩ | ⟨t1, f, args, happ, _, ra⟩
  · -- source: a fresh empty array
    have hc : (Cond.eq (G_ 32) ZERO).eval m2 = true := by simp [Cond.eval, hG32, t0, hz2]
    obtain ⟨m3, k3, e3, hk3, ag3, hD3, hh3, hHP3⟩ := emptyArrM_spec (G_ 31) (by constructor <;> addr3)
      (fun m => Ctx m) (fun _ h => h) m2 hctx2
    refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc e3)), by omega,
      (ag2.trans ag3).mono (fun x hx => by simp at hx ⊢; tauto), ?_, ?_⟩
    · refine ⟨by rw [hD3, hHP2]; exact hhp, by rw [hD3, hh3, hHP3], ?_⟩
      rw [hD3]
      unfold arrAt
      rw [hh3]
      unfold GInstance.argsOf
      rw [hnode, hsrc]; rfl
    · exact (ag3.var (X_ 0) (lt_hp (by rw [hHP2]; exact hhp) (by decide)) (by decide) (by decide)).trans hX2
  · -- application: the argument array
    have hc : (Cond.eq (G_ 32) ZERO).eval m2 = false := by simp [Cond.eval, hG32, t1, hz2]
    obtain ⟨m3, k3, e3, hk3, ag3, hD3, hHP3⟩ := field2M_spec (G_ 30) (G_ 31) (by constructor <;> addr3) (by decide)
      (fun m => Ctx m ∧ IN ≤ m (G_ 30)) (fun _ h => h.1) (fun _ h => h.2) m2 ⟨hctx2, by rw [hG30]; exact a3⟩
    obtain ⟨g1, g2⟩ := repArr_bounds ra
    refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_false hc e3)), by omega,
      (ag2.trans ag3).mono (fun x hx => by simp at hx ⊢; tauto), ?_, ?_⟩
    · have hV31 : ∀ x, x ∈ [G_ 31] → x < IN := fun x hx => by simp at hx; subst hx; addr3
      have hcell : m2 (p + 2) = m (p + 2) := hheap2 (p + 2) (by omega) (by
        rw [happ] at a4; have := a4.2.1; omega)
      have hcell2 : m2 (m (p + 2)) = m (m (p + 2)) := hheap2 _ g1 (by omega)
      unfold ArrIs
      rw [hD3, hG30, hcell]
      refine ⟨g1, ?_, ?_⟩
      · rw [ag3.heap hV31 _ g1 (by rw [hHP2]; omega), hHP3, hHP2, hcell2]; exact g2
      · rw [ag3.arrAt hV31 _ g1 (by rw [hHP2, hcell2]; exact g2)]
        rw [arrAt_congr (fun x h1 h2 => hheap2 x (by omega) (by omega)), repArr_arrAt ra]
        unfold GInstance.argsOf
        rw [hnode, happ]
    · exact (ag3.var (X_ 0) (lt_hp (by rw [hHP2]; exact hhp) (by decide)) (by decide) (by decide)).trans hX2


/-- `(VAL, V2) := (2 ids[X_ 1] + 1, 2 ids[X_ 0])`. -/
def edgePairM : Cmd :=
  .seq (getDM IDS (X_ 1) (G_ 33)) (.seq (add VAL (G_ 33) (G_ 33)) (.seq (add VAL VAL ONE)
    (.seq (getDM IDS (X_ 0) (G_ 34)) (add V2 (G_ 34) (G_ 34)))))

theorem edgePairM_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → IdsCtx k g m) :
    FunSpec2 edgePairM [G_ 33, VAL, G_ 34, V2] 15 Pre
      (fun m => (2 * g.base.canonIds.getD (m (X_ 1)) 0 + 1, 2 * g.base.canonIds.getD (m (X_ 0)) 0)) := by
  intro m hm
  have hi := hctx m hm
  have hhp : 200 ≤ m HP := hi.1.ctx.2.2
  have hone := hi.1.ctx.1
  obtain ⟨m1, k1, e1, hk1, ag1, hv1, hHP1⟩ := getDM_spec IDS (X_ 1) (G_ 33) (by constructor <;> addr3)
    (by decide) (by decide) (fun m => IdsCtx k g m) (fun m hm => hm.1.ctx) (fun m hm => hm.2.1) m hi
  rw [hi.2.2.2] at hv1
  have hV33 : ∀ x, x ∈ [G_ 33] → x < IN := fun x hx => by simp at hx; subst hx; addr3
  have hi1 : IdsCtx k g m1 := (IdsCtx.stable (safeVars_of_decide _ (by decide)) (by decide) ag1 hi).1
  have m1one : m1 ONE = 1 := by rw [ag1.var ONE (lt_hp hhp (by decide)) (by decide) (by decide), hone]
  have m1X0 : m1 (X_ 0) = m (X_ 0) := ag1.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)
  obtain ⟨v, hv⟩ : ∃ v, v = g.base.canonIds.getD (m (X_ 1)) 0 := ⟨_, rfl⟩
  rw [← hv] at hv1
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write VAL (v + v) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add VAL (G_ 33) (G_ 33)) m1 m2 1 := by
    have := Exec.add VAL (G_ 33) (G_ 33) m1; rwa [hv1, ← hm2] at this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m1.write VAL (v + v + 1) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add VAL VAL ONE) m2 m3 1 := by
    have := Exec.add VAL VAL ONE m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr3), m1one, Mem.write_write] at this
    rw [hm3, hm2]; exact this
  have ag3 : Agree m1 m3 [VAL] := by rw [hm3]; exact Agree.write m1 VAL _ (by addr3)
  have hi3 : IdsCtx k g m3 := (IdsCtx.stable (safeVars_of_decide _ (by decide)) (by decide) ag3 hi1).1
  obtain ⟨m4, k4, e4, hk4, ag4, hv4, hHP4⟩ := getDM_spec IDS (X_ 0) (G_ 34) (by constructor <;> addr3)
    (by decide) (by decide) (fun m => IdsCtx k g m) (fun m hm => hm.1.ctx) (fun m hm => hm.2.1) m3 hi3
  rw [hi3.2.2.2] at hv4
  have m3X0 : m3 (X_ 0) = m (X_ 0) := by rw [hm3, Mem.write_ne _ _ (by addr3), m1X0]
  rw [m3X0] at hv4
  obtain ⟨w, hw⟩ : ∃ w, w = g.base.canonIds.getD (m (X_ 0)) 0 := ⟨_, rfl⟩
  rw [← hw] at hv4
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write V2 (w + w) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add V2 (G_ 34) (G_ 34)) m4 m5 1 := by
    have := Exec.add V2 (G_ 34) (G_ 34) m4; rwa [hv4, ← hm5] at this
  have hHP3 : m3 HP = m HP := by rw [hm3, Mem.write_ne _ _ (by addr3), hHP1]
  have m4VAL : m4 VAL = v + v + 1 := by
    rw [ag4.var VAL (lt_hp (by rw [hHP3]; exact hhp) (by decide)) (by decide) (by decide), hm3, Mem.write_same]
  refine ⟨m5, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e5))), by omega, ?_, ?_⟩
  · refine (((ag1.trans ag3).trans ag4).trans (by rw [hm5]; exact Agree.write m4 V2 _ (by addr3))).mono
      (fun x hx => by simp at hx ⊢; tauto)
  · show (m5 VAL, m5 V2) = _
    rw [hm5, Mem.write_ne _ _ (by addr3), Mem.write_same, m4VAL, hv, hw]
    simp only [Prod.mk.injEq]; omega

/-- The edge arcs of node `X_ 0`, as a fresh array of records (address in `VAL`). -/
def argsPairsM : Cmd := .seq argsPtrM (.seq (mapPairM 1 (G_ 31) edgePairM) (mov VAL (OUT_ 1)))

/-- The edge-arc list of node `j`. -/
def edgeList (g : GInstance) (j : ℕ) : List (ℕ × ℕ) :=
  (g.argsOf j).map (fun a => (2 * g.base.canonIds.getD a 0 + 1, 2 * g.base.canonIds.getD j 0))

/-- The structure produced by `argsPairsM`: a record array holding `edgeList g j`, all in `[q, HP)`. -/
def EdgePost (g : GInstance) (j : ℕ) (m : Mem) (q : ℕ) : Prop :=
  IN ≤ q ∧ q + 1 + m q ≤ m HP ∧ pairsAt m q = edgeList g j ∧ RecsIn m q (q + 1 + m q) (m HP)

theorem EdgePost.stable (g : GInstance) : PostStable (EdgePost g) := by
  intro j m₂ m₃ q h hc hhp
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hq : m₃ q = m₂ q := hc q le_rfl (by omega)
  refine ⟨h1, by rw [hq]; omega, ?_, ?_⟩
  · rw [← h3]
    apply pairsAt_congr (arrAt_congr (fun x hx1 hx2 => hc x hx1 (by omega)))
    intro p hp
    obtain ⟨hp1, hp2⟩ := h4 p hp
    exact ⟨hc p (by omega) (by omega), hc (p + 1) (by omega) (by omega)⟩
  · rw [hq]
    intro p hp
    rw [arrAt_congr (fun x hx1 hx2 => hc x hx1 (by omega))] at hp
    exact ⟨(h4 p hp).1, le_trans (h4 p hp).2 hhp⟩

theorem argsOf_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) (j : ℕ) : (g.argsOf j).length ≤ n := by
  unfold GInstance.argsOf
  by_cases hj : j < g.base.nodes.length
  · rw [List.getD_eq_getElem _ _ hj]
    have hmem := List.getElem_mem hj
    generalize g.base.nodes[j] = nd at hmem
    cases nd with
    | src i => simp
    | app f args => exact hn.args _ hmem f args rfl
  · rw [List.getD_eq_default _ _ (by omega)]; simp

def argsPairsV : List ℕ := [G_ 30, G_ 32, G_ 31] ++ ((Lvars 1 ++ [G_ 33, VAL, G_ 34, V2]) ++ [VAL])

theorem argsPairsV_safe : SafeVars argsPairsV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (SafeVars.append (safeVars_Lvars 1 (by norm_num))
    (safeVars_of_decide _ (by decide))) (safeVars_of_decide _ (by decide)))

theorem argsPairsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    AllocSpec argsPairsM argsPairsV (9 + (n * (15 + 14) + 9) + 1)
      (fun m => NC1 k g m ∧ m (X_ 0) ∈ arrAt m (m RNGN)) (X_ 0) (EdgePost g) := by
  intro m hm
  have hi : IdsCtx k g m := hm.1.1.1
  have hhp : 200 ≤ m HP := hi.1.ctx.2.2
  have hj : m (X_ 0) < g.base.nodes.length := by
    have := hm.2; rw [hm.1.1.2.1.2.2, List.mem_range] at this; exact this
  -- the argument array
  obtain ⟨m1, k1, e1, hk1, ag1, harr1, hX1⟩ := argsPtrM_spec k g
    (fun m => NC1 k g m ∧ m (X_ 0) ∈ arrAt m (m RNGN)) (fun m hm => hm.1.1.1.1)
    (fun m hm => by have := hm.2; rw [hm.1.1.2.1.2.2, List.mem_range] at this; exact this) m hm
  have hs1 : SafeVars [G_ 30, G_ 32, G_ 31] := safeVars_of_decide _ (by decide)
  have hn1 : NC1 k g m1 := NC1.stableP hs1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    m m1 hm.1 ag1
  -- the pair map
  let Pre1 : Mem → Prop := fun m => NC1 k g m ∧ ArrIs m (G_ 31) (g.argsOf (m (X_ 0)))
  have hsV : SafeVars (Lvars 1 ++ [G_ 33, VAL, G_ 34, V2]) :=
    SafeVars.append (safeVars_Lvars 1 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hPre1 : StableP Pre1 (Lvars 1 ++ [G_ 33, VAL, G_ 34, V2]) := by
    intro m m' hm hag
    have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
    refine ⟨NC1.stableP hsV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m m' hm.1 hag, ?_⟩
    rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)]
    exact hm.2.stable hag (fun x hx => (hsV x hx).2.1) (by addr3) (by addr3) (by decide)
  obtain ⟨m2, k2, e2, hk2, ag2, hO2, hpairs2, hrec2, hroom2⟩ := mapPairM_spec 1 (G_ 31) n
    (edgePairM_spec k g (fun m => Pre1 m ∧ m (X_ 1) ∈ arrAt m (m (G_ 31))) (fun m hm => hm.1.1.1.1))
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (fun m hm => hm.1.1.1.1.ctx)
    (fun m hm => ⟨hm.2.1, hm.2.2.1, by rw [hm.2.len]; exact argsOf_length_le hn _⟩) hPre1
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      show (2 * g.base.canonIds.getD (m' (X_ 1)) 0 + 1, 2 * g.base.canonIds.getD (m' (X_ 0)) 0) =
        (2 * g.base.canonIds.getD (m (X_ 1)) 0 + 1, 2 * g.base.canonIds.getD (m (X_ 0)) 0)
      rw [hag.var (X_ 1) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
    m1 ⟨hn1, by rw [hX1]; exact harr1⟩
  have hHP1 : m HP ≤ m1 HP := ag1.2
  have hhp1 : 200 ≤ m1 HP := by omega
  have hX2 : m2 (X_ 0) = m1 (X_ 0) := ag2.var (X_ 0) (lt_hp hhp1 (by decide)) (by decide) (by decide)
  -- VAL := OUT_ 1
  refine ⟨m2.write VAL (m2 (OUT_ 1)), _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Exec.mov _ _ _)), by omega, ?_, ?_, ?_, ?_⟩
  · exact ((ag1.trans ag2).trans (Agree.write m2 VAL _ (by addr3))).mono (fun x hx => by unfold argsPairsV; exact hx)
  · rw [Mem.write_same, hO2]; exact hHP1
  · rw [Mem.write_same, Mem.write_ne _ _ (by addr3), hO2]; have := harr1.len; omega
  · rw [Mem.write_same, hO2]
    have hVlt : ∀ x, x ∈ [VAL] → x < IN := fun x hx => by simp at hx; subst hx; addr3
    have hlen : m2 (m1 HP) = m1 (m1 (G_ 31)) := by
      have := congrArg List.length hpairs2
      simp only [pairsAt, List.length_map, arrAt_length] at this
      exact this
    have hrec' : RecsIn m2 (m1 HP) (m1 HP + 1 + m2 (m1 HP)) (m2 HP) := by rw [hlen]; exact hrec2
    have hpw : pairsAt (m2.write VAL (m1 HP)) (m1 HP) = pairsAt m2 (m1 HP) := by
      apply pairsAt_congr (arrAt_write_lo _ _ _ _ (by addr3) hhp1)
      intro q hq
      obtain ⟨hq1, _⟩ := hrec' q hq
      rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]; exact ⟨rfl, rfl⟩
    refine ⟨hhp1, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hlen]; exact hroom2
    · rw [hpw, hpairs2, harr1.2.2]
      unfold edgeList
      apply List.map_congr_left
      intro a _
      rw [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide), hX1]
    · rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]
      intro q hq
      rw [arrAt_write_lo _ _ _ _ (by addr3) hhp1] at hq
      exact hrec' q hq


/-- The array of edge-arc arrays at `G_ 45`. -/
def EdgeArrs (g : GInstance) (m : Mem) : Prop :=
  IN ≤ m (G_ 45) ∧ m (G_ 45) + 1 + m (m (G_ 45)) ≤ m HP ∧ m (m (G_ 45)) = g.base.nodes.length ∧
    ∀ i, i < g.base.nodes.length → m (G_ 45) + 1 + g.base.nodes.length ≤ m (m (G_ 45) + 1 + i) ∧
      EdgePost g i m (m (m (G_ 45) + 1 + i))

theorem EdgeArrs.stable {g : GInstance} {V : List ℕ} (hV : ∀ x, x ∈ V → x < IN) (h45 : G_ 45 ∉ V)
    {m m' : Mem} (hag : Agree m m' V) (hhp : IN ≤ m HP) (h : EdgeArrs g m) : EdgeArrs g m' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hG : m' (G_ 45) = m (G_ 45) := hag.var (G_ 45) (by addr3) (by addr3) h45
  have hc : m' (m (G_ 45)) = m (m (G_ 45)) := hag.heap hV _ h1 (by omega)
  refine ⟨by rw [hG]; exact h1, by rw [hG, hc]; exact le_trans h2 hag.2, by rw [hG, hc]; exact h3, ?_⟩
  intro i hi
  obtain ⟨c1, c2⟩ := h4 i hi
  have hcell : m' (m (G_ 45) + 1 + i) = m (m (G_ 45) + 1 + i) := hag.heap hV _ (by omega) (by omega)
  rw [hG, hcell]
  exact ⟨c1, EdgePost.stable g _ _ _ _ c2 (fun y hy hy' => hag.heap hV y (by have := c2.1; omega) hy') hag.2⟩

theorem EdgeArrs.stableP {g : GInstance} {V : List ℕ} (hV : ∀ x, x ∈ V → x < IN) (h45 : G_ 45 ∉ V)
    (hhp : ∀ m, EdgeArrs g m → IN ≤ m HP) : StableP (EdgeArrs g) V :=
  fun m m' hm hag => hm.stable hV h45 hag (hhp m hm)

/-- The edge arcs before deduplication. -/
def edgeFlat (g : GInstance) : List (ℕ × ℕ) := (List.range g.base.nodes.length).flatMap (fun j => edgeList g j)

theorem edgeArcsL_eq (g : GInstance) : g.edgeArcsL g.base.canonIds = dedupList (edgeFlat g) := rfl

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (n : ℕ) (h : ∀ x, x ∈ l → (f x).length ≤ n) :
    (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x (List.mem_cons_self ..)
    rw [Nat.succ_mul]; omega

theorem edgeFlat_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) : (edgeFlat g).length ≤ n * n := by
  unfold edgeFlat
  have := length_flatMap_le (List.range g.base.nodes.length) (fun j => edgeList g j) n
    (fun j _ => by unfold edgeList; rw [List.length_map]; exact argsOf_length_le hn j)
  rw [List.length_range] at this
  exact le_trans this (Nat.mul_le_mul_right _ hn.nodes)

/-- `G_ 47 := edgeArcsL ids`. -/
def edgeArcsM : Cmd :=
  .seq (.seq (mapM 0 RNGN argsPairsM) (mov (G_ 45) (OUT_ 0)))
  (.seq (.seq (flattenM 0 (G_ 45)) (mov (G_ 46) (OUT_ 0)))
        (.seq (dedupM 0 (G_ 46)) (mov (G_ 47) (OUT_ 0))))

def edgeArcsV : List ℕ :=
  (Lvars 0 ++ argsPairsV ++ [G_ 45]) ++ ((Lvars 0 ++ Lvars 1 ++ [G_ 46]) ++ (dedupV 0 ++ [G_ 47]))

theorem dedupV0_safe : SafeVars (dedupV 0) := by
  unfold dedupV
  exact SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_memPairV 1 (by norm_num))

theorem edgeArcsV_safe : SafeVars edgeArcsV :=
  SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) argsPairsV_safe)
    (safeVars_of_decide _ (by decide)))
  (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_Lvars 1 (by norm_num)))
    (safeVars_of_decide _ (by decide))) (SafeVars.append dedupV0_safe (safeVars_of_decide _ (by decide))))

theorem edgeArcsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec edgeArcsM edgeArcsV
      ((n * ((9 + (n * (15 + 14) + 9) + 1) + 9) + 9 + 1) + ((12 * n * n + 18 * n + 13 + 1) +
        (23 * (n * n) * (n * n) + 23 * (n * n) + 8 + 1)))
      (NC1 k g) (fun _ m' => NC1 k g m' ∧ PArrIs m' (G_ 47) (g.edgeArcsL g.base.canonIds)) := by
  have hs1 : SafeVars (Lvars 0 ++ argsPairsV) := SafeVars.append (safeVars_Lvars 0 (by norm_num)) argsPairsV_safe
  have hs1' : SafeVars (Lvars 0 ++ argsPairsV ++ [G_ 45]) := SafeVars.append hs1 (safeVars_of_decide _ (by decide))
  -- E1
  have hE1 := mapArrM_spec 0 RNGN n (argsPairsM_spec k g n hn) (by norm_num)
    (fun x hx => ⟨(argsPairsV_safe x hx).1, (argsPairsV_safe x hx).2.1⟩) (by constructor <;> addrn) (by decide)
    (by decide) (by decide) (fun m hm => hm.1.1.1.ctx)
    (fun m hm => ⟨hm.1.2.1.1, hm.1.2.1.2.1, by rw [hm.1.2.1.len, List.length_range]; exact hn.nodes⟩)
    (NC1.stableP hs1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (EdgePost.stable g)
  have s1 := (RSpec.seq_mov 0 (G_ 45) (by constructor <;> addr3) hE1
    (fun m m' v hm hr => by
      have hhp := hm.1.1.1.ctx.2.2
      refine ⟨by rw [Mem.write_ne _ _ (by addr3)]; exact hr.1, ?_, by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2.2⟩
      intro i hi
      obtain ⟨c1, c2, c3⟩ := hr.2.1 i hi
      rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]
      exact ⟨c1, c2, EdgePost.stable g _ _ _ _ c3 (fun y hy _ => Mem.write_ne _ _ (by addr3))
        (by rw [Mem.write_ne _ _ (by addr3)])⟩)).mono'
    (Post' := fun _ m' => EdgeArrs g m') (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => by
      obtain ⟨hP', hlen, hcells, hroom⟩ := hp
      have hhp := hm.1.1.1.ctx.2.2
      have hrng := hm.1.2.1
      rw [hrng.len, List.length_range] at hlen hroom
      refine ⟨by rw [hP']; exact hhp, by rw [hP', hlen]; exact hroom, by rw [hP', hlen], ?_⟩
      intro i hi
      have hi' : i < (arrAt m (m RNGN)).length := by rw [hrng.2.2, List.length_range]; exact hi
      obtain ⟨c1, c2, c3⟩ := hcells i hi'
      rw [hrng.2.2, List.length_range] at c1
      have hidx : (arrAt m (m RNGN))[i] = i := by
        have := List.getElem_of_eq hrng.2.2 hi'; rw [this, List.getElem_range]
      rw [hidx] at c3
      rw [hP']
      exact ⟨c1, c3⟩)
  have s1' := s1.carry (NC1.stableP hs1' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- E2
  let P2 : Mem → Prop := fun m => NC1 k g m ∧ EdgeArrs g m
  have hs2 : SafeVars (Lvars 0 ++ Lvars 1) := SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_Lvars 1 (by norm_num))
  have hs2' : SafeVars (Lvars 0 ++ Lvars 1 ++ [G_ 46]) := SafeVars.append hs2 (safeVars_of_decide _ (by decide))
  have hE2 := flattenM_spec 0 (G_ 45) n (by norm_num) (by constructor <;> addr3) (by decide) (by decide) P2
    (fun m hm => hm.1.1.1.1.ctx)
    (fun m hm => ⟨hm.2.1, hm.2.2.1, fun q hq => by
      rw [List.mem_iff_getElem] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      rw [arrAt_length, hm.2.2.2.1] at hi
      rw [arrAt_getElem]
      exact ⟨(hm.2.2.2.2 i hi).2.1, (hm.2.2.2.2 i hi).2.2.1⟩⟩)
    (fun m hm => ⟨by rw [hm.2.2.2.1]; exact hn.nodes, fun q hq => by
      rw [List.mem_iff_getElem] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      rw [arrAt_length, hm.2.2.2.1] at hi
      rw [arrAt_getElem]
      have := (hm.2.2.2.2 i hi).2.2.2.1
      have hl : m (m (m (G_ 45) + 1 + i)) = (edgeList g i).length := by
        rw [← this, pairsAt, List.length_map, arrAt_length]
      rw [hl]; unfold edgeList; rw [List.length_map]; exact argsOf_length_le hn i⟩)
  have hP2 : StableP P2 (Lvars 0 ++ Lvars 1 ++ [G_ 46]) :=
    (NC1.stableP hs2' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (EdgeArrs.stableP (fun x hx => (hs2' x hx).2.1) (by decide) (fun m hm => by have := hm.1; have := hm.2.1; omega))
  have s2 := (RSpec.seq_mov 0 (G_ 46) (by constructor <;> addr3) hE2
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ (by addr3) hm.1.1.1.1.ctx.2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)).mono'
    (Post' := fun _ m' => PArrIs m' (G_ 46) (edgeFlat g)) (fun x hx => hx) le_rfl (fun m hm => hm)
    (fun m m' hm hag hp => by
      obtain ⟨hP', harr, hroom⟩ := hp
      have hhp := hm.1.1.1.1.ctx.2.2
      obtain ⟨e1, e2, e3, e4⟩ := hm.2
      have hV' : ∀ x, x ∈ Lvars 0 ++ Lvars 1 ++ [G_ 46] → x < IN := fun x hx => (hs2' x hx).2.1
      -- the outer array as a list of pointers
      have houter : arrAt m (m (G_ 45)) = (List.range g.base.nodes.length).map (fun i => m (m (G_ 45) + 1 + i)) := by
        unfold arrAt; rw [e3]
      -- every flattened pointer is a record below the old heap pointer
      have hptr : ∀ q, q ∈ ((arrAt m (m (G_ 45))).map (fun a => arrAt m a)).flatten → IN ≤ q ∧ q + 2 ≤ m HP := by
        intro q hq
        rw [List.mem_flatten] at hq
        obtain ⟨l, hl, hql⟩ := hq
        rw [List.mem_map] at hl
        obtain ⟨a, ha, rfl⟩ := hl
        rw [houter, List.mem_map] at ha
        obtain ⟨i, hi, rfl⟩ := ha
        rw [List.mem_range] at hi
        obtain ⟨_, p1, _, _, hrec⟩ := e4 i hi
        exact ⟨by have := (hrec q hql).1; omega, (hrec q hql).2⟩
      have hsum : m' (m HP) = ((arrAt m (m (G_ 45))).map (fun q => m q)).sum := by
        rw [← arrAt_length m' (m HP), harr, List.length_flatten, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        simp only [Function.comp, arrAt_length]
      refine ⟨⟨by rw [hP']; exact hhp, by rw [hP', hsum]; exact hroom, ?_⟩, ?_⟩
      · rw [hP']
        intro q hq
        rw [harr] at hq
        obtain ⟨h1, h2⟩ := hptr q hq
        exact ⟨h1, le_trans h2 hag.2⟩
      · rw [hP']
        unfold pairsAt
        rw [harr, List.map_flatten, List.map_map]
        unfold edgeFlat
        rw [List.flatMap_def, houter, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        obtain ⟨_, p1, _, hpairs, hrec⟩ := e4 i hi
        simp only [Function.comp]
        rw [← hpairs]
        unfold pairsAt
        apply List.map_congr_left
        intro q hq
        obtain ⟨hq1, hq2⟩ := hrec q hq
        rw [hag.heap hV' q (by omega) (by omega), hag.heap hV' (q + 1) (by omega) (by omega)])
  have s2' := s2.carry hP2
  -- E3
  let P3 : Mem → Prop := fun m => P2 m ∧ PArrIs m (G_ 46) (edgeFlat g)
  have hs3 : SafeVars (dedupV 0 ++ [G_ 47]) := SafeVars.append dedupV0_safe (safeVars_of_decide _ (by decide))
  have hP3 : StableP P3 (dedupV 0 ++ [G_ 47]) :=
    ((NC1.stableP hs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (EdgeArrs.stableP (fun x hx => (hs3 x hx).2.1) (by decide)
        (fun m hm => by have := hm.1; have := hm.2.1; omega))).and
      (PArrIs.stableP (P := G_ 46) (fun x hx => (hs3 x hx).2.1) (by addr3) (by addr3) (by decide))
  have s3 := (dedupM_parr_spec 0 (G_ 46) (G_ 47) (n * n) (edgeFlat g) (by norm_num) (by constructor <;> addr3)
    (by decide) (by constructor <;> addr3) (by decide) P3 (fun m hm => hm.1.1.1.1.1.ctx) (fun m hm => hm.2)
    (edgeFlat_length_le hn)).carry hP3
  -- assembly
  have hall := s1'.seqP (s2'.seqP s3)
  unfold edgeArcsM edgeArcsV
  refine hall.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  rw [edgeArcsL_eq]
  exact ⟨hp.1.1.1, hp.2⟩


/-! ### Source arcs -/

theorem isSrcNode_eq (g : GInstance) (j : ℕ) {m : Mem} {lo hi p : ℕ}
    (h : RepNode m lo hi p (g.base.nodes.getD j (.src 0))) : g.isSrcNode j = decide (m p = 0) := by
  unfold GInstance.isSrcNode
  rcases repNode_cases h with ⟨h0, i, he, _⟩ | ⟨h1, f, args, he, _, _⟩
  · rw [he, h0]; rfl
  · rw [he, h1]; rfl

/-- `isSrcNode (X_ 0)`. -/
def isSrcT : Cmd := .seq (elemM NODES (X_ 0) (G_ 1)) (.seq (load (G_ 2) (G_ 1)) (eqTest (G_ 2) ZERO))

theorem isSrcT_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → InstCtx k g m)
    (hj : ∀ m, Pre m → m (X_ 0) < g.base.nodes.length) (hstab : StableP Pre [G_ 1, G_ 2]) :
    TestSpec isSrcT [G_ 1, G_ 2, FLAG] 7 Pre (fun m => g.isSrcNode (m (X_ 0))) := by
  have hs1 : SafeVars [G_ 1] := safeVars_of_decide _ (by decide)
  have hs2 : SafeVars [G_ 2] := safeVars_of_decide _ (by decide)
  have hst1 : StableP Pre [G_ 1] := hstab.mono (fun x hx => by simp at hx ⊢; tauto)
  have hst2 : StableP Pre [G_ 2] := hstab.mono (fun x hx => by simp at hx ⊢; tauto)
  have hnode : ∀ m, Pre m → IN ≤ m NODES + 1 + m (X_ 0) ∧ m NODES + 1 + m (X_ 0) < m HP ∧
      IN ≤ m (m NODES + 1 + m (X_ 0)) ∧ m (m NODES + 1 + m (X_ 0)) + 2 ≤ m HP ∧
      RepNode m IN (m HP) (m (m NODES + 1 + m (X_ 0))) (g.base.nodes.getD (m (X_ 0)) (.src 0)) :=
    fun m hm => (hctx m hm).node_at (by rw [(hctx m hm).nn]; exact hj m hm)
  let Pre1 : Mem → Prop := fun m => Pre m ∧ m (G_ 1) = m (m NODES + 1 + m (X_ 0))
  have e1 := elemM_spec NODES (X_ 0) (G_ 1) (by constructor <;> addr3) (by decide) (by decide) Pre
    (fun m hm => (hctx m hm).ctx) (fun m hm => (hctx m hm).arr_nodes.1)
  have e2 := loadM_spec (G_ 1) (G_ 2) (by constructor <;> addr3) Pre1
  have t2 := TestSpec.after e2 (eqTest_spec (G_ 2) ZERO (fun m => Pre1 m ∧ m (G_ 2) = m (m (G_ 1))))
    (Q := fun m => decide (m (m (G_ 1)) = 0))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm.1).ctx.2.2
      obtain ⟨a1, a2, a3, a4, _⟩ := hnode m hm.1
      have hV : ∀ x, x ∈ [G_ 2] → x < IN := fun x hx => (hs2 x hx).2.1
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine ⟨⟨hst2 m m₁ hm.1 hag, ?_⟩, ?_⟩
      · rw [hG1, hag.var NODES (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV _ a1 a2]; exact hm.2
      · rw [hp.1, hG1, hag.heap hV _ (by rw [hm.2]; exact a3) (by rw [hm.2]; omega)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm.1).ctx.2.2
      dsimp only
      rw [hp.1, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide), (hctx m hm.1).ctx.2.1])
  have t1 := TestSpec.after e1 t2 (Q := fun m => g.isSrcNode (m (X_ 0)))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm).ctx.2.2
      obtain ⟨a1, a2, _⟩ := hnode m hm
      have hV : ∀ x, x ∈ [G_ 1] → x < IN := fun x hx => (hs1 x hx).2.1
      refine ⟨hst1 m m₁ hm hag, ?_⟩
      rw [hp.1, hag.var NODES (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV _ a1 a2])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm).ctx.2.2
      obtain ⟨a1, a2, a3, a4, a5⟩ := hnode m hm
      have hV : ∀ x, x ∈ [G_ 1] → x < IN := fun x hx => (hs1 x hx).2.1
      dsimp only
      rw [hp.1, hag.heap hV _ a3 (by omega), isSrcNode_eq g _ a5])
  unfold isSrcT
  exact t1.mono (fun x hx => by simp at hx ⊢; tauto) (by omega) (fun m hm => hm)

/-- `(VAL, V2) := (NETS, 2 ids[X_ 0])`. -/
def srcPairM : Cmd := .seq (mov VAL NETS) (.seq (getDM IDS (X_ 0) (G_ 3)) (add V2 (G_ 3) (G_ 3)))

theorem srcPairM_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → IdsCtx k g m) :
    FunSpec2 srcPairM [VAL, G_ 3, V2] 8 Pre (fun m => (m NETS, 2 * g.base.canonIds.getD (m (X_ 0)) 0)) := by
  intro m hm
  have hi := hctx m hm
  have hhp : 200 ≤ m HP := hi.1.ctx.2.2
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write VAL (m NETS) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov VAL NETS) m m1 1 := by rw [hm1]; exact Exec.mov _ _ _
  have ag1 : Agree m m1 [VAL] := by rw [hm1]; exact Agree.write m VAL _ (by addr3)
  have hi1 : IdsCtx k g m1 := (IdsCtx.stable (safeVars_of_decide _ (by decide)) (by decide) ag1 hi).1
  obtain ⟨m2, k2, e2, hk2, ag2, hv2, hHP2⟩ := getDM_spec IDS (X_ 0) (G_ 3) (by constructor <;> addr3)
    (by decide) (by decide) (fun m => IdsCtx k g m) (fun m hm => hm.1.ctx) (fun m hm => hm.2.1) m1 hi1
  rw [hi1.2.2.2, hm1, Mem.write_ne _ _ (by addr3)] at hv2
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write V2 (m2 (G_ 3) + m2 (G_ 3)) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add V2 (G_ 3) (G_ 3)) m2 m3 1 := by rw [hm3]; exact Exec.add _ _ _ _
  refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), by omega, ?_, ?_⟩
  · exact ((ag1.trans ag2).trans (by rw [hm3]; exact Agree.write m2 V2 _ (by addr3))).mono
      (fun x hx => by simp at hx ⊢; tauto)
  · show (m3 VAL, m3 V2) = _
    have hhp1 : 200 ≤ m1 HP := by rw [hm1, Mem.write_ne _ _ (by addr3)]; exact hhp
    rw [hm3, Mem.write_ne _ _ (by addr3), Mem.write_same, hv2,
      ag2.var VAL (lt_hp hhp1 (by decide)) (by decide) (by decide), hm1, Mem.write_same]
    simp only [Prod.mk.injEq, true_and]
    omega

/-- `G_ 50 := srcArcsL ids`. -/
def srcArcsM : Cmd :=
  .seq (.seq (filterM 0 RNGN isSrcT) (mov (G_ 48) (OUT_ 0)))
  (.seq (.seq (mapPairM 0 (G_ 48) srcPairM) (mov (G_ 49) (OUT_ 0)))
        (.seq (dedupM 0 (G_ 49)) (mov (G_ 50) (OUT_ 0))))

def srcArcsV : List ℕ :=
  (Lvars 0 ++ FLAG :: [G_ 1, G_ 2, FLAG] ++ [G_ 48]) ++ ((Lvars 0 ++ [VAL, G_ 3, V2] ++ [G_ 49]) ++ (dedupV 0 ++ [G_ 50]))

theorem srcArcsV_safe : SafeVars srcArcsV :=
  SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (safeVars_of_decide _ (by decide)))
  (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (safeVars_of_decide _ (by decide))) (SafeVars.append dedupV0_safe (safeVars_of_decide _ (by decide))))

theorem srcArcsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec srcArcsM srcArcsV
      ((n * (7 + 14) + 9 + 1) + ((n * (8 + 14) + 9 + 1) + (23 * n * n + 23 * n + 8 + 1)))
      (NC1 k g) (fun _ m' => NC1 k g m' ∧ PArrIs m' (G_ 50) (g.srcArcsL g.base.canonIds)) := by
  have hsrc : ((List.range g.base.nodes.length).filter g.isSrcNode).length ≤ n :=
    le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact hn.nodes)
  -- F1
  have hs1 : SafeVars (Lvars 0 ++ FLAG :: [G_ 1, G_ 2, FLAG]) :=
    SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hs1' : SafeVars (Lvars 0 ++ FLAG :: [G_ 1, G_ 2, FLAG] ++ [G_ 48]) :=
    SafeVars.append hs1 (safeVars_of_decide _ (by decide))
  have s1 := (filterM_arr_spec 0 RNGN (G_ 48) n (List.range g.base.nodes.length) g.isSrcNode
    (isSrcT_spec k g (fun m => NC1 k g m ∧ m (X_ 0) ∈ arrAt m (m RNGN)) (fun m hm => hm.1.1.1.1)
      (fun m hm => by have := hm.2; rw [hm.1.1.2.1.2.2, List.mem_range] at this; exact this)
      (fun m m' hm hag => by
        have hs12 : SafeVars [G_ 1, G_ 2] := safeVars_of_decide _ (by decide)
        have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
        refine ⟨NC1.stableP hs12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m m' hm.1 hag, ?_⟩
        rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var RNGN (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.arrAt (fun x hx => (hs12 x hx).2.1) _ hm.1.1.2.1.1 hm.1.1.2.1.2.1]
        exact hm.2))
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> constructor <;> addr3)
    (by constructor <;> addrn) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by constructor <;> addr3) (fun m hm => hm.1.1.1.ctx) (fun m hm => hm.1.2.1)
    (by rw [List.length_range]; exact hn.nodes)
    (NC1.stableP hs1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      show g.isSrcNode (m' (X_ 0)) = g.isSrcNode (m (X_ 0))
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x _ _ => by rw [Mem.write_same])).carry
    (NC1.stableP hs1' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- F2
  let P2 : Mem → Prop := fun m => NC1 k g m ∧ ArrIs m (G_ 48) ((List.range g.base.nodes.length).filter g.isSrcNode)
  have hs2 : SafeVars (Lvars 0 ++ [VAL, G_ 3, V2]) :=
    SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hs2' : SafeVars (Lvars 0 ++ [VAL, G_ 3, V2] ++ [G_ 49]) := SafeVars.append hs2 (safeVars_of_decide _ (by decide))
  have hP2 : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V → NETN ∉ V →
      G_ 48 ∉ V → StableP P2 V := fun hV h1 h2 h3 h4 h5 h6 h48 =>
    (NC1.stableP hV h1 h2 h3 h4 h5 h6).and
      (ArrIs.stableP (P := G_ 48) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h48)
  have s2 := (mapPairM_parr_spec 0 (G_ 48) (G_ 49) n _ (fun j => (g.netS, 2 * g.base.canonIds.getD j 0))
    (srcPairM_spec k g (fun m => P2 m ∧ m (X_ 0) ∈ arrAt m (m (G_ 48))) (fun m hm => hm.1.1.1.1))
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by constructor <;> addr3)
    (fun m hm => hm.1.1.1.1.ctx) (fun m hm => hm.2) hsrc (hP2 hs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      show (m' NETS, 2 * g.base.canonIds.getD (m' (X_ 0)) 0) = (m NETS, 2 * g.base.canonIds.getD (m (X_ 0)) 0)
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var NETS (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x hm _ => by rw [Mem.write_same, Mem.write_ne _ _ (by addrn), hm.1.2.1])).carry
    (hP2 hs2' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- F3
  let P3 : Mem → Prop := fun m => P2 m ∧ PArrIs m (G_ 49)
    (((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j => (g.netS, 2 * g.base.canonIds.getD j 0)))
  have hs3 : SafeVars (dedupV 0 ++ [G_ 50]) := SafeVars.append dedupV0_safe (safeVars_of_decide _ (by decide))
  have s3 := (dedupM_parr_spec 0 (G_ 49) (G_ 50) n _ (by norm_num) (by constructor <;> addr3) (by decide)
    (by constructor <;> addr3) (by decide) P3 (fun m hm => hm.1.1.1.1.1.ctx) (fun m hm => hm.2)
    (by rw [List.length_map]; exact hsrc)).carry
    ((hP2 hs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (PArrIs.stableP (P := G_ 49) (fun x hx => (hs3 x hx).2.1) (by addr3) (by addr3) (by decide)))
  have hall := s1.seqP (s2.seqP s3)
  unfold srcArcsM srcArcsV
  refine hall.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  exact ⟨hp.1.1.1, hp.2⟩


/-! ### Sink arcs -/

theorem idxOf_eq_firstIndex (l : List Node) (a d : Node) :
    l.idxOf a = Instance.firstIndex (fun i => decide (l.getD i d = a)) l.length := by
  have hidx : l.idxOf a = l.findIdx (· == a) := rfl
  rcases Instance.firstIndex_spec (fun i => decide (l.getD i d = a)) l.length with ⟨hlt, hpr, hmin⟩ | ⟨heq, hnone⟩
  · rw [hidx]
    simp only [decide_eq_true_eq, List.getD_eq_getElem _ _ hlt] at hpr
    have h1 : ¬ (l.findIdx (· == a) < Instance.firstIndex (fun i => decide (l.getD i d = a)) l.length) := by
      intro hc
      have hf : l.findIdx (· == a) < l.length := lt_trans hc hlt
      have := hmin _ hc
      simp only [decide_eq_false_iff_not, List.getD_eq_getElem _ _ hf] at this
      have h2 := @List.findIdx_getElem _ (· == a) l hf
      simp only [beq_iff_eq] at h2
      exact this h2
    have h2 : ¬ (Instance.firstIndex (fun i => decide (l.getD i d = a)) l.length < l.findIdx (· == a)) := by
      intro hc
      have := List.not_of_lt_findIdx hc
      simp only [beq_eq_false_iff_ne, ne_eq] at this
      exact this hpr
    omega
  · rw [hidx, heq]
    apply List.findIdx_eq_length.mpr
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have := hnone i hi
    simp only [decide_eq_false_iff_not, List.getD_eq_getElem _ _ hi] at this
    simp [this]

/-- `G_ 51 := xNode`, `G_ 52 := yNode`. -/
def xNodeM : Cmd := firstIndexM 1 (G_ 51) NN (isSrcTest (X_ 1) XV (G_ 1) (G_ 2))
def yNodeM : Cmd := firstIndexM 1 (G_ 52) NN (isSrcTest (X_ 1) YV (G_ 1) (G_ 2))

theorem fiV_safe (R : ℕ) (hR : 5 ≤ R ∧ R < IN ∧ R ∉ instVars) : SafeVars (fiV 1 R [G_ 1, G_ 2, FLAG]) :=
  SafeVars.cons hR (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons ⟨by addr3, by addr3, by decide⟩
    (SafeVars.cons ⟨by addr3, by addr3, by decide⟩ (SafeVars.cons safeVars_FLAG (safeVars_of_decide _ (by decide))))))

/-- The first index of `.src M[XY]` among the nodes, as a routine. -/
theorem srcNodeM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) (R XY : ℕ)
    (hR : 5 ≤ R ∧ R < IN ∧ R ∉ instVars) (hRL : R ∉ Lvars 1)
    (hRn : R ∉ [NETS, NETT, NETN, RNGN, REPS, G_ 1, G_ 2, FLAG, NN, IDS, XV, YV])
    (hXY : XY ∈ [XV, YV]) :
    RSpec (firstIndexM 1 R NN (isSrcTest (X_ 1) XY (G_ 1) (G_ 2))) (fiV 1 R [G_ 1, G_ 2, FLAG]) (n * (15 + 9) + 5)
      (NC1 k g) (fun m m' => m' R = g.base.nodes.idxOf (.src (m XY))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hRn
  obtain ⟨hRS, hRT, hRN, hRR, hRP, hRG1, hRG2, hRF, hRNN, hRI, hRX, hRY⟩ := hRn
  have hXYv : XY = XV ∨ XY = YV := by simpa using hXY
  have hXYb : 5 ≤ XY ∧ XY < IN ∧ XY ≠ G_ 1 ∧ XY ≠ G_ 2 ∧ XY ≠ FLAG := by
    rcases hXYv with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have hXYR : XY ≠ R := by rcases hXYv with rfl | rfl <;> [exact Ne.symm hRX; exact Ne.symm hRY]
  have hXYL : XY ∉ Lvars 1 := by rcases hXYv with rfl | rfl <;> decide
  have hsV : SafeVars (fiV 1 R [G_ 1, G_ 2, FLAG]) := fiV_safe R hR
  have ht := (isSrcTest_spec k g (X_ 1) XY (G_ 1) (G_ 2) (safeVars_G 1 (by norm_num)) (safeVars_G 2 (by norm_num))
    (by decide) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide) hXYb (by decide) (by decide)).mono
    (fun x hx => hx) le_rfl (fun m (hm : NC1 k g m ∧ m (X_ 1) < m NN) => hm.1.1.1.1)
  have hfi := firstIndexM_spec 1 R NN n (by norm_num) ht
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> constructor <;> addr3)
    ⟨hR.1, hR.2.1⟩ (by simp; exact ⟨hRG1, hRG2, hRF⟩) hRL hRF hRNN (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (fun m hm => hm.1.1.1.ctx) (fun m hm => by rw [hm.1.1.1.nn]; exact hn.nodes)
    (NC1.stableP hsV (by simp [fiV]; exact ⟨Ne.symm hRI, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
      (by simp [fiV]; exact ⟨Ne.symm hRR, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
      (by simp [fiV]; exact ⟨Ne.symm hRP, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
      (by simp [fiV]; exact ⟨Ne.symm hRS, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
      (by simp [fiV]; exact ⟨Ne.symm hRT, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩)
      (by simp [fiV]; exact ⟨Ne.symm hRN, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩))
    (fun m m' hm hag => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      show decide (g.base.nodes.getD (m' (X_ 1)) (.app 0 []) = .src (m' XY)) =
        decide (g.base.nodes.getD (m (X_ 1)) (.app 0 []) = .src (m XY))
      rw [hag.var (X_ 1) (lt_hp hhp (by decide)) (by decide) (by simp; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | decide | (intro h; exact hRL (by rw [← h]; simp [Lvars]))),
        hag.var XY (lt_hp hhp hXYb.2.1) (by rcases hXYv with rfl | rfl <;> decide)
          (by simp; exact ⟨hXYR, by rcases hXYv with rfl | rfl <;> decide, by rcases hXYv with rfl | rfl <;> decide,
            hXYb.2.2.2.2, hXYb.2.2.1, hXYb.2.2.2.1, hXYb.2.2.2.2⟩)])
  refine hfi.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  rw [hp, idxOf_eq_firstIndex _ _ (.app 0 []), ← hm.1.1.1.nn]
  congr 1
  funext i
  rw [Mem.write_same, Mem.write_ne _ _ (by rcases hXYv with rfl | rfl <;> decide)]

theorem xNodeM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec xNodeM (fiV 1 (G_ 51) [G_ 1, G_ 2, FLAG]) (n * (15 + 9) + 5) (NC1 k g)
      (fun _ m' => NC1 k g m' ∧ m' (G_ 51) = g.xNode) := by
  have h := srcNodeM_spec k g n hn (G_ 51) XV (safeVars_G 51 (by norm_num)) (by decide) (by decide) (by decide)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  refine ⟨NC1.stableP (fiV_safe _ (safeVars_G 51 (by norm_num))) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m m' hm hag, ?_⟩
  rw [hp, hm.1.1.1.x]; rfl

theorem yNodeM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec yNodeM (fiV 1 (G_ 52) [G_ 1, G_ 2, FLAG]) (n * (15 + 9) + 5) (NC1 k g)
      (fun _ m' => NC1 k g m' ∧ m' (G_ 52) = g.yNode) := by
  have h := srcNodeM_spec k g n hn (G_ 52) YV (safeVars_G 52 (by norm_num)) (by decide) (by decide) (by decide)
  refine h.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  refine ⟨NC1.stableP (fiV_safe _ (safeVars_G 52 (by norm_num))) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) m m' hm hag, ?_⟩
  rw [hp, hm.1.1.1.y]; rfl


/-- `(VAL, V2) := (2 ids[X_ 0] + 1, NETT)`. -/
def snkPairM : Cmd :=
  .seq (getDM IDS (X_ 0) (G_ 3)) (.seq (add VAL (G_ 3) (G_ 3)) (.seq (add VAL VAL ONE) (mov V2 NETT)))

theorem snkPairM_spec (k : ℕ) (g : GInstance) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → IdsCtx k g m) :
    FunSpec2 snkPairM [G_ 3, VAL, V2] 9 Pre (fun m => (2 * g.base.canonIds.getD (m (X_ 0)) 0 + 1, m NETT)) := by
  intro m hm
  have hi := hctx m hm
  have hhp : 200 ≤ m HP := hi.1.ctx.2.2
  have hone := hi.1.ctx.1
  obtain ⟨m1, k1, e1, hk1, ag1, hv1, hHP1⟩ := getDM_spec IDS (X_ 0) (G_ 3) (by constructor <;> addr3)
    (by decide) (by decide) (fun m => IdsCtx k g m) (fun m hm => hm.1.ctx) (fun m hm => hm.2.1) m hi
  rw [hi.2.2.2] at hv1
  obtain ⟨v, hv⟩ : ∃ v, v = g.base.canonIds.getD (m (X_ 0)) 0 := ⟨_, rfl⟩
  rw [← hv] at hv1
  have m1one : m1 ONE = 1 := by rw [ag1.var ONE (lt_hp hhp (by decide)) (by decide) (by decide), hone]
  have m1T : m1 NETT = m NETT := ag1.var NETT (lt_hp hhp (by decide)) (by decide) (by decide)
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write VAL (v + v) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add VAL (G_ 3) (G_ 3)) m1 m2 1 := by
    have := Exec.add VAL (G_ 3) (G_ 3) m1; rwa [hv1, ← hm2] at this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m1.write VAL (v + v + 1) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add VAL VAL ONE) m2 m3 1 := by
    have := Exec.add VAL VAL ONE m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr3), m1one, Mem.write_write] at this
    rw [hm3, hm2]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write V2 (m NETT) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (mov V2 NETT) m3 m4 1 := by
    have := Exec.mov V2 NETT m3
    rw [hm3, Mem.write_ne _ _ (by addrn), m1T] at this
    rw [hm4, hm3]; exact this
  have ag3 : Agree m1 m3 [VAL] := by rw [hm3]; exact Agree.write m1 VAL _ (by addr3)
  have ag4 : Agree m3 m4 [V2] := by rw [hm4]; exact Agree.write m3 V2 _ (by addr3)
  refine ⟨m4, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 e4)), by omega, ?_, ?_⟩
  · exact ((ag1.trans ag3).trans ag4).mono (fun x hx => by simp at hx ⊢; tauto)
  · show (m4 VAL, m4 V2) = _
    rw [hm4, Mem.write_ne _ _ (by addr3), Mem.write_same, hm3, Mem.write_same, hv]
    simp only [Prod.mk.injEq, and_true]; omega

/-- `G_ 56 := snkArcsL ids`. -/
def snkArcsM : Cmd :=
  .seq xNodeM (.seq yNodeM (.seq (.seq (arr2M (G_ 51) (G_ 52)) (mov (G_ 53) (OUT_ 0)))
    (.seq (.seq (appendM 0 (G_ 53) OUTS) (mov (G_ 54) (OUT_ 0)))
      (.seq (.seq (mapPairM 0 (G_ 54) snkPairM) (mov (G_ 55) (OUT_ 0)))
            (.seq (dedupM 0 (G_ 55)) (mov (G_ 56) (OUT_ 0)))))))

def snkArcsV : List ℕ :=
  fiV 1 (G_ 51) [G_ 1, G_ 2, FLAG] ++ (fiV 1 (G_ 52) [G_ 1, G_ 2, FLAG] ++ ((Lvars 0 ++ [G_ 53]) ++
    ((Lvars 0 ++ [G_ 54]) ++ ((Lvars 0 ++ [G_ 3, VAL, V2] ++ [G_ 55]) ++ (dedupV 0 ++ [G_ 56])))))

theorem snkArcsV_safe : SafeVars snkArcsV :=
  SafeVars.append (fiV_safe _ (safeVars_G 51 (by norm_num))) (SafeVars.append (fiV_safe _ (safeVars_G 52 (by norm_num)))
    (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
      (safeVars_of_decide _ (by decide))) (SafeVars.append dedupV0_safe (safeVars_of_decide _ (by decide)))))))

theorem snkArcsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec snkArcsM snkArcsV
      ((n * (15 + 9) + 5) + ((n * (15 + 9) + 5) + ((8 + 1) + ((2 * (n + 2) * 12 + 15 + 1) +
        ((n + 2) * (9 + 14) + 9 + 1 + (23 * (n + 2) * (n + 2) + 23 * (n + 2) + 8 + 1))))))
      (NC1 k g) (fun _ m' => NC1 k g m' ∧ PArrIs m' (G_ 56) (g.snkArcsL g.base.canonIds)) := by
  have hs0 : SafeVars (Lvars 0) := safeVars_Lvars 0 (by norm_num)
  -- the two source nodes
  have s1 := xNodeM_spec k g n hn
  let P1 : Mem → Prop := fun m => NC1 k g m ∧ m (G_ 51) = g.xNode
  have hP1 : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V → NETN ∉ V →
      G_ 51 ∉ V → StableP P1 V := fun hV h1 h2 h3 h4 h5 h6 h51 m m' hm hag =>
    ⟨NC1.stableP hV h1 h2 h3 h4 h5 h6 m m' hm.1 hag, by
      rw [hag.var (G_ 51) (lt_hp hm.1.1.1.1.ctx.2.2 (by decide)) (by decide) h51]; exact hm.2⟩
  have s2 := ((yNodeM_spec k g n hn).mono' (Pre' := P1) (Post' := fun _ m' => m' (G_ 52) = g.yNode)
    (fun x hx => hx) le_rfl (fun m hm => hm.1) (fun m m' hm hag hp => hp.2)).carry
    (hP1 (fiV_safe _ (safeVars_G 52 (by norm_num))) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  -- [xNode, yNode]
  let P2 : Mem → Prop := fun m => P1 m ∧ m (G_ 52) = g.yNode
  have hP2 : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V → NETN ∉ V →
      G_ 51 ∉ V → G_ 52 ∉ V → StableP P2 V := fun hV h1 h2 h3 h4 h5 h6 h51 h52 m m' hm hag =>
    ⟨hP1 hV h1 h2 h3 h4 h5 h6 h51 m m' hm.1 hag, by
      rw [hag.var (G_ 52) (lt_hp hm.1.1.1.1.1.ctx.2.2 (by decide)) (by decide) h52]; exact hm.2⟩
  have hs53 : SafeVars (Lvars 0 ++ [G_ 53]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have s3 := ((RSpec.seq_mov 0 (G_ 53) (by constructor <;> addr3)
    (arr2M_spec (G_ 51) (G_ 52) (by constructor <;> addr3) (by constructor <;> addr3) (by decide) (by decide) P2
      (fun m hm => hm.1.1.1.1.1.ctx))
    (fun m m' v hm hr => ⟨by rw [arrAt_write_lo _ _ _ _ (by addr3) hm.1.1.1.1.1.ctx.2.2]; exact hr.1,
      by rw [Mem.write_ne _ _ (by addr3)]; exact hr.2⟩)).mono'
    (Post' := fun _ m' => ArrIs m' (G_ 53) [g.xNode, g.yNode]) (fun x hx => hx) le_rfl (fun m hm => hm)
    (fun m m' hm hag hp => by
      obtain ⟨hP', harr, hroom⟩ := hp
      exact ArrIs.of_out hm.1.1.1.1.1.ctx.2.2 hP' (by rw [harr, hm.1.2, hm.2]) hroom)).carry
    (hP2 hs53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- outNodes
  let P3 : Mem → Prop := fun m => P2 m ∧ ArrIs m (G_ 53) [g.xNode, g.yNode]
  have hs54 : SafeVars (Lvars 0 ++ [G_ 54]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have s4 := (appendM_arr_spec 0 (G_ 53) OUTS (G_ 54) (n + 2) _ _ (by norm_num) (by constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addr3) P3
    (fun m hm => hm.1.1.1.1.1.1.ctx) (fun m hm => hm.2)
    (fun m hm => ⟨hm.1.1.1.1.1.1.arr_outs.1, hm.1.1.1.1.1.1.arr_outs.2.1, hm.1.1.1.1.1.1.arr_outs.2.2⟩)
    ⟨by simp, by have := hn.outs; omega⟩).carry
    ((hP2 hs54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (ArrIs.stableP (P := G_ 53) (fun x hx => (hs54 x hx).2.1) (by addr3) (by addr3) (by decide)))
  -- the pairs
  let P4 : Mem → Prop := fun m => P3 m ∧ ArrIs m (G_ 54) ([g.xNode, g.yNode] ++ g.outs)
  have hs55 : SafeVars (Lvars 0 ++ [G_ 3, VAL, V2]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have hs55' : SafeVars (Lvars 0 ++ [G_ 3, VAL, V2] ++ [G_ 55]) := SafeVars.append hs55 (safeVars_of_decide _ (by decide))
  have hP4 : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V → NETN ∉ V →
      G_ 51 ∉ V → G_ 52 ∉ V → G_ 53 ∉ V → G_ 54 ∉ V → StableP P4 V :=
    fun hV h1 h2 h3 h4 h5 h6 h51 h52 h53 h54 =>
      ((hP2 hV h1 h2 h3 h4 h5 h6 h51 h52).and
        (ArrIs.stableP (P := G_ 53) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h53)).and
        (ArrIs.stableP (P := G_ 54) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h54)
  have s5 := (mapPairM_parr_spec 0 (G_ 54) (G_ 55) (n + 2) _ (fun j => (2 * g.base.canonIds.getD j 0 + 1, g.netT))
    (snkPairM_spec k g (fun m => P4 m ∧ m (X_ 0) ∈ arrAt m (m (G_ 54))) (fun m hm => hm.1.1.1.1.1.1.1))
    (by norm_num) (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by constructor <;> addr3)
    (fun m hm => hm.1.1.1.1.1.1.1.ctx) (fun m hm => hm.2) (by simp; have := hn.outs; omega)
    (hP4 hs55 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.1.1.ctx.2.2
      show (2 * g.base.canonIds.getD (m' (X_ 0)) 0 + 1, m' NETT) = (2 * g.base.canonIds.getD (m (X_ 0)) 0 + 1, m NETT)
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var NETT (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x hm _ => by rw [Mem.write_same, Mem.write_ne _ _ (by addrn), hm.1.1.1.1.2.2.1])).carry
    (hP4 hs55' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- dedup
  let P5 : Mem → Prop := fun m => P4 m ∧ PArrIs m (G_ 55)
    (([g.xNode, g.yNode] ++ g.outs).map (fun j => (2 * g.base.canonIds.getD j 0 + 1, g.netT)))
  have hs56 : SafeVars (dedupV 0 ++ [G_ 56]) := SafeVars.append dedupV0_safe (safeVars_of_decide _ (by decide))
  have s6 := (dedupM_parr_spec 0 (G_ 55) (G_ 56) (n + 2) _ (by norm_num) (by constructor <;> addr3) (by decide)
    (by constructor <;> addr3) (by decide) P5 (fun m hm => hm.1.1.1.1.1.1.1.1.ctx) (fun m hm => hm.2)
    (by simp; have := hn.outs; omega)).carry
    ((hP4 hs56 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (PArrIs.stableP (P := G_ 55) (fun x hx => (hs56 x hx).2.1) (by addr3) (by addr3) (by decide)))
  have hall := s1.seqP (s2.seqP (s3.seqP (s4.seqP (s5.seqP s6))))
  unfold snkArcsM snkArcsV
  refine hall.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  exact ⟨hp.1.1.1.1.1.1, hp.2⟩


/-! ### The arc list and the whole network -/

theorem RSpec.carryFact {c : Cmd} {V : List ℕ} {B : ℕ} {Pre Q F : Mem → Prop}
    (h : RSpec c V B Pre (fun _ m' => Q m')) (hstab : StableP F V) :
    RSpec c V B (fun m => Pre m ∧ F m) (fun _ m' => Q m' ∧ F m') :=
  h.mono' (fun x hx => hx) le_rfl (fun m hm => hm.1) (fun m m' hm hag hq => ⟨hq, hstab m m' hm.2 hag⟩)

/-- `ARCS := nodeArcs ++ edgeArcs ++ srcArcs ++ snkArcs`. -/
def arcsM : Cmd :=
  .seq (.seq (appendM 0 (G_ 44) (G_ 47)) (mov (G_ 57) (OUT_ 0)))
  (.seq (.seq (appendM 0 (G_ 57) (G_ 50)) (mov (G_ 58) (OUT_ 0)))
        (.seq (appendM 0 (G_ 58) (G_ 56)) (mov ARCS (OUT_ 0))))

def arcsV : List ℕ := (Lvars 0 ++ [G_ 57]) ++ ((Lvars 0 ++ [G_ 58]) ++ (Lvars 0 ++ [ARCS]))

theorem arcsV_safe : SafeVars arcsV :=
  SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
      (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide))))

/-- The context after the network is built. -/
def NetCtx (k : ℕ) (g : GInstance) (m : Mem) : Prop :=
  NC1 k g m ∧ PArrIs m ARCS (g.networkL g.base.canonIds).arcs

theorem NetCtx.stableP {k : ℕ} {g : GInstance} {V : List ℕ} (hV : SafeVars V) (hI : IDS ∉ V) (hR : RNGN ∉ V)
    (hP : REPS ∉ V) (hS : NETS ∉ V) (hT : NETT ∉ V) (hN : NETN ∉ V) (hA : ARCS ∉ V) : StableP (NetCtx k g) V :=
  (NC1.stableP hV hI hR hP hS hT hN).and
    (PArrIs.stableP (P := ARCS) (fun x hx => (hV x hx).2.1) (by addrn) (by addrn) hA)

theorem nodeArcsL_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) : (g.nodeArcsL g.base.canonIds).length ≤ n := by
  unfold GInstance.nodeArcsL; rw [List.length_map]; exact le_trans (repsL_length_le g _) hn.nodes

theorem dedupList_length_le' {α : Type} [DecidableEq α] (l : List α) : (dedupList l).length ≤ l.length :=
  dedupList_length_le l

theorem edgeArcsL_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) : (g.edgeArcsL g.base.canonIds).length ≤ n * n := by
  rw [edgeArcsL_eq]; exact le_trans (dedupList_length_le' _) (edgeFlat_length_le hn)

theorem srcArcsL_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) : (g.srcArcsL g.base.canonIds).length ≤ n := by
  unfold GInstance.srcArcsL
  refine le_trans (dedupList_length_le' _) ?_
  rw [List.length_map]
  exact le_trans (List.length_filter_le _ _) (by rw [List.length_range]; exact hn.nodes)

theorem snkArcsL_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) : (g.snkArcsL g.base.canonIds).length ≤ n + 2 := by
  unfold GInstance.snkArcsL
  refine le_trans (dedupList_length_le' _) ?_
  rw [List.length_map]
  unfold GInstance.outNodes
  simp only [List.length_append, List.length_cons, List.length_nil]
  have := hn.outs; omega

theorem arcsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec arcsM arcsV (3 * (2 * (n * n + 2 * n + 2) * 12 + 15 + 1))
      (fun m => NC1 k g m ∧ PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds) ∧
        PArrIs m (G_ 47) (g.edgeArcsL g.base.canonIds) ∧ PArrIs m (G_ 50) (g.srcArcsL g.base.canonIds) ∧
        PArrIs m (G_ 56) (g.snkArcsL g.base.canonIds))
      (fun _ m' => NetCtx k g m') := by
  have hs0 : SafeVars (Lvars 0) := safeVars_Lvars 0 (by norm_num)
  have hs57 : SafeVars (Lvars 0 ++ [G_ 57]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have hs58 : SafeVars (Lvars 0 ++ [G_ 58]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have hsA : SafeVars (Lvars 0 ++ [ARCS]) := SafeVars.append hs0 (safeVars_of_decide _ (by decide))
  have hN : n * n + 2 * n + 2 ≥ n := by nlinarith
  let P0 : Mem → Prop := fun m => NC1 k g m ∧ PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds) ∧
    PArrIs m (G_ 47) (g.edgeArcsL g.base.canonIds) ∧ PArrIs m (G_ 50) (g.srcArcsL g.base.canonIds) ∧
    PArrIs m (G_ 56) (g.snkArcsL g.base.canonIds)
  have hP0 : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V → NETN ∉ V →
      G_ 44 ∉ V → G_ 47 ∉ V → G_ 50 ∉ V → G_ 56 ∉ V → StableP P0 V :=
    fun hV h1 h2 h3 h4 h5 h6 h44 h47 h50 h56 =>
      (NC1.stableP hV h1 h2 h3 h4 h5 h6).and ((PArrIs.stableP (P := G_ 44) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h44).and
        ((PArrIs.stableP (P := G_ 47) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h47).and
        ((PArrIs.stableP (P := G_ 50) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h50).and
        (PArrIs.stableP (P := G_ 56) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h56))))
  have s1 := (appendM_parr_spec 0 (G_ 44) (G_ 47) (G_ 57) (n * n + 2 * n + 2) _ _ (by norm_num)
    (by constructor <;> addr3) (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addr3) P0
    (fun m hm => hm.1.1.1.1.ctx) (fun m hm => hm.2.1) (fun m hm => hm.2.2.1)
    ⟨le_trans (nodeArcsL_length_le hn) hN, le_trans (edgeArcsL_length_le hn) (by omega)⟩).carry
    (hP0 hs57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  let P1 : Mem → Prop := fun m => P0 m ∧ PArrIs m (G_ 57) (g.nodeArcsL g.base.canonIds ++ g.edgeArcsL g.base.canonIds)
  have s2 := (appendM_parr_spec 0 (G_ 57) (G_ 50) (G_ 58) (n * n + 2 * n + 2) _ _ (by norm_num)
    (by constructor <;> addr3) (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addr3) P1
    (fun m hm => hm.1.1.1.1.1.ctx) (fun m hm => hm.2) (fun m hm => hm.1.2.2.2.1)
    ⟨by rw [List.length_append]; have := nodeArcsL_length_le hn; have := edgeArcsL_length_le hn; omega,
      le_trans (srcArcsL_length_le hn) hN⟩).carry
    ((hP0 hs58 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (PArrIs.stableP (P := G_ 57) (fun x hx => (hs58 x hx).2.1) (by addr3) (by addr3) (by decide)))
  let P2 : Mem → Prop := fun m => P1 m ∧
    PArrIs m (G_ 58) (g.nodeArcsL g.base.canonIds ++ g.edgeArcsL g.base.canonIds ++ g.srcArcsL g.base.canonIds)
  have s3 := (appendM_parr_spec 0 (G_ 58) (G_ 56) ARCS (n * n + 2 * n + 2) _ _ (by norm_num)
    (by constructor <;> addr3) (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addrn) P2
    (fun m hm => hm.1.1.1.1.1.1.ctx) (fun m hm => hm.2) (fun m hm => hm.1.1.2.2.2.2)
    ⟨by simp only [List.length_append]; have := nodeArcsL_length_le hn; have := edgeArcsL_length_le hn;
        have := srcArcsL_length_le hn; omega,
      le_trans (snkArcsL_length_le hn) (by omega)⟩).carry
    (((hP0 hsA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
      (PArrIs.stableP (P := G_ 57) (fun x hx => (hsA x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (PArrIs.stableP (P := G_ 58) (fun x hx => (hsA x hx).2.1) (by addr3) (by addr3) (by decide)))
  have hall := s1.seqP (s2.seqP s3)
  unfold arcsM arcsV
  refine hall.mono' (fun x hx => hx) (by omega) (fun m hm => hm) (fun m m' hm hag hp => ?_)
  exact ⟨hp.1.1.1.1, hp.2⟩

/-- The whole network construction. -/
def netM : Cmd :=
  .seq rangeNM (.seq repsM (.seq netNodesM (.seq nodeArcsM (.seq edgeArcsM (.seq srcArcsM (.seq snkArcsM arcsM))))))

def netV : List ℕ :=
  (Lvars 0 ++ [RNGN]) ++ (repsV ++ (netNodesV ++ (nodeArcsV ++ (edgeArcsV ++ (srcArcsV ++ (snkArcsV ++ arcsV))))))

theorem netV_safe : SafeVars netV :=
  SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (safeVars_of_decide _ (by decide)))
      (safeVars_of_decide _ (by decide)))
    (SafeVars.append netNodesV_safe (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num))
      (safeVars_of_decide _ (by decide))) (safeVars_of_decide _ (by decide)))
    (SafeVars.append edgeArcsV_safe (SafeVars.append srcArcsV_safe (SafeVars.append snkArcsV_safe arcsV_safe))))))

/-- The step bound of the network construction. -/
def netB (n : ℕ) : ℕ :=
  (n * 6 + 8 + 1) + ((n * (9 + 14) + 9 + 1) +
  (((n * (1 + 9) + 9 + 1) + ((n * (2 + 9) + 9 + 1) + ((2 * n * 12 + 15 + 1) + (2 + ((8 + 1) + (2 * (2 * n + 2) * 12 + 15 + 1)))))) +
  ((n * (2 + 14) + 9 + 1) +
  (((n * ((9 + (n * (15 + 14) + 9) + 1) + 9) + 9 + 1) + ((12 * n * n + 18 * n + 13 + 1) +
        (23 * (n * n) * (n * n) + 23 * (n * n) + 8 + 1))) +
  (((n * (7 + 14) + 9 + 1) + ((n * (8 + 14) + 9 + 1) + (23 * n * n + 23 * n + 8 + 1))) +
  (((n * (15 + 9) + 5) + ((n * (15 + 9) + 5) + ((8 + 1) + ((2 * (n + 2) * 12 + 15 + 1) +
        ((n + 2) * (9 + 14) + 9 + 1 + (23 * (n + 2) * (n + 2) + 23 * (n + 2) + 8 + 1)))))) +
  (3 * (2 * (n * n + 2 * n + 2) * 12 + 15 + 1))))))))

theorem netM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec netM netV (netB n) (IdsCtx k g) (fun _ m' => NetCtx k g m') := by
  have s1 := rangeNM_spec k g n hn
  have s2 := repsM_spec k g n hn
  have s3 := (netNodesM_spec k g n hn).mono' (Pre' := fun m => (IdsCtx k g m ∧ ArrIs m RNGN (List.range g.base.nodes.length)) ∧
      ArrIs m REPS (g.repsL g.base.canonIds)) (Post' := fun _ m' => NC1 k g m')
    (fun x hx => hx) le_rfl (fun m hm => ⟨hm.1.1, hm.1.2, hm.2⟩) (fun _ _ _ _ hp => hp)
  have s4 := nodeArcsM_spec k g n hn
  have s5 := (edgeArcsM_spec k g n hn).carryFact (F := fun m => PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds))
    (PArrIs.stableP (P := G_ 44) (fun x hx => (edgeArcsV_safe x hx).2.1) (by addr3) (by addr3) (by decide))
  have s6 := ((srcArcsM_spec k g n hn).carryFact (F := fun m => PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds) ∧
      PArrIs m (G_ 47) (g.edgeArcsL g.base.canonIds))
    ((PArrIs.stableP (P := G_ 44) (fun x hx => (srcArcsV_safe x hx).2.1) (by addr3) (by addr3) (by decide)).and
      (PArrIs.stableP (P := G_ 47) (fun x hx => (srcArcsV_safe x hx).2.1) (by addr3) (by addr3) (by decide)))).mono'
    (Pre' := fun m => (NC1 k g m ∧ PArrIs m (G_ 47) (g.edgeArcsL g.base.canonIds)) ∧ PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds))
    (Post' := fun _ m' => (NC1 k g m' ∧ PArrIs m' (G_ 50) (g.srcArcsL g.base.canonIds)) ∧
      (PArrIs m' (G_ 44) (g.nodeArcsL g.base.canonIds) ∧ PArrIs m' (G_ 47) (g.edgeArcsL g.base.canonIds)))
    (fun x hx => hx) le_rfl (fun m hm => ⟨hm.1.1, hm.2, hm.1.2⟩) (fun _ _ _ _ hp => hp)
  have s7 := ((snkArcsM_spec k g n hn).carryFact (F := fun m => (PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds) ∧
      PArrIs m (G_ 47) (g.edgeArcsL g.base.canonIds)) ∧ PArrIs m (G_ 50) (g.srcArcsL g.base.canonIds))
    (((PArrIs.stableP (P := G_ 44) (fun x hx => (snkArcsV_safe x hx).2.1) (by addr3) (by addr3) (by decide)).and
      (PArrIs.stableP (P := G_ 47) (fun x hx => (snkArcsV_safe x hx).2.1) (by addr3) (by addr3) (by decide))).and
      (PArrIs.stableP (P := G_ 50) (fun x hx => (snkArcsV_safe x hx).2.1) (by addr3) (by addr3) (by decide)))).mono'
    (Pre' := fun m => (NC1 k g m ∧ PArrIs m (G_ 50) (g.srcArcsL g.base.canonIds)) ∧
      (PArrIs m (G_ 44) (g.nodeArcsL g.base.canonIds) ∧ PArrIs m (G_ 47) (g.edgeArcsL g.base.canonIds)))
    (Post' := fun _ m' => NC1 k g m' ∧ PArrIs m' (G_ 44) (g.nodeArcsL g.base.canonIds) ∧
      PArrIs m' (G_ 47) (g.edgeArcsL g.base.canonIds) ∧ PArrIs m' (G_ 50) (g.srcArcsL g.base.canonIds) ∧
      PArrIs m' (G_ 56) (g.snkArcsL g.base.canonIds))
    (fun x hx => hx) le_rfl (fun m hm => ⟨hm.1.1, ⟨hm.2.1, hm.2.2⟩, hm.1.2⟩)
    (fun _ _ _ _ hp => ⟨hp.1.1, hp.2.1.1, hp.2.1.2, hp.2.2, hp.1.2⟩)
  have s8 := arcsM_spec k g n hn
  have hall := s1.seqP (s2.seqP (s3.seqP (s4.seqP (s5.seqP (s6.seqP (s7.seqP s8))))))
  unfold netM netV netB
  exact hall.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun _ _ _ _ hp => hp)

end DisequalityDispersion.Machine
