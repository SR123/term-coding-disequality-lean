import MLib

/-! # Array routines, part 2: append, flatten, reverse iteration, deduplication -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Pushing a variable -/

/-- Append `M[Y]` to the array whose header address is in `OUT_ L`. -/
def pushV (L Y : ℕ) : Cmd :=
  .seq (load (CONT_ L) (OUT_ L)) (.seq (add (PTR_ L) (OUT_ L) (CONT_ L))
    (.seq (add (PTR_ L) (PTR_ L) ONE) (.seq (store (PTR_ L) Y)
      (.seq (add (CONT_ L) (CONT_ L) ONE) (store (OUT_ L) (CONT_ L))))))

theorem pushV_spec (L Y : ℕ) (hL : L ≤ 9) (hY : Y < IN) (hYC : Y ≠ CONT_ L) (hYP : Y ≠ PTR_ L)
    (m : Mem) (hdr : ℕ) (hout : m (OUT_ L) = hdr) (hone : m ONE = 1) (hhdr : IN ≤ hdr) :
    ∃ m' k, Cmd.Exec (pushV L Y) m m' k ∧ k ≤ 6 ∧
      (∀ x, x ≠ CONT_ L → x ≠ PTR_ L → x ≠ hdr → x ≠ hdr + 1 + m hdr → m' x = m x) ∧
      m' hdr = m hdr + 1 ∧ m' (hdr + 1 + m hdr) = m Y := by
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
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (hdr + 1 + m hdr) (m Y) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (store (PTR_ L) Y) m3 m4 1 := by
    have := Exec.store (PTR_ L) Y m3
    rw [hm3, Mem.write_same, Mem.write_ne _ _ hYP, hm1, Mem.write_ne _ _ hYC] at this
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

/-! ### Prepending into a buffer filled from the top -/

theorem arrAt_prepend {m m' : Mem} {hdr v : ℕ} (h0 : 1 ≤ hdr) (h1 : m' (hdr - 1) = m hdr + 1)
    (h2 : m' hdr = v) (h3 : ∀ i, i < m hdr → m' (hdr + 1 + i) = m (hdr + 1 + i)) :
    arrAt m' (hdr - 1) = v :: arrAt m hdr := by
  unfold arrAt
  rw [h1, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [show hdr - 1 + 1 + 0 = hdr by omega, h2]
  · apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp]
    rw [show hdr - 1 + 1 + (i + 1) = hdr + 1 + i by omega, h3 i hi]

/-- Prepend `M[Y]` to the array whose header address is in `OUT_ L`; the header moves one
cell down. -/
def prependV (L Y : ℕ) : Cmd :=
  .seq (load (CONT_ L) (OUT_ L)) (.seq (store (OUT_ L) Y) (.seq (sub (OUT_ L) (OUT_ L) ONE)
    (.seq (add (CONT_ L) (CONT_ L) ONE) (store (OUT_ L) (CONT_ L)))))

theorem prependV_spec (L Y : ℕ) (hL : L ≤ 9) (hY : Y < IN) (hYC : Y ≠ CONT_ L) (hYO : Y ≠ OUT_ L)
    (m : Mem) (hdr : ℕ) (hout : m (OUT_ L) = hdr) (hone : m ONE = 1) (hhdr : IN < hdr) :
    ∃ m' k, Cmd.Exec (prependV L Y) m m' k ∧ k ≤ 5 ∧
      (∀ x, x ≠ CONT_ L → x ≠ OUT_ L → x ≠ hdr → x ≠ hdr - 1 → m' x = m x) ∧
      m' (OUT_ L) = hdr - 1 ∧ m' (hdr - 1) = m hdr + 1 ∧ m' hdr = m Y := by
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write (CONT_ L) (m hdr) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load (CONT_ L) (OUT_ L)) m m1 1 := by
    have := Exec.load (CONT_ L) (OUT_ L) m; rwa [hout, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write hdr (m Y) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (store (OUT_ L) Y) m1 m2 1 := by
    have := Exec.store (OUT_ L) Y m1
    rw [hm1, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ hYC, hout] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (OUT_ L) (hdr - 1) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (sub (OUT_ L) (OUT_ L) ONE) m2 m3 1 := by
    have := Exec.sub (OUT_ L) (OUT_ L) ONE m2
    rw [hm2, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm1,
      Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout, hone] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (CONT_ L) (m hdr + 1) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add (CONT_ L) (CONT_ L) ONE) m3 m4 1 := by
    have := Exec.add (CONT_ L) (CONT_ L) ONE m3
    rw [hm3, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm1, Mem.write_same,
      Mem.write_ne _ _ (by addr'), hone] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (hdr - 1) (m hdr + 1) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (store (OUT_ L) (CONT_ L)) m4 m5 1 := by
    have := Exec.store (OUT_ L) (CONT_ L) m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same] at this
    rw [hm5, hm4, hm3]; exact this
  refine ⟨m5, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e5))),
    by omega, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2 h3 h4
    rw [hm5, Mem.write_ne _ _ h4, hm4, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h2, hm2,
      Mem.write_ne _ _ h3, hm1, Mem.write_ne _ _ h1]
  · rw [hm5, Mem.write_ne _ _ (by addr'), hm4, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
  · rw [hm5, Mem.write_same]
  · rw [hm5, Mem.write_ne _ _ (by omega), hm4, Mem.write_ne _ _ (by addr'), hm3,
      Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]


/-! ### Iteration in reverse order -/

/-- `for X in (array at SRC).reverse do body`: iteration `j` sees element `n - 1 - j`. -/
def forEachRevM (L SRC : ℕ) (body : Cmd) : Cmd :=
  .seq (load (CNT_ L) SRC) (.seq (setc (I_ L) 0)
    (forLoop (I_ L) (CNT_ L) (.seq (add (PTR_ L) SRC (CNT_ L)) (.seq (sub (PTR_ L) (PTR_ L) (I_ L))
      (.seq (load (X_ L) (PTR_ L)) body)))))

theorem forEachRevM_spec (L SRC : ℕ) (hL : L ≤ 9) (hSRC : SRC < IN) (hSL : SRC ∉ Lvars L)
    (body : Cmd) (Inv : ℕ → Mem → Prop) (a : ℕ) (ha : IN ≤ a) (l : List ℕ) (B : ℕ)
    (hI : ∀ j m, Inv j m → m (I_ L) = j ∧ m (CNT_ L) = l.length ∧ m SRC = a ∧ m ONE = 1 ∧
      a + 1 + l.length ≤ m HP ∧ (∀ i, (h : i < l.length) → m (a + 1 + i) = l[i]))
    (hstable : ∀ j m v w, Inv j m → Inv j ((m.write (PTR_ L) v).write (X_ L) w))
    (hbody : ∀ j m, (h : j < l.length) → Inv j m → m (X_ L) = l[l.length - 1 - j] →
      m (PTR_ L) = a + l.length - j →
      ∃ m' k, Cmd.Exec body m m' k ∧ k ≤ B ∧ m' (I_ L) = j ∧ m' ONE = 1 ∧
        Inv (j + 1) (m'.write (I_ L) (j + 1))) :
    ∀ m, m SRC = a → m a = l.length → Inv 0 ((m.write (CNT_ L) l.length).write (I_ L) 0) →
      ∃ m' k, Cmd.Exec (forEachRevM L SRC body) m m' k ∧ Inv l.length m' ∧
        k ≤ l.length * (B + 6) + 4 := by
  intro m hsrc hlen hinv
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write (CNT_ L) l.length := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load (CNT_ L) SRC) m m1 1 := by
    have := Exec.load (CNT_ L) SRC m; rwa [hsrc, hlen, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (I_ L) 0 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (setc (I_ L) 0) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
  rw [← hm1, ← hm2] at hinv
  have main := forLoop_spec (I_ L) (CNT_ L)
    (.seq (add (PTR_ L) SRC (CNT_ L)) (.seq (sub (PTR_ L) (PTR_ L) (I_ L)) (.seq (load (X_ L) (PTR_ L)) body)))
    Inv l.length (B + 3) (fun j m hm => ⟨(hI j m hm).1, (hI j m hm).2.1⟩) ?_ 0 m2 (Nat.zero_le _) hinv
  · obtain ⟨m', k, e, hinv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e), hinv', ?_⟩
    have : (l.length - 0) * (B + 3 + 3) = l.length * (B + 6) := by simp
    omega
  · intro j m hj hm
    obtain ⟨hI1, hI2, hI3, hI4, hI5, hI6⟩ := hI j m hm
    have hSP : SRC ≠ PTR_ L := fun h => hSL (by rw [h]; simp [Lvars])
    obtain ⟨n1, hn1⟩ : ∃ n1, n1 = m.write (PTR_ L) (a + l.length) := ⟨_, rfl⟩
    have f1 : Cmd.Exec (add (PTR_ L) SRC (CNT_ L)) m n1 1 := by
      have := Exec.add (PTR_ L) SRC (CNT_ L) m; rwa [hI3, hI2, ← hn1] at this
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = m.write (PTR_ L) (a + l.length - j) := ⟨_, rfl⟩
    have f2 : Cmd.Exec (sub (PTR_ L) (PTR_ L) (I_ L)) n1 n2 1 := by
      have := Exec.sub (PTR_ L) (PTR_ L) (I_ L) n1
      rw [hn1, Mem.write_same, Mem.write_ne _ _ (by addr'), hI1, Mem.write_write] at this
      rw [hn2, hn1]; exact this
    have hidx : a + l.length - j = a + 1 + (l.length - 1 - j) := by omega
    obtain ⟨n3, hn3⟩ : ∃ n3, n3 = n2.write (X_ L) (l[l.length - 1 - j]'(by omega)) := ⟨_, rfl⟩
    have f3 : Cmd.Exec (load (X_ L) (PTR_ L)) n2 n3 1 := by
      have := Exec.load (X_ L) (PTR_ L) n2
      rw [hn2, Mem.write_same, hidx, Mem.write_ne _ _ (by addr'), hI6 _ (by omega)] at this
      rw [hn3, hn2, hidx]; exact this
    have inv3 : Inv j n3 := by rw [hn3, hn2]; exact hstable j m _ _ hm
    obtain ⟨m', k, e, hk, hi', hone', hinv'⟩ := hbody j n3 hj inv3 (by rw [hn3, Mem.write_same])
      (by rw [hn3, Mem.write_ne _ _ (by addr'), hn2, Mem.write_same])
    exact ⟨m', _, Cmd.Exec.seq f1 (Cmd.Exec.seq f2 (Cmd.Exec.seq f3 e)), by omega, hi', hone', hinv'⟩

/-! ### `append` -/

/-- The concatenation of the arrays at `A` and `B`, as a fresh array (address in `OUT_ L`). -/
def appendM (L A B : ℕ) : Cmd :=
  .seq (mov (OUT_ L) HP) (.seq (store (OUT_ L) ZERO) (.seq (load (CNT_ L) A) (.seq (load (CONT_ L) B)
    (.seq (add (CNT_ L) (CNT_ L) (CONT_ L)) (.seq (add HP HP (CNT_ L)) (.seq (add HP HP ONE)
      (.seq (forEachM L A (pushM L)) (forEachM L B (pushM L)))))))))

/-- The invariant of the copying loops of `appendM`: `pre ++ l.take j` has been pushed. -/
structure AppInv (L : ℕ) (m0 : Mem) (hdr a : ℕ) (pre l : List ℕ) (tot : ℕ) (j : ℕ) (m : Mem) :
    Prop where
  agree : Agree m0 m (Lvars L)
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = hdr
  arr : arrAt m hdr = pre ++ l.take j
  room : hdr + 1 + tot ≤ m HP
  src : m ONE = 1 ∧ a + 1 + l.length ≤ m HP ∧ (∀ i, (h : i < l.length) → m (a + 1 + i) = l[i])

/-- One copying pass: pushes every element of the array at `A` (address `a`, contents `l`). -/
theorem appendM_pass (L A : ℕ) (hL : L ≤ 9) (hA : 5 ≤ A ∧ A < IN) (hAL : A ∉ Lvars L)
    (m0 : Mem) (hdr a : ℕ) (pre l : List ℕ) (tot : ℕ) (hhdr : IN ≤ hdr) (ha : IN ≤ a)
    (hhdr0 : m0 HP ≤ hdr) (hsrc0 : a + 1 + l.length ≤ m0 HP)
    (hpre : pre.length + l.length ≤ tot) (hsrcA : ∀ m, Agree m0 m (Lvars L) → m A = a) :
    ∀ m, AppInv L m0 hdr a pre l tot 0 ((m.write (CNT_ L) l.length).write (I_ L) 0) → m A = a →
      m a = l.length →
      ∃ m' k, Cmd.Exec (forEachM L A (pushM L)) m m' k ∧ AppInv L m0 hdr a pre l tot l.length m' ∧
        k ≤ l.length * 12 + 4 := by
  intro m hinv hmA hma
  have hAP : A ≠ PTR_ L := fun h => hAL (by rw [h]; simp [Lvars])
  have hAX : A ≠ X_ L := fun h => hAL (by rw [h]; simp [Lvars])
  refine forEachM_spec L A hL hA.2 hAL (pushM L) (AppInv L m0 hdr a pre l tot) a ha l 6 ?_ ?_ ?_ m hmA hma hinv
  · intro j m hm
    obtain ⟨hag, hi, hcnt, hout, harr, hroom, hone, hsz, hcells⟩ := hm
    exact ⟨hi, hcnt, hsrcA m hag, hone, hsz, hcells⟩
  · intro j m v w hm
    obtain ⟨hag, hi, hcnt, hout, harr, hroom, hone, hsz, hcells⟩ := hm
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    have hw : ∀ x, IN ≤ x → ((m.write (PTR_ L) v).write (X_ L) w) x = m x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp [Lvars]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout]
    · rw [← harr]; exact arrAt_congr (fun x h1 h2 => hw x (by omega))
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hone]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hsz
    · intro i hi'; rw [hw _ (by omega), hcells i hi']
  · intro j m hj hm hx _
    obtain ⟨hag, hi, hcnt, hout, harr, hroom, hone, hsz, hcells⟩ := hm
    have hlen : m hdr = pre.length + j := by
      have h := congrArg List.length harr
      rw [arrAt_length, List.length_append, List.length_take, min_eq_left (by omega)] at h
      exact h
    obtain ⟨m', k, e, hk, fr, hhdr', hcell⟩ := pushM_spec L hL m hdr hout hone hhdr
    have m'I : m' (I_ L) = j := by rw [fr _ (by addr') (by addr') (by addr') (by addr'), hi]
    have m'one : m' ONE = 1 := by rw [fr _ (by addr') (by addr') (by addr') (by addr'), hone]
    refine ⟨m', k, e, hk, m'I, m'one, ?_⟩
    have hw : ∀ x, IN ≤ x → (m'.write (I_ L) (j + 1)) x = m' x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr')]
    refine ⟨?_, by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1, fr y hyV'.2.2.2.2.1 hyV'.2.2.2.1 (by omega) (by omega)]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), fr HP (by addr') (by addr') (by addr') (by addr')]
        exact hag.2
    · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hout]
    · have h1 : arrAt (m'.write (I_ L) (j + 1)) hdr = arrAt m' hdr :=
        arrAt_congr (fun x h1 h2 => hw x (by omega))
      rw [h1, List.take_succ_eq_append_getElem hj, ← List.append_assoc, ← harr, ← hx]
      exact arrAt_push hhdr' hcell (fun i hi' => fr _ (by addr') (by addr') (by omega) (by omega))
    · rw [Mem.write_ne _ _ (by addr'), fr HP (by addr') (by addr') (by addr') (by addr')]; exact hroom
    · rw [Mem.write_ne _ _ (by addr'), m'one]
    · rw [Mem.write_ne _ _ (by addr'), fr HP (by addr') (by addr') (by addr') (by addr')]; exact hsz
    · intro i hi'
      rw [hw _ (by omega), fr _ (by addr') (by addr') (by omega) (by omega), hcells i hi']

theorem appendM_spec (L A B n : ℕ) (hL : L ≤ 9) (hA : 5 ≤ A ∧ A < IN) (hB : 5 ≤ B ∧ B < IN)
    (hAL : A ∉ Lvars L) (hBL : B ∉ Lvars L) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (harrA : ∀ m, Pre m → IN ≤ m A ∧ m A + 1 + m (m A) ≤ m HP ∧ m (m A) ≤ n)
    (harrB : ∀ m, Pre m → IN ≤ m B ∧ m B + 1 + m (m B) ≤ m HP ∧ m (m B) ≤ n) :
    RSpec (appendM L A B) (Lvars L) (2 * n * 12 + 15) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧ arrAt m' (m HP) = arrAt m (m A) ++ arrAt m (m B) ∧
        m HP + 1 + m (m A) + m (m B) ≤ m' HP) := by
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨haA, harrA0, hnA⟩ := harrA m0 hm0
  obtain ⟨haB, harrB0, hnB⟩ := harrB m0 hm0
  obtain ⟨la, hla⟩ : ∃ la, arrAt m0 (m0 A) = la := ⟨_, rfl⟩
  obtain ⟨lb, hlb⟩ : ∃ lb, arrAt m0 (m0 B) = lb := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  have hlena : la.length = m0 (m0 A) := by rw [← hla, arrAt_length]
  have hlenb : lb.length = m0 (m0 B) := by rw [← hlb, arrAt_length]
  have hAO : A ≠ OUT_ L := fun h => hAL (by rw [h]; simp [Lvars])
  have hBO : B ≠ OUT_ L := fun h => hBL (by rw [h]; simp [Lvars])
  have hAC : A ≠ CNT_ L := fun h => hAL (by rw [h]; simp [Lvars])
  have hBC : B ≠ CNT_ L := fun h => hBL (by rw [h]; simp [Lvars])
  have hACO : A ≠ CONT_ L := fun h => hAL (by rw [h]; simp [Lvars])
  have hBCO : B ≠ CONT_ L := fun h => hBL (by rw [h]; simp [Lvars])
  have hAI : A ≠ I_ L := fun h => hAL (by rw [h]; simp [Lvars])
  have hBI : B ≠ I_ L := fun h => hBL (by rw [h]; simp [Lvars])
  -- setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov (OUT_ L) HP) m0 m1 1 := by
    have := Exec.mov (OUT_ L) HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write hdr 0 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (store (OUT_ L) ZERO) m1 m2 1 := by
    have := Exec.store (OUT_ L) ZERO m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr'), hzero0] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (CNT_ L) la.length := ⟨_, rfl⟩
  have e3 : Cmd.Exec (load (CNT_ L) A) m2 m3 1 := by
    have := Exec.load (CNT_ L) A m2
    rw [hm2, Mem.write_ne _ _ (show A ≠ hdr by addr'), hm1, Mem.write_ne _ _ hAO,
      Mem.write_ne _ _ (show m0 A ≠ hdr by omega), Mem.write_ne _ _ (by addr'), ← hlena] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (CONT_ L) lb.length := ⟨_, rfl⟩
  have e4 : Cmd.Exec (load (CONT_ L) B) m3 m4 1 := by
    have := Exec.load (CONT_ L) B m3
    rw [hm3, Mem.write_ne _ _ hBC, hm2, Mem.write_ne _ _ (show B ≠ hdr by addr'), hm1,
      Mem.write_ne _ _ hBO, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (show m0 B ≠ hdr by omega),
      Mem.write_ne _ _ (by addr'), ← hlenb] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (CNT_ L) (la.length + lb.length) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add (CNT_ L) (CNT_ L) (CONT_ L)) m4 m5 1 := by
    have := Exec.add (CNT_ L) (CNT_ L) (CONT_ L) m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same] at this
    rw [hm5, hm4, hm3]; exact this
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write HP (hdr + (la.length + lb.length)) := ⟨_, rfl⟩
  have e6 : Cmd.Exec (add HP HP (CNT_ L)) m5 m6 1 := by
    have := Exec.add HP HP (CNT_ L) m5
    rw [hm5, Mem.write_same, Mem.write_ne _ _ (by addr'), hm4, Mem.write_ne _ _ (by addr'), hm3,
      Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'),
      ← hhdr] at this
    rw [hm6, hm5, hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m7, hm7⟩ : ∃ m7, m7 = m5.write HP (hdr + 1 + (la.length + lb.length)) := ⟨_, rfl⟩
  have e7 : Cmd.Exec (add HP HP ONE) m6 m7 1 := by
    have := Exec.add HP HP ONE m6
    rw [hm6, Mem.write_same, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm4,
      Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'),
      hm1, Mem.write_ne _ _ (by addr'), hone0, Mem.write_write,
      show hdr + (la.length + lb.length) + 1 = hdr + 1 + (la.length + lb.length) by omega] at this
    rw [hm7, hm6, hm5, hm4, hm3, hm2, hm1]; exact this
  have q7 : ∀ x, x ≠ HP → x ≠ CNT_ L → x ≠ CONT_ L → x ≠ hdr → x ≠ OUT_ L → m7 x = m0 x :=
    fun x h1 h2 h3 h4 h5 => by
      rw [hm7, Mem.write_ne _ _ h1, hm5, Mem.write_ne _ _ h2, hm4, Mem.write_ne _ _ h3, hm3,
        Mem.write_ne _ _ h2, hm2, Mem.write_ne _ _ h4, hm1, Mem.write_ne _ _ h5]
  have m7HP : m7 HP = hdr + 1 + (la.length + lb.length) := by rw [hm7, Mem.write_same]
  have m7hdr : m7 hdr = 0 := by
    rw [hm7, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm4,
      Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
  have m7O : m7 (OUT_ L) = hdr := by
    rw [hm7, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'), hm4,
      Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'),
      hm1, Mem.write_same]
  have agree7 : Agree m0 m7 (Lvars L) := by
    refine ⟨fun x hx hxV => ?_, by rw [m7HP]; omega⟩
    simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hxV
    exact q7 x hxV.1 hxV.2.2.1 hxV.2.2.2.2.1 (by omega) hxV.2.2.2.2.2.2
  have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
  have hAv : ∀ m, Agree m0 m (Lvars L) → m A = m0 A := fun m hag =>
    hag.var A (by addr') (by addr') hAL
  have hBv : ∀ m, Agree m0 m (Lvars L) → m B = m0 B := fun m hag =>
    hag.var B (by addr') (by addr') hBL
  have hLlt : ∀ x, x ∈ Lvars L → x < IN := fun x hx => (Lvars_range L hL x hx).2
  -- first pass
  have inv7 : AppInv L m0 hdr (m0 A) [] la (la.length + lb.length) 0
      ((m7.write (CNT_ L) la.length).write (I_ L) 0) := by
    have ag : Agree m0 ((m7.write (CNT_ L) la.length).write (I_ L) 0) (Lvars L) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1, Mem.write_ne _ _ hyV'.2.2.1]
        exact agree7.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact agree7.2
    have hw : ∀ x, IN ≤ x → ((m7.write (CNT_ L) la.length).write (I_ L) 0) x = m7 x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨ag, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr'), Mem.write_same],
      by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m7O], ?_,
      by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m7HP], ?_, ?_, ?_⟩
    · simp only [List.take_zero, List.append_nil, arrAt, hw hdr hhdrIN, m7hdr, List.range_zero,
        List.map_nil]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'),
        q7 ONE (by addr') (by addr') (by addr') (by addr') (by addr'), hone0]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m7HP, hlena]; omega
    · intro i hi
      rw [hw _ (by omega), q7 _ (by addr') (by addr') (by addr') (by omega) (by addr'),
        ← arrAt_getElem m0 (m0 A) i (by rw [arrAt_length, ← hlena]; exact hi)]
      exact List.getElem_of_eq hla _
  obtain ⟨m8, k8, e8, inv8, hk8⟩ := appendM_pass L A hL hA hAL m0 hdr (m0 A) [] la
    (la.length + lb.length) hhdrIN haA (by omega) (by rw [hlena]; exact harrA0) (by simp) hAv m7 inv7
    (by rw [q7 A (by addr') hAC hACO (by addr') hAO]) (by
      rw [q7 (m0 A) (by addr') (by addr') (by addr') (by omega) (by addr'), hlena])
  -- second pass
  have inv8' : AppInv L m0 hdr (m0 B) la lb (la.length + lb.length) 0
      ((m8.write (CNT_ L) lb.length).write (I_ L) 0) := by
    obtain ⟨hag, hi, hcnt, hout, harr, hroom, hone, hsz, hcells⟩ := inv8
    have ag : Agree m0 ((m8.write (CNT_ L) lb.length).write (I_ L) 0) (Lvars L) := by
      refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1, Mem.write_ne _ _ hyV'.2.2.1]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hag.2
    have hw : ∀ x, IN ≤ x → ((m8.write (CNT_ L) lb.length).write (I_ L) 0) x = m8 x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨ag, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr'), Mem.write_same],
      by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout], ?_,
      by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom, ?_, ?_, ?_⟩
    · have harr' : arrAt m8 hdr = la := by rw [harr, List.nil_append, List.take_length]
      rw [List.take_zero, List.append_nil, ← harr']
      exact arrAt_congr (fun x h1 h2 => hw x (by omega))
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hone]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
      have := hag.2; rw [hlenb]; omega
    · intro i hi
      rw [hw _ (by omega), hag.heap hLlt _ (by omega) (by omega),
        ← arrAt_getElem m0 (m0 B) i (by rw [arrAt_length, ← hlenb]; exact hi)]
      exact List.getElem_of_eq hlb _
  obtain ⟨m9, k9, e9, inv9, hk9⟩ := appendM_pass L B hL hB hBL m0 hdr (m0 B) la lb
    (la.length + lb.length) hhdrIN haB (by omega) (by rw [hlenb]; exact harrB0) (by omega) hBv m8 inv8'
    (hBv m8 inv8.agree) (by
      rw [inv8.agree.heap hLlt _ haB (by omega), hlenb])
  refine ⟨m9, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5
    (Cmd.Exec.seq e6 (Cmd.Exec.seq e7 (Cmd.Exec.seq e8 e9))))))), ?_, inv9.agree, ?_⟩
  · have h1 : la.length * 12 ≤ n * 12 := Nat.mul_le_mul_right _ (by omega)
    have h2 : lb.length * 12 ≤ n * 12 := Nat.mul_le_mul_right _ (by omega)
    omega
  · refine ⟨by rw [inv9.out, hhdr], ?_, ?_⟩
    · rw [← hhdr, inv9.arr, List.take_length, hla, hlb]
    · rw [← hlena, ← hlenb, ← hhdr]; have := inv9.room; omega


/-! ### `flatten` -/

/-- `CONT_ L := Σ` of the lengths of the arrays pointed to from the array at `SRC`. -/
def sumLenM (L SRC : ℕ) : Cmd :=
  .seq (setc (CONT_ L) 0)
    (forEachM L SRC (.seq (load (PTR_ L) (X_ L)) (add (CONT_ L) (CONT_ L) (PTR_ L))))

/-- The concatenation of the arrays pointed to from the array at `SRC` (address in `OUT_ L`). -/
def flattenM (L SRC : ℕ) : Cmd :=
  .seq (sumLenM L SRC) (.seq (mov (OUT_ L) HP) (.seq (store (OUT_ L) ZERO)
    (.seq (add HP HP (CONT_ L)) (.seq (add HP HP ONE)
      (forEachM L SRC (forEachM (L + 1) (X_ L) (pushV L (X_ (L + 1)))))))))

/-- Well-formed array of pointers to arrays, all below the heap pointer. -/
def ArrsWF (m : Mem) (a : ℕ) : Prop :=
  IN ≤ a ∧ a + 1 + m a ≤ m HP ∧ ∀ q, q ∈ arrAt m a → IN ≤ q ∧ q + 1 + m q ≤ m HP

theorem sumLen_take_succ {m0 : Mem} {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    ((l.take (j + 1)).map (fun q => m0 q)).sum = ((l.take j).map (fun q => m0 q)).sum + m0 l[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]

theorem flatten_take_succ {m0 : Mem} {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    ((l.take (j + 1)).map (fun q => arrAt m0 q)).flatten =
      ((l.take j).map (fun q => arrAt m0 q)).flatten ++ arrAt m0 l[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.map_append, List.flatten_append, List.map_singleton,
    List.flatten_singleton]

theorem sumLenM_spec (L SRC n : ℕ) (hL : L ≤ 9) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSL : SRC ∉ Lvars L)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hwf : ∀ m, Pre m → ArrsWF m (m SRC))
    (hn : ∀ m, Pre m → m (m SRC) ≤ n) :
    RSpec (sumLenM L SRC) (Lvars L) (n * 8 + 5) Pre
      (fun m m' => m' (CONT_ L) = ((arrAt m (m SRC)).map (fun q => m q)).sum ∧ m' HP = m HP) := by
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨hsrc0, harr0, hq0⟩ := hwf m0 hm0
  have hn0 := hn m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hSC : SRC ≠ CONT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hLlt : ∀ x, x ∈ Lvars L → x < IN := fun x hx => (Lvars_range L hL x hx).2
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (CONT_ L) 0 := ⟨_, rfl⟩
  have e1 : Cmd.Exec (setc (CONT_ L) 0) m0 m1 1 := by rw [hm1]; exact Exec.setc _ _ _
  have main := forEachM_spec L SRC hL hSRC.2 hSL (.seq (load (PTR_ L) (X_ L)) (add (CONT_ L) (CONT_ L) (PTR_ L)))
    (fun j m => Agree m0 m (Lvars L) ∧ m (I_ L) = j ∧ m (CNT_ L) = l.length ∧ m HP = m0 HP ∧
      m (CONT_ L) = ((l.take j).map (fun q => m0 q)).sum)
    (m0 SRC) hsrc0 l 2 ?_ ?_ ?_ m1 (by rw [hm1, Mem.write_ne _ _ hSC]) (by
      rw [hm1, Mem.write_ne _ _ (by addr'), hlen]) ?_
  · obtain ⟨m', k, e, ⟨hag, hi, hcnt, hhp, hcont⟩, hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 e, ?_, hag, ?_, hhp⟩
    · have : l.length * (2 + 6) ≤ n * 8 := Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [hcont, List.take_length, hl]
  · intro j m ⟨hag, hi, hcnt, hhp, hcont⟩
    refine ⟨hi, hcnt, hag.var SRC (by addr') (by addr') hSL, ?_, ?_, ?_⟩
    · rw [hag.var ONE (by addr') (by addr') (fun h => by have := (Lvars_range L hL _ h).1; addr'), hone0]
    · rw [hhp, hlen]; exact harr0
    · intro i hi'
      rw [hag.heap hLlt _ (by omega) (by omega),
        ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length, ← hlen]; exact hi')]
      exact List.getElem_of_eq hl _
  · intro j m v w ⟨hag, hi, hcnt, hhp, hcont⟩
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp [Lvars]), ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hhp]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcont]
  · intro j m hj ⟨hag, hi, hcnt, hhp, hcont⟩ hx _
    have hq : IN ≤ l[j] ∧ l[j] + 1 + m0 l[j] ≤ m0 HP := hq0 _ (by rw [hl]; exact List.getElem_mem hj)
    obtain ⟨n1, hn1⟩ : ∃ n1, n1 = m.write (PTR_ L) (m0 l[j]) := ⟨_, rfl⟩
    have f1 : Cmd.Exec (load (PTR_ L) (X_ L)) m n1 1 := by
      have := Exec.load (PTR_ L) (X_ L) m
      rw [hx, hag.heap hLlt _ hq.1 (by omega)] at this
      rw [hn1]; exact this
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = n1.write (CONT_ L) (((l.take j).map (fun q => m0 q)).sum + m0 l[j]) :=
      ⟨_, rfl⟩
    have f2 : Cmd.Exec (add (CONT_ L) (CONT_ L) (PTR_ L)) n1 n2 1 := by
      have := Exec.add (CONT_ L) (CONT_ L) (PTR_ L) n1
      rw [hn1, Mem.write_same, Mem.write_ne _ _ (by addr'), hcont] at this
      rw [hn2, hn1]; exact this
    have q2 : ∀ x, x ≠ CONT_ L → x ≠ PTR_ L → n2 x = m x := fun x h1 h2 => by
      rw [hn2, Mem.write_ne _ _ h1, hn1, Mem.write_ne _ _ h2]
    refine ⟨n2, _, Cmd.Exec.seq f1 f2, by omega, by rw [q2 _ (by addr') (by addr'), hi],
      by rw [q2 _ (by addr') (by addr'),
        hag.var ONE (by addr') (by addr') (fun h => by have := (Lvars_range L hL _ h).1; addr'), hone0],
      ?_, by rw [Mem.write_same], ?_, ?_, ?_⟩
    · refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1, q2 y hyV'.2.2.2.2.1 hyV'.2.2.2.1]
        exact hag.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), q2 HP (by addr') (by addr')]; exact hag.2
    · rw [Mem.write_ne _ _ (by addr'), q2 _ (by addr') (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), q2 _ (by addr') (by addr'), hhp]
    · rw [Mem.write_ne _ _ (by addr'), hn2, Mem.write_same, sumLen_take_succ hj]
  · refine ⟨?_, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr'), Mem.write_same], ?_, ?_⟩
    · refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1, Mem.write_ne _ _ hyV'.2.2.1, hm1, Mem.write_ne _ _ hyV'.2.2.2.2.1]
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr')]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr')]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm1, Mem.write_same]; rfl


/-- The outer invariant of `flattenM`. -/
structure FlatInv (L : ℕ) (m0 : Mem) (hdr tot : ℕ) (l : List ℕ) (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ Lvars (L + 1))
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = hdr
  arr : arrAt m hdr = ((l.take j).map (fun q => arrAt m0 q)).flatten
  room : hdr + 1 + tot ≤ m HP

/-- The inner invariant of `flattenM` (copying the `j`-th inner array). -/
structure FlatInInv (L : ℕ) (m0 : Mem) (hdr tot : ℕ) (l : List ℕ) (j : ℕ) (q : ℕ) (i : ℕ)
    (m : Mem) : Prop where
  agree : Agree m0 m (Lvars L ++ Lvars (L + 1))
  ii : m (I_ (L + 1)) = i
  icnt : m (CNT_ (L + 1)) = m0 q
  x : m (X_ L) = q
  i0 : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m (OUT_ L) = hdr
  arr : arrAt m hdr = ((l.take j).map (fun q => arrAt m0 q)).flatten ++ (arrAt m0 q).take i
  room : hdr + 1 + tot ≤ m HP

theorem flattenM_spec (L SRC n : ℕ) (hL : L + 1 ≤ 9) (hSRC : 5 ≤ SRC ∧ SRC < IN)
    (hSL : SRC ∉ Lvars L) (hSL' : SRC ∉ Lvars (L + 1))
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hwf : ∀ m, Pre m → ArrsWF m (m SRC))
    (hn : ∀ m, Pre m → m (m SRC) ≤ n ∧ ∀ q, q ∈ arrAt m (m SRC) → m q ≤ n) :
    RSpec (flattenM L SRC) (Lvars L ++ Lvars (L + 1)) (12 * n * n + 18 * n + 13) Pre
      (fun m m' => m' (OUT_ L) = m HP ∧
        arrAt m' (m HP) = ((arrAt m (m SRC)).map (fun q => arrAt m q)).flatten ∧
        m HP + 1 + ((arrAt m (m SRC)).map (fun q => m q)).sum ≤ m' HP) := by
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨hsrc0, harr0, hq0⟩ := hwf m0 hm0
  obtain ⟨hn0, hnq⟩ := hn m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  obtain ⟨tot, htot⟩ : ∃ tot, tot = (l.map (fun q => m0 q)).sum := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hLlt : ∀ x, x ∈ Lvars L ++ Lvars (L + 1) → x < IN := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with h | h
    · exact (Lvars_range L (by omega) x h).2
    · exact (Lvars_range (L + 1) hL x h).2
  have hL5 : ∀ x, x ∈ Lvars L ++ Lvars (L + 1) → 5 ≤ x := by
    intro x hx; rw [List.mem_append] at hx
    rcases hx with h | h
    · have := (Lvars_range L (by omega) x h).1; omega
    · have := (Lvars_range (L + 1) hL x h).1; omega
  have hSC : SRC ≠ CONT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSO : SRC ≠ OUT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp0
  have hSv : ∀ m, Agree m0 m (Lvars L ++ Lvars (L + 1)) → m SRC = m0 SRC := fun m hag =>
    hag.var SRC (by addr') (by addr') (by rw [List.mem_append, not_or]; exact ⟨hSL, hSL'⟩)
  have hcellv : ∀ m, Agree m0 m (Lvars L ++ Lvars (L + 1)) → ∀ i, (h : i < l.length) →
      m (m0 SRC + 1 + i) = l[i] := by
    intro m hag i hi
    rw [hag.heap hLlt _ (by omega) (by omega),
      ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length, ← hlen]; exact hi)]
    exact List.getElem_of_eq hl _
  have hqwf : ∀ j, (h : j < l.length) → IN ≤ l[j] ∧ l[j] + 1 + m0 l[j] ≤ m0 HP ∧ m0 l[j] ≤ n :=
    fun j hj => ⟨(hq0 _ (by rw [hl]; exact List.getElem_mem hj)).1,
      (hq0 _ (by rw [hl]; exact List.getElem_mem hj)).2, hnq _ (by rw [hl]; exact List.getElem_mem hj)⟩
  -- the sum
  obtain ⟨m1, k1, e1, hk1, ag1, hcont1, hhp1⟩ := sumLenM_spec L SRC n (by omega) hSRC hSL Pre hctx hwf
    (fun m hm => (hn m hm).1) m0 hm0
  rw [hl, ← htot] at hcont1
  have hag1' : Agree m0 m1 (Lvars L ++ Lvars (L + 1)) := ag1.mono (fun x hx => List.mem_append_left _ hx)
  have m1one : m1 ONE = 1 := by rw [ag1.var ONE (by addr') (by addr') (fun h => by have := (Lvars_range L (by omega) _ h).1; addr'), hone0]
  have m1zero : m1 ZERO = 0 := by rw [ag1.var ZERO (by addr') (by addr') (fun h => by have := (Lvars_range L (by omega) _ h).1; addr'), hzero0]
  -- the allocation
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (OUT_ L) hdr := ⟨_, rfl⟩
  have e2 : Cmd.Exec (mov (OUT_ L) HP) m1 m2 1 := by
    have := Exec.mov (OUT_ L) HP m1; rwa [hhp1, ← hhdr, ← hm2] at this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write hdr 0 := ⟨_, rfl⟩
  have e3 : Cmd.Exec (store (OUT_ L) ZERO) m2 m3 1 := by
    have := Exec.store (OUT_ L) ZERO m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr'), m1zero] at this
    rw [hm3, hm2]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (hdr + tot) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP HP (CONT_ L)) m3 m4 1 := by
    have := Exec.add HP HP (CONT_ L) m3
    rw [hm3, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hhp1, ← hhdr, hcont1] at this
    rw [hm4, hm3, hm2]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m3.write HP (hdr + 1 + tot) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_same, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2,
      Mem.write_ne _ _ (by addr'), m1one, Mem.write_write,
      show hdr + tot + 1 = hdr + 1 + tot by omega] at this
    rw [hm5, hm4, hm3, hm2]; exact this
  have q5 : ∀ x, x ≠ HP → x ≠ hdr → x ≠ OUT_ L → m5 x = m1 x := fun x h1 h2 h3 => by
    rw [hm5, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h2, hm2, Mem.write_ne _ _ h3]
  have m5HP : m5 HP = hdr + 1 + tot := by rw [hm5, Mem.write_same]
  have m5hdr : m5 hdr = 0 := by rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
  have m5O : m5 (OUT_ L) = hdr := by
    rw [hm5, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
  have agree5 : Agree m0 m5 (Lvars L ++ Lvars (L + 1)) := by
    refine ⟨fun x hx hxV => ?_, by rw [m5HP]; omega⟩
    have hxV' := hxV
    simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hxV'
    rw [q5 x hxV'.1 (by omega) hxV'.2.1.2.2.2.2.2]
    exact hag1'.1 x hx hxV
  -- the copying loops
  have main := forEachM_spec L SRC (by omega) hSRC.2 hSL (forEachM (L + 1) (X_ L) (pushV L (X_ (L + 1))))
    (FlatInv L m0 hdr tot l) (m0 SRC) hsrc0 l (n * 12 + 4) ?_ ?_ ?_ m5
    (by rw [q5 SRC (by addr') (by addr') hSO, hSv m1 hag1']) (by
      rw [q5 (m0 SRC) (by addr') (by omega) (by addr'), hag1'.heap hLlt _ hsrc0 (by omega), hlen]) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4
      (Cmd.Exec.seq e5 e)))), ?_, inv'.agree, ?_⟩
    · have h1 : l.length * (n * 12 + 4 + 6) ≤ n * (n * 12 + 10) := Nat.mul_le_mul_right _ (by omega)
      have h2 : n * (n * 12 + 10) = 12 * n * n + 10 * n := by ring
      omega
    · refine ⟨by rw [inv'.out, hhdr], ?_, ?_⟩
      · rw [← hhdr, inv'.arr, List.take_length, hl]
      · rw [hl, ← htot, ← hhdr]; exact inv'.room
  · -- hI
    intro j m hm
    obtain ⟨hag, hi, hcnt, hout, harr, hroom⟩ := hm
    refine ⟨hi, hcnt, hSv m hag, ?_, ?_, hcellv m hag⟩
    · rw [hag.var ONE (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hone0]
    · exact le_trans (by rw [hlen]; exact harr0) hag.2
  · -- hstable
    intro j m v w hm
    obtain ⟨hag, hi, hcnt, hout, harr, hroom⟩ := hm
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    have hw : ∀ x, IN ≤ x → ((m.write (PTR_ L) v).write (X_ L) w) x = m x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp [Lvars]), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout]
    · rw [← harr]; exact arrAt_congr (fun x h1 h2 => hw x (by omega))
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom
  · -- hbody: the inner loop
    intro j m hj hm hx _
    obtain ⟨hag, hi, hcnt, hout, harr, hroom⟩ := hm
    obtain ⟨hqIN, hqwf', hqn⟩ := hqwf j hj
    have hXL : X_ L ∉ Lvars (L + 1) := by
      intro h; simp [Lvars, X_, I_, CNT_, PTR_, CONT_, OUT_] at h; omega
    have inner := forEachM_spec (L + 1) (X_ L) hL (by addr') hXL (pushV L (X_ (L + 1)))
      (FlatInInv L m0 hdr tot l j l[j]) l[j] hqIN (arrAt m0 l[j]) 6 ?_ ?_ ?_ m hx
      (by rw [hag.heap hLlt _ hqIN (by omega), arrAt_length]) ?_
    · obtain ⟨m', k, e, inv', hk⟩ := inner
      have hw : ∀ x, IN ≤ x → (m'.write (I_ L) (j + 1)) x = m' x := fun x hx => by
        rw [Mem.write_ne _ _ (by addr')]
      refine ⟨m', k, e, ?_, inv'.i0, ?_, ?_⟩
      · have : (arrAt m0 l[j]).length * (6 + 6) ≤ n * 12 := Nat.mul_le_mul_right _ (by rw [arrAt_length]; exact hqn)
        omega
      · rw [inv'.agree.var ONE (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hone0]
      · refine ⟨?_, by rw [Mem.write_same], ?_, ?_, ?_, ?_⟩
        · refine ⟨fun y hy hyV => ?_, ?_⟩
          · have hyV' := hyV
            simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
            rw [Mem.write_ne _ _ hyV'.2.1.1]
            exact inv'.agree.1 y hy hyV
          · rw [Mem.write_ne _ _ (by addr')]; exact inv'.agree.2
        · rw [Mem.write_ne _ _ (by addr'), inv'.cnt]
        · rw [Mem.write_ne _ _ (by addr'), inv'.out]
        · rw [flatten_take_succ hj, ← List.take_length (l := arrAt m0 l[j]), ← inv'.arr]
          exact arrAt_congr (fun x h1 h2 => hw x (by omega))
        · rw [Mem.write_ne _ _ (by addr')]; exact inv'.room
    · -- inner hI
      intro i m' hm'
      obtain ⟨hag', hii, hicnt, hx', hi0, hcnt', hout', harr', hroom'⟩ := hm'
      refine ⟨hii, by rw [hicnt, arrAt_length], hx', ?_, ?_, ?_⟩
      · rw [hag'.var ONE (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hone0]
      · rw [arrAt_length]; exact le_trans hqwf' hag'.2
      · intro i' hi'
        rw [hag'.heap hLlt _ (by omega) (by rw [arrAt_length] at hi'; omega), arrAt_getElem]
    · -- inner hstable
      intro i m' v w hm'
      obtain ⟨hag', hii, hicnt, hx', hi0, hcnt', hout', harr', hroom'⟩ := hm'
      have hag'' : Agree m' ((m'.write (PTR_ (L + 1)) v).write (X_ (L + 1)) w) [PTR_ (L + 1), X_ (L + 1)] := by
        refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
      have hw : ∀ x, IN ≤ x → ((m'.write (PTR_ (L + 1)) v).write (X_ (L + 1)) w) x = m' x := fun x hx => by
        rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
      refine ⟨(hag'.trans hag'').mono (by
          intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
          · exact h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl <;> simp [Lvars]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hii]
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hicnt]
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hx']
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi0]
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt']
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout']
      · rw [← harr']; exact arrAt_congr (fun x h1 h2 => hw x (by omega))
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom'
    · -- inner body: push
      intro i m' hi' hm' hx' _
      obtain ⟨hag', hii, hicnt, hx'', hi0, hcnt', hout', harr', hroom'⟩ := hm'
      have hone' : m' ONE = 1 := by
        rw [hag'.var ONE (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hone0]
      have hlen' : m' hdr = ((l.take j).map (fun q => arrAt m0 q)).flatten.length + i := by
        have h := congrArg List.length harr'
        rw [arrAt_length, List.length_append, List.length_take, min_eq_left (by omega)] at h
        exact h
      have hlt : ((l.take j).map (fun q => arrAt m0 q)).flatten.length + i < tot := by
        rw [htot]
        have h1 : ((l.take j).map (fun q => arrAt m0 q)).flatten.length =
            ((l.take j).map (fun q => m0 q)).sum := by
          rw [List.length_flatten, List.map_map]; congr 1
          apply List.map_congr_left; intro q _; simp [arrAt_length]
        have h2 : (l.map (fun q => m0 q)).sum = ((l.take (j + 1)).map (fun q => m0 q)).sum +
            ((l.drop (j + 1)).map (fun q => m0 q)).sum := by
          rw [← List.sum_append, ← List.map_append, List.take_append_drop]
        rw [h2, sumLen_take_succ hj, h1]
        rw [arrAt_length] at hi'
        omega
      obtain ⟨m'', k, e, hk, fr, hhdr', hcell⟩ := pushV_spec L (X_ (L + 1)) (by omega) (by addr')
        (by addr') (by addr') m' hdr hout' hone' hhdrIN
      have hw : ∀ x, IN ≤ x → (m''.write (I_ (L + 1)) (i + 1)) x = m'' x := fun x hx => by
        rw [Mem.write_ne _ _ (by addr')]
      refine ⟨m'', k, e, hk, by rw [fr _ (by addr') (by addr') (by addr') (by addr'), hii],
        by rw [fr _ (by addr') (by addr') (by addr') (by addr'), hone'], ?_⟩
      refine ⟨?_, by rw [Mem.write_same], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun y hy hyV => ?_, ?_⟩
        · have hyV' := hyV
          simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
          rw [Mem.write_ne _ _ hyV'.2.2.1, fr y hyV'.2.1.2.2.2.1 hyV'.2.1.2.2.1 (by omega) (by omega)]
          exact hag'.1 y hy hyV
        · rw [Mem.write_ne _ _ (by addr'), fr HP (by addr') (by addr') (by addr') (by addr')]
          exact hag'.2
      · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hicnt]
      · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hx'']
      · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hi0]
      · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hcnt']
      · rw [Mem.write_ne _ _ (by addr'), fr _ (by addr') (by addr') (by addr') (by addr'), hout']
      · have h1 : arrAt (m''.write (I_ (L + 1)) (i + 1)) hdr = arrAt m'' hdr :=
          arrAt_congr (fun x h1 h2 => hw x (by omega))
        rw [h1, List.take_succ_eq_append_getElem hi', ← List.append_assoc, ← harr', ← hx']
        exact arrAt_push hhdr' hcell (fun i hi' => fr _ (by addr') (by addr') (by omega) (by omega))
      · rw [Mem.write_ne _ _ (by addr'), fr HP (by addr') (by addr') (by addr') (by addr')]; exact hroom'
    · -- the initial inner invariant
      have hw : ∀ x, IN ≤ x → ((m.write (CNT_ (L + 1)) (arrAt m0 l[j]).length).write (I_ (L + 1)) 0) x = m x :=
        fun x hx => by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
      refine ⟨?_, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr'), Mem.write_same, arrAt_length],
        by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hx],
        by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi],
        by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt],
        by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hout], ?_,
        by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom⟩
      · refine ⟨fun y hy hyV => ?_, ?_⟩
        · have hyV' := hyV
          simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
          rw [Mem.write_ne _ _ hyV'.2.2.1, Mem.write_ne _ _ hyV'.2.2.2.1]
          exact hag.1 y hy hyV
        · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hag.2
      · rw [List.take_zero, List.append_nil, ← harr]
        exact arrAt_congr (fun x h1 h2 => hw x (by omega))
  · -- the initial outer invariant
    have hw : ∀ x, IN ≤ x → ((m5.write (CNT_ L) l.length).write (I_ L) 0) x = m5 x :=
      fun x hx => by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    refine ⟨?_, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr'), Mem.write_same],
      by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5O], ?_,
      by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m5HP]⟩
    · refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, Mem.write_ne _ _ hyV'.2.1.2.1]
        exact agree5.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact agree5.2
    · simp only [List.take_zero, List.map_nil, List.flatten_nil, arrAt, hw hdr hhdrIN, m5hdr,
        List.range_zero]


/-! ### Membership of a pair (by value) in an array of pairs -/

/-- `FLAG := (record at M[a]) = (record at M[b])`, using the scratch variables `s1`, `s2`. -/
def pairEqTest (a b s1 s2 : ℕ) : Cmd :=
  .seq (load s1 a) (.seq (load s2 b) (.ite (.eq s1 s2)
    (.seq (add s1 a ONE) (.seq (load s1 s1) (.seq (add s2 b ONE) (.seq (load s2 s2)
      (.ite (.eq s1 s2) (setc FLAG 1) (setc FLAG 0))))))
    (setc FLAG 0)))

theorem pairEqTest_spec (a b s1 s2 : ℕ) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (hs1 : 5 ≤ s1 ∧ s1 < IN) (hs2 : 5 ≤ s2 ∧ s2 < IN) (h12 : s1 ≠ s2) (ha : a < IN) (hb : b < IN)
    (ha1 : a ≠ s1) (ha2 : a ≠ s2) (hb1 : b ≠ s1) (hb2 : b ≠ s2) (hF1 : FLAG ≠ s1) (hF2 : FLAG ≠ s2)
    (hrec : ∀ m, Pre m → IN ≤ m a ∧ IN ≤ m b) :
    TestSpec (pairEqTest a b s1 s2) [s1, s2, FLAG] 12 Pre
      (fun m => decide ((m (m a), m (m a + 1)) = (m (m b), m (m b + 1)))) := by
  intro m hm
  dsimp only
  obtain ⟨hone, _, hhp⟩ := hctx m hm
  obtain ⟨hra, hrb⟩ := hrec m hm
  have hagree : ∀ m', (∀ x, x ≠ s1 → x ≠ s2 → x ≠ FLAG → m' x = m x) → Agree m m' [s1, s2, FLAG] := by
    intro m' h
    refine ⟨fun y _ hy => ?_, by rw [h HP (by addr') (by addr') (by addr')]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact h y hy.2.1 hy.2.2.1 hy.2.2.2
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write s1 (m (m a)) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load s1 a) m m1 1 := by rw [hm1]; exact Exec.load _ _ _
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write s2 (m (m b)) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (load s2 b) m1 m2 1 := by
    have := Exec.load s2 b m1
    rw [hm1, Mem.write_ne _ _ hb1, Mem.write_ne _ _ (by omega)] at this
    rw [hm2, hm1]; exact this
  have q2 : ∀ x, x ≠ s1 → x ≠ s2 → m2 x = m x := fun x h1 h2 => by
    rw [hm2, Mem.write_ne _ _ h2, hm1, Mem.write_ne _ _ h1]
  have m2s1 : m2 s1 = m (m a) := by rw [hm2, Mem.write_ne _ _ h12, hm1, Mem.write_same]
  have m2s2 : m2 s2 = m (m b) := by rw [hm2, Mem.write_same]
  by_cases hfst : m (m a) = m (m b)
  · have hc : (Cond.eq s1 s2).eval m2 = true := by simp [Cond.eval, m2s1, m2s2, hfst]
    obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write s1 (m a + 1) := ⟨_, rfl⟩
    have e3 : Cmd.Exec (add s1 a ONE) m2 m3 1 := by
      have := Exec.add s1 a ONE m2
      rw [q2 a ha1 ha2, q2 ONE (by addr') (by addr'), hone] at this
      rw [hm3]; exact this
    obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write s1 (m (m a + 1)) := ⟨_, rfl⟩
    have e4 : Cmd.Exec (load s1 s1) m3 m4 1 := by
      have := Exec.load s1 s1 m3
      rw [hm3, Mem.write_same, Mem.write_ne _ _ (by omega), q2 _ (by omega) (by omega)] at this
      rw [hm4, hm3]; exact this
    obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write s2 (m b + 1) := ⟨_, rfl⟩
    have e5 : Cmd.Exec (add s2 b ONE) m4 m5 1 := by
      have := Exec.add s2 b ONE m4
      rw [hm4, Mem.write_ne _ _ hb1, Mem.write_ne _ _ (by addr'), hm3,
        Mem.write_ne _ _ hb1, Mem.write_ne _ _ (by addr'), q2 b hb1 hb2,
        q2 ONE (by addr') (by addr'), hone] at this
      rw [hm5, hm4, hm3]; exact this
    obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write s2 (m (m b + 1)) := ⟨_, rfl⟩
    have e6 : Cmd.Exec (load s2 s2) m5 m6 1 := by
      have := Exec.load s2 s2 m5
      rw [hm5, Mem.write_same, Mem.write_ne _ _ (by omega), hm4, Mem.write_ne _ _ (by omega), hm3,
        Mem.write_ne _ _ (by omega), q2 _ (by omega) (by omega)] at this
      rw [hm6, hm5, hm4, hm3]; exact this
    have q6 : ∀ x, x ≠ s1 → x ≠ s2 → m6 x = m x := fun x h1 h2 => by
      rw [hm6, Mem.write_ne _ _ h2, hm5, Mem.write_ne _ _ h2, hm4, Mem.write_ne _ _ h1, hm3,
        Mem.write_ne _ _ h1, q2 x h1 h2]
    have m6s1 : m6 s1 = m (m a + 1) := by
      rw [hm6, Mem.write_ne _ _ h12, hm5, Mem.write_ne _ _ h12, hm4, Mem.write_same]
    have m6s2 : m6 s2 = m (m b + 1) := by rw [hm6, Mem.write_same]
    by_cases hsnd : m (m a + 1) = m (m b + 1)
    · have hc' : (Cond.eq s1 s2).eval m6 = true := by simp [Cond.eval, m6s1, m6s2, hsnd]
      refine ⟨m6.write FLAG 1, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc
        (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 (Cmd.Exec.seq e6
          (Cmd.Exec.ite_true hc' (Exec.setc _ _ _)))))))), by omega, ?_, ?_⟩
      · exact hagree _ (fun x h1 h2 h3 => by rw [Mem.write_ne _ _ h3, q6 x h1 h2])
      · rw [Mem.write_same, hfst, hsnd]; simp
    · have hc' : (Cond.eq s1 s2).eval m6 = false := by simp [Cond.eval, m6s1, m6s2, hsnd]
      refine ⟨m6.write FLAG 0, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc
        (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 (Cmd.Exec.seq e6
          (Cmd.Exec.ite_false hc' (Exec.setc _ _ _)))))))), by omega, ?_, ?_⟩
      · exact hagree _ (fun x h1 h2 h3 => by rw [Mem.write_ne _ _ h3, q6 x h1 h2])
      · rw [Mem.write_same]; simp [hsnd]
  · have hc : (Cond.eq s1 s2).eval m2 = false := by simp [Cond.eval, m2s1, m2s2, hfst]
    refine ⟨m2.write FLAG 0, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_false hc
      (Exec.setc _ _ _))), by omega, ?_, ?_⟩
    · exact hagree _ (fun x h1 h2 h3 => by rw [Mem.write_ne _ _ h3, q2 x h1 h2])
    · rw [Mem.write_same]; simp [hfst]

theorem mem_pairsAt_any (m : Mem) (d : ℕ) (p : ℕ × ℕ) :
    decide (p ∈ pairsAt m d) = (arrAt m d).any (fun q => decide ((m q, m (q + 1)) = p)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  simp only [pairsAt, List.mem_map, decide_eq_true_iff]

/-- `FLAG := (record at M[Y]) ∈ (array of records at M[D])` (by value). -/
def memPairM (L D Y : ℕ) : Cmd := anyM L D (pairEqTest (X_ L) Y (X_ (L + 1)) (PTR_ (L + 1)))

/-- Well-formed array of pointers to records, all below the heap pointer. -/
def PairsWF (m : Mem) (a : ℕ) : Prop :=
  IN ≤ a ∧ a + 1 + m a ≤ m HP ∧ RecsIn m a IN (m HP)

theorem TestSpec.congr {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P Q : Mem → Bool}
    (h : TestSpec t V B Pre P) (hPQ : ∀ m, Pre m → P m = Q m) : TestSpec t V B Pre Q := by
  intro m hm
  obtain ⟨m', k, e, hk, ag, hfl⟩ := h m hm
  refine ⟨m', k, e, hk, ag, ?_⟩
  show m' FLAG = bitv (Q m)
  rw [hfl, hPQ m hm]

theorem any_congr_mem {l : List ℕ} {p q : ℕ → Bool} (h : ∀ x, x ∈ l → p x = q x) :
    l.any p = l.any q := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩; exact ⟨x, hx, by rw [← h x hx]; exact hp⟩
  · rintro ⟨x, hx, hq⟩; exact ⟨x, hx, by rw [h x hx]; exact hq⟩

/-- The variables written by `memPairM L`. -/
def memPairV (L : ℕ) : List ℕ := Lvars L ++ FLAG :: [X_ (L + 1), PTR_ (L + 1), FLAG]

theorem memPairV_range (L : ℕ) (hL : L + 1 ≤ 9) : ∀ x, x ∈ memPairV L → 5 ≤ x ∧ x < IN := by
  intro x hx
  simp only [memPairV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | rfl | rfl | rfl | rfl
  · have := Lvars_range L (by omega) x h; constructor <;> omega
  all_goals constructor <;> addr'

theorem memPairM_spec (L D Y n : ℕ) (hL : L + 1 ≤ 9) (hD : 5 ≤ D ∧ D < IN) (hY : 5 ≤ Y ∧ Y < IN)
    (hDL : D ∉ Lvars L) (hDL' : D ∉ Lvars (L + 1)) (hYL : Y ∉ Lvars L) (hYL' : Y ∉ Lvars (L + 1))
    (hDF : D ≠ FLAG) (hYF : Y ≠ FLAG)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (hwf : ∀ m, Pre m → PairsWF m (m D) ∧ m (m D) ≤ n ∧ IN ≤ m Y ∧ m Y + 2 ≤ m HP)
    (hPre : StableP Pre (memPairV L)) :
    TestSpec (memPairM L D Y) (memPairV L) (n * 23 + 10) Pre
      (fun m => decide ((m (m Y), m (m Y + 1)) ∈ pairsAt m (m D))) := by
  have hYX : Y ≠ X_ L := fun h => hYL (by rw [h]; simp [Lvars])
  have hX1 : X_ (L + 1) ∉ LvarsX L := by simp [LvarsX, X_, I_, CNT_, PTR_, CONT_, OUT_]; omega
  have hP1 : PTR_ (L + 1) ∉ LvarsX L := by simp [LvarsX, X_, I_, CNT_, PTR_, CONT_, OUT_]; omega
  have hrecX : ∀ m, Pre m → m (X_ L) ∈ arrAt m (m D) → IN ≤ m (X_ L) ∧ m (X_ L) + 2 ≤ m HP :=
    fun m hm hx => (hwf m hm).1.2.2 _ hx
  have ht := pairEqTest_spec (X_ L) Y (X_ (L + 1)) (PTR_ (L + 1))
    (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m D)) (fun m hm => hctx m hm.1) (by constructor <;> addr')
    (by constructor <;> addr') (by addr') (by addr') hY.2 (by addr') (by addr')
    (fun h => hYL' (by rw [h]; simp [Lvars])) (fun h => hYL' (by rw [h]; simp [Lvars]))
    (by addr') (by addr') (fun m hm => ⟨(hrecX m hm.1 hm.2).1, (hwf m hm.1).2.2.1⟩)
  have hany := anyM_spec L D n ht (by omega) ?_ hD ?_ hDL hDF ?_ hctx ?_ hPre ?_
  · refine hany.congr (fun m hm => ?_)
    obtain ⟨⟨hDIN, hDwf, hDrec⟩, _, hYIN, hYwf⟩ := hwf m hm
    rw [mem_pairsAt_any]
    apply any_congr_mem
    intro q hq
    obtain ⟨hq1, hq2⟩ := hDrec q hq
    simp only [Mem.write_same, Mem.write_ne _ _ hYX, Mem.write_ne _ _ (show q ≠ X_ L by addr'),
      Mem.write_ne _ _ (show q + 1 ≠ X_ L by addr'), Mem.write_ne _ _ (show m Y ≠ X_ L by addr'),
      Mem.write_ne _ _ (show m Y + 1 ≠ X_ L by addr')]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> constructor <;> addr'
  · intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h
    · exact hDL' (by rw [h]; simp [Lvars])
    · exact hDL' (by rw [h]; simp [Lvars])
    · exact hDF h
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hX1
    · exact hP1
    · simp [LvarsX, FLAG, I_, CNT_, PTR_, CONT_, OUT_]; omega
  · intro m hm
    obtain ⟨⟨hDIN, hDwf, _⟩, hn, _, _⟩ := hwf m hm
    exact ⟨hDIN, hDwf, hn⟩
  · -- stability of the test's value
    intro m m' hm hmem hag
    obtain ⟨⟨hDIN, hDwf, hDrec⟩, _, hYIN, hYwf⟩ := hwf m hm
    obtain ⟨hXIN, hXwf⟩ := hrecX m hm hmem
    have hV : ∀ x, x ∈ LvarsX L ++ FLAG :: [X_ (L + 1), PTR_ (L + 1), FLAG] → x < IN := by
      intro x hx
      simp only [List.mem_append, List.mem_cons, LvarsX, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl <;> addr'
    have hhp := (hctx m hm).2.2
    have hYv : m' Y = m Y := hag.var Y (by omega) (by addr') (by
      simp only [List.mem_append, List.mem_cons, LvarsX, List.not_mem_nil, or_false, not_or]
      exact ⟨⟨fun h => hYL (by rw [h]; simp [Lvars]), fun h => hYL (by rw [h]; simp [Lvars]),
        fun h => hYL (by rw [h]; simp [Lvars]), fun h => hYL (by rw [h]; simp [Lvars]),
        fun h => hYL (by rw [h]; simp [Lvars])⟩, hYF, fun h => hYL' (by rw [h]; simp [Lvars]),
        fun h => hYL' (by rw [h]; simp [Lvars]), hYF⟩)
    have hXv : m' (X_ L) = m (X_ L) := hag.var (X_ L) (by addr') (by addr') (by
      simp only [List.mem_append, List.mem_cons, LvarsX, List.not_mem_nil, or_false, not_or]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> addr')
    simp only [hYv, hXv, hag.heap hV _ hXIN (by omega), hag.heap hV _ (by omega : IN ≤ m (X_ L) + 1) (by omega),
      hag.heap hV _ hYIN (by omega), hag.heap hV _ (by omega : IN ≤ m Y + 1) (by omega)]


/-! ### `dedupList` on arrays of records -/

theorem dedupList_cons' {α : Type} [DecidableEq α] (x : α) (l : List α) :
    dedupList (x :: l) = if x ∈ dedupList l then dedupList l else x :: dedupList l := rfl

theorem dedupList_length_le {α : Type} [DecidableEq α] (l : List α) :
    (dedupList l).length ≤ l.length := by
  induction l with
  | nil => simp [dedupList]
  | cons x l ih =>
      rw [dedupList_cons']
      split_ifs
      · simp; omega
      · simp; omega

/-- `dedupList` of the records (by value) of the array at `SRC`; the result is a fresh array
of the same record pointers (address in `OUT_ L`). -/
def dedupM (L SRC : ℕ) : Cmd :=
  .seq (load (CNT_ L) SRC) (.seq (add (OUT_ L) HP (CNT_ L)) (.seq (store (OUT_ L) ZERO)
    (.seq (add HP (OUT_ L) ONE)
      (forEachRevM L SRC (.seq (memPairM (L + 1) (OUT_ L) (X_ L))
        (.ite (.eq FLAG ONE) nop (prependV L (X_ L))))))))

/-- The variables written by `dedupM L`. -/
def dedupV (L : ℕ) : List ℕ := Lvars L ++ memPairV (L + 1)

/-- The loop invariant of `dedupM`. -/
structure DedupInv (L : ℕ) (m0 : Mem) (src : ℕ) (l : List ℕ) (j : ℕ) (m : Mem) : Prop where
  agree : Agree m0 m (dedupV L)
  i : m (I_ L) = j
  cnt : m (CNT_ L) = l.length
  out : m0 HP ≤ m (OUT_ L) ∧ m (OUT_ L) + (arrAt m (m (OUT_ L))).length = m0 HP + l.length
  arr : pairsAt m (m (OUT_ L)) = dedupList ((pairsAt m0 src).drop (l.length - j))
  sub : ∀ q, q ∈ arrAt m (m (OUT_ L)) → q ∈ l
  room : m0 HP + l.length + 1 ≤ m HP

theorem dedupM_spec (L SRC n : ℕ) (hL : L + 2 ≤ 9) (hSRC : 5 ≤ SRC ∧ SRC < IN)
    (hSd : SRC ∉ dedupV L) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (hwf : ∀ m, Pre m → PairsWF m (m SRC) ∧ m (m SRC) ≤ n) :
    RSpec (dedupM L SRC) (dedupV L) (23 * n * n + 23 * n + 8) Pre
      (fun m m' => pairsAt m' (m' (OUT_ L)) = dedupList (pairsAt m (m SRC)) ∧
        PairsWF m' (m' (OUT_ L)) ∧ m HP ≤ m' (OUT_ L) ∧ (m' (OUT_ L) ∈ List.range (m HP + 1 + m (m SRC)))) := by
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  obtain ⟨⟨hsrc0, harr0, hrec0⟩, hn0⟩ := hwf m0 hm0
  obtain ⟨l, hl⟩ : ∃ l, arrAt m0 (m0 SRC) = l := ⟨_, rfl⟩
  obtain ⟨base, hbase⟩ : ∃ base, base = m0 HP := ⟨_, rfl⟩
  have hlen : l.length = m0 (m0 SRC) := by rw [← hl, arrAt_length]
  have hbaseIN : IN ≤ base := by rw [hbase]; exact hhp0
  have hLv : ∀ x, x ∈ dedupV L → x < IN := by
    intro x hx
    simp only [dedupV, List.mem_append] at hx
    rcases hx with h | h
    · exact (Lvars_range L (by omega) x h).2
    · exact (memPairV_range (L + 1) (by omega) x h).2
  have hL5 : ∀ x, x ∈ dedupV L → 5 ≤ x := by
    intro x hx
    simp only [dedupV, List.mem_append] at hx
    rcases hx with h | h
    · have := (Lvars_range L (by omega) x h).1; omega
    · exact (memPairV_range (L + 1) (by omega) x h).1
  have hSL : SRC ∉ Lvars L := fun h => hSd (by simp only [dedupV, List.mem_append]; exact Or.inl h)
  have hSC : SRC ≠ CNT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hSO : SRC ≠ OUT_ L := fun h => hSL (by rw [h]; simp [Lvars])
  have hpairs : pairsAt m0 (m0 SRC) = l.map (fun q => (m0 q, m0 (q + 1))) := by
    unfold pairsAt; rw [hl]
  -- setup
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write (CNT_ L) l.length := ⟨_, rfl⟩
  have e1 : Cmd.Exec (load (CNT_ L) SRC) m0 m1 1 := by
    have := Exec.load (CNT_ L) SRC m0; rwa [← hlen, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (OUT_ L) (base + l.length) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add (OUT_ L) HP (CNT_ L)) m1 m2 1 := by
    have := Exec.add (OUT_ L) HP (CNT_ L) m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr'), ← hbase] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (base + l.length) 0 := ⟨_, rfl⟩
  have e3 : Cmd.Exec (store (OUT_ L) ZERO) m2 m3 1 := by
    have := Exec.store (OUT_ L) ZERO m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hzero0] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write HP (base + l.length + 1) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add HP (OUT_ L) ONE) m3 m4 1 := by
    have := Exec.add HP (OUT_ L) ONE m3
    rw [hm3, Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hm2, Mem.write_same,
      Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr'), hone0] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  have q4 : ∀ x, x ≠ HP → x ≠ base + l.length → x ≠ OUT_ L → x ≠ CNT_ L → m4 x = m0 x :=
    fun x h1 h2 h3 h4 => by
      rw [hm4, Mem.write_ne _ _ h1, hm3, Mem.write_ne _ _ h2, hm2, Mem.write_ne _ _ h3, hm1,
        Mem.write_ne _ _ h4]
  have m4HP : m4 HP = base + l.length + 1 := by rw [hm4, Mem.write_same]
  have m4O : m4 (OUT_ L) = base + l.length := by
    rw [hm4, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
  have m4hdr : m4 (base + l.length) = 0 := by
    rw [hm4, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
  have agree4 : Agree m0 m4 (dedupV L) := by
    refine ⟨fun x hx hxV => ?_, by rw [m4HP]; omega⟩
    have hxV' := hxV
    simp only [List.mem_cons, dedupV, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hxV'
    exact q4 x hxV'.1 (by omega) hxV'.2.1.2.2.2.2.2 hxV'.2.1.2.1
  -- facts about the source array, stable under the loop
  have hsrcv : ∀ m, Agree m0 m (dedupV L) → m SRC = m0 SRC := fun m hag =>
    hag.var SRC (by addr') (by addr') hSd
  have hcellv : ∀ m, Agree m0 m (dedupV L) → ∀ i, (h : i < l.length) → m (m0 SRC + 1 + i) = l[i] := by
    intro m hag i hi
    rw [hag.heap hLv _ (by omega) (by omega),
      ← arrAt_getElem m0 (m0 SRC) i (by rw [arrAt_length, ← hlen]; exact hi)]
    exact List.getElem_of_eq hl _
  have hql : ∀ q, q ∈ l → IN ≤ q ∧ q + 2 ≤ m0 HP := fun q hq => hrec0 q (by rw [hl]; exact hq)
  have hrecv : ∀ m, Agree m0 m (dedupV L) → ∀ q, q ∈ l → m q = m0 q ∧ m (q + 1) = m0 (q + 1) :=
    fun m hag q hq => ⟨hag.heap hLv q (hql q hq).1 (by have := hql q hq; omega),
      hag.heap hLv (q + 1) (by have := hql q hq; omega) (by have := hql q hq; omega)⟩
  -- the loop
  have main := forEachRevM_spec L SRC (by omega) hSRC.2 hSL
    (.seq (memPairM (L + 1) (OUT_ L) (X_ L)) (.ite (.eq FLAG ONE) nop (prependV L (X_ L))))
    (DedupInv L m0 (m0 SRC) l) (m0 SRC) hsrc0 l (n * 23 + 17) ?_ ?_ ?_ m4
    (hsrcv m4 agree4) (by rw [q4 (m0 SRC) (by addr') (by omega) (by addr') (by addr'), hlen]) ?_
  · obtain ⟨m', k, e, inv', hk⟩ := main
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e))), ?_,
      inv'.agree, ?_⟩
    · have h1 : l.length * (n * 23 + 17 + 6) ≤ n * (n * 23 + 23) := Nat.mul_le_mul_right _ (by omega)
      have h2 : n * (n * 23 + 23) = 23 * n * n + 23 * n := by ring
      omega
    · obtain ⟨hag, hi, hcnt, ⟨hout1, hout2⟩, harr, hsub, hroom⟩ := inv'
      have hlen' := arrAt_length m' (m' (OUT_ L))
      refine ⟨by rw [harr, Nat.sub_self, List.drop_zero], ⟨by omega, by omega, ?_⟩, by omega, ?_⟩
      · intro q hq
        have := hql q (hsub q hq)
        exact ⟨this.1, le_trans this.2 hag.2⟩
      · rw [List.mem_range, ← hlen]
        omega
  · -- hI
    intro j m hm
    obtain ⟨hag, hi, hcnt, hout, harr, hsub, hroom⟩ := hm
    refine ⟨hi, hcnt, hsrcv m hag, ?_, ?_, hcellv m hag⟩
    · rw [hag.var ONE (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hone0]
    · exact le_trans (by rw [hlen]; exact harr0) hag.2
  · -- hstable
    intro j m v w hm
    obtain ⟨hag, hi, hcnt, hout, harr, hsub, hroom⟩ := hm
    have hag' : Agree m ((m.write (PTR_ L) v).write (X_ L) w) [PTR_ L, X_ L] := by
      refine ⟨fun y _ hy => ?_, by rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [Mem.write_ne _ _ hy.2.2, Mem.write_ne _ _ hy.2.1]
    have hw : ∀ x, IN ≤ x → ((m.write (PTR_ L) v).write (X_ L) w) x = m x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    have hO : ((m.write (PTR_ L) v).write (X_ L) w) (OUT_ L) = m (OUT_ L) := by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    have hA : arrAt ((m.write (PTR_ L) v).write (X_ L) w) (m (OUT_ L)) = arrAt m (m (OUT_ L)) :=
      arrAt_congr (fun x h1 h2 => hw x (by omega))
    refine ⟨(hag.trans hag').mono (by
        intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
        · exact h
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl <;> simp [dedupV, Lvars]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hi]
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), hcnt]
    · rw [hO, hA]; exact hout
    · rw [hO, ← harr]
      refine pairsAt_congr hA (fun q hq => ?_)
      have := hql q (hsub q hq)
      exact ⟨hw q this.1, hw (q + 1) (by omega)⟩
    · rw [hO, hA]; exact hsub
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact hroom
  · -- hbody
    intro j m hj hm hx _
    obtain ⟨hag, hi, hcnt, ⟨hout1, hout2⟩, harr, hsub, hroom⟩ := hm
    obtain ⟨q, hq⟩ : ∃ q, q = l[l.length - 1 - j] := ⟨_, rfl⟩
    rw [← hq] at hx
    have hqmem : q ∈ l := by rw [hq]; exact List.getElem_mem _
    obtain ⟨hqIN, hqwf⟩ := hql q hqmem
    have hhp : m0 HP ≤ m HP := hag.2
    have hone : m ONE = 1 := by
      rw [hag.var ONE (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hone0]
    obtain ⟨S, hS⟩ : ∃ S, S = m (OUT_ L) := ⟨_, rfl⟩
    rw [← hS] at hout1 hout2 harr hsub
    have hdlen : (arrAt m S).length ≤ j := by
      have h1 : (pairsAt m S).length = (arrAt m S).length := by simp [pairsAt]
      rw [← h1, harr]
      refine le_trans (dedupList_length_le _) ?_
      rw [List.length_drop, hpairs, List.length_map]; omega
    have hSlen : m S = (arrAt m S).length := (arrAt_length m S).symm
    -- the membership test
    have hmem := memPairM_spec (L + 1) (OUT_ L) (X_ L) n (by omega) (by constructor <;> addr')
      (by constructor <;> addr') (by simp [Lvars, OUT_, I_, CNT_, PTR_, CONT_, X_]; omega)
      (by simp [Lvars, OUT_, I_, CNT_, PTR_, CONT_, X_]; omega)
      (by simp [Lvars, X_, I_, CNT_, PTR_, CONT_, OUT_]; omega)
      (by simp [Lvars, X_, I_, CNT_, PTR_, CONT_, OUT_]; omega) (by addr') (by addr')
      (fun m' => Ctx m' ∧ PairsWF m' (m' (OUT_ L)) ∧ m' (m' (OUT_ L)) ≤ n ∧ IN ≤ m' (X_ L) ∧
        m' (X_ L) + 2 ≤ m' HP) (fun m' hm' => hm'.1) (fun m' hm' => hm'.2) ?_ m
      ⟨⟨hone, by rw [hag.var ZERO (by addr') (by addr') (fun h => by have := hL5 _ h; addr'), hzero0],
        by omega⟩, ⟨by rw [← hS]; omega, by rw [← hS]; omega, fun q' hq' => by
          have := hql q' (hsub q' (by rw [hS]; exact hq'))
          exact ⟨this.1, by omega⟩⟩,
        by rw [← hS]; omega, by rw [hx]; exact hqIN, by rw [hx]; omega⟩
    · obtain ⟨m1, k1, f1, hk1, ag1, hfl1⟩ := hmem
      dsimp only at hfl1
      have hVlt1 : ∀ x, x ∈ memPairV (L + 1) → x < IN := fun x hx => (memPairV_range (L + 1) (by omega) x hx).2
      have hV5_1 : ∀ x, x ∈ memPairV (L + 1) → 5 ≤ x := fun x hx => (memPairV_range (L + 1) (by omega) x hx).1
      have hnotL : ∀ x, x ∈ Lvars L → x ∉ memPairV (L + 1) := by
        intro x hx h
        simp only [memPairV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        simp only [Lvars, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases h with h | h | h | h | h
        · simp only [Lvars, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h | h | h | h | h <;>
            simp [I_, CNT_, PTR_, CONT_, X_, OUT_] at h <;> omega
        all_goals (rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [I_, CNT_, PTR_, CONT_, X_, OUT_, FLAG] at h <;> omega)
      have v1 : ∀ x, x ∈ Lvars L → m1 x = m x := fun x hx =>
        ag1.var x (by have := (Lvars_range L (by omega) x hx).2; omega)
          (by have := (Lvars_range L (by omega) x hx).1; addr') (hnotL x hx)
      have m1one : m1 ONE = 1 := by
        rw [ag1.var ONE (by addr') (by addr') (fun h => by have := hV5_1 _ h; addr'), hone]
      have m1S : m1 (OUT_ L) = S := by rw [v1 _ (by simp [Lvars]), hS]
      have m1X : m1 (X_ L) = q := by rw [v1 _ (by simp [Lvars]), hx]
      have m1I : m1 (I_ L) = j := by rw [v1 _ (by simp [Lvars]), hi]
      have m1C : m1 (CNT_ L) = l.length := by rw [v1 _ (by simp [Lvars]), hcnt]
      have m1arr : arrAt m1 S = arrAt m S := ag1.arrAt hVlt1 S (by omega) (by omega)
      have m1pairs : pairsAt m1 S = pairsAt m S := ag1.pairsAt hVlt1 S (by omega) (by omega)
        (fun q' hq' => by have := hql q' (hsub q' hq'); exact ⟨this.1, by omega⟩)
      have m1rec : m1 q = m0 q ∧ m1 (q + 1) = m0 (q + 1) := by
        obtain ⟨r1, r2⟩ := hrecv m hag q hqmem
        exact ⟨by rw [ag1.heap hVlt1 q hqIN (by omega), r1],
          by rw [ag1.heap hVlt1 (q + 1) (by omega) (by omega), r2]⟩
      have hp : (m q, m (q + 1)) = (pairsAt m0 (m0 SRC))[l.length - 1 - j]'(by
          rw [hpairs, List.length_map]; omega) := by
        obtain ⟨r1, r2⟩ := hrecv m hag q hqmem
        rw [r1, r2]
        simp only [hpairs, List.getElem_map, hq]
      have hdrop : (pairsAt m0 (m0 SRC)).drop (l.length - (j + 1)) =
          (pairsAt m0 (m0 SRC))[l.length - 1 - j]'(by rw [hpairs, List.length_map]; omega) ::
            (pairsAt m0 (m0 SRC)).drop (l.length - j) := by
        rw [show l.length - (j + 1) = l.length - 1 - j by omega,
          List.drop_eq_getElem_cons (by rw [hpairs, List.length_map]; omega),
          show l.length - 1 - j + 1 = l.length - j by omega]
      rw [← hS, hx, harr, hp] at hfl1
      have hagree' : ∀ m2, Agree m1 m2 [OUT_ L, CONT_ L, S, S - 1] → (∀ x, x < m0 HP → x ≠ OUT_ L → x ≠ CONT_ L → m2 x = m1 x) →
          Agree m0 (m2.write (I_ L) (j + 1)) (dedupV L) := by
        intro m2 hag2 hfr
        refine ⟨fun y hy hyV => ?_, ?_⟩
        · have hyV' := hyV
          simp only [List.mem_cons, dedupV, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
          rw [Mem.write_ne _ _ hyV'.2.1.1, hfr y hy hyV'.2.1.2.2.2.2.2 hyV'.2.1.2.2.2.1,
            ag1.var y (by omega) hyV'.1 hyV'.2.2]
          exact hag.1 y hy hyV
        · rw [Mem.write_ne _ _ (by addr')]; exact le_trans hhp (le_trans ag1.2 hag2.2)
      by_cases hin : (pairsAt m0 (m0 SRC))[l.length - 1 - j]'(by rw [hpairs, List.length_map]; omega) ∈
        dedupList ((pairsAt m0 (m0 SRC)).drop (l.length - j))
      · -- already present
        rw [decide_eq_true hin] at hfl1
        have hc : (Cond.eq FLAG ONE).eval m1 = true := by simp [Cond.eval, hfl1, m1one]
        refine ⟨m1, _, Cmd.Exec.seq f1 (Cmd.Exec.ite_true hc (Exec.nop m1)), by omega, m1I, m1one, ?_⟩
        have hw : ∀ x, IN ≤ x → (m1.write (I_ L) (j + 1)) x = m1 x := fun x hx => by
          rw [Mem.write_ne _ _ (by addr')]
        have hA1 : arrAt (m1.write (I_ L) (j + 1)) S = arrAt m1 S :=
          arrAt_congr (fun x h1 h2 => hw x (by omega))
        have hA : arrAt (m1.write (I_ L) (j + 1)) S = arrAt m S := by rw [hA1, m1arr]
        refine ⟨hagree' m1 (Agree.refl _ _) (fun x _ _ _ => rfl), by rw [Mem.write_same],
          by rw [Mem.write_ne _ _ (by addr'), m1C], ?_, ?_, ?_, ?_⟩
        · rw [Mem.write_ne _ _ (by addr'), m1S, hA]; exact ⟨hout1, hout2⟩
        · rw [Mem.write_ne _ _ (by addr'), m1S, hdrop, dedupList_cons', if_pos hin, ← harr, ← m1pairs]
          refine pairsAt_congr hA1 (fun q' hq' => ?_)
          have := hql q' (hsub q' (by rw [← m1arr]; exact hq'))
          exact ⟨hw q' this.1, hw (q' + 1) (by omega)⟩
        · rw [Mem.write_ne _ _ (by addr'), m1S, hA]; exact hsub
        · rw [Mem.write_ne _ _ (by addr')]; exact le_trans hroom ag1.2
      · -- prepend
        rw [decide_eq_false hin] at hfl1
        have hc : (Cond.eq FLAG ONE).eval m1 = false := by simp [Cond.eval, hfl1, m1one]
        have hSgt : base + 1 ≤ S := by omega
        obtain ⟨m2, k2, f2, hk2, fr2, m2O, m2hdr, m2S⟩ := prependV_spec L (X_ L) (by omega) (by addr')
          (by addr') (by addr') m1 S m1S m1one (by omega)
        have hw : ∀ x, IN ≤ x → x ≠ S → x ≠ S - 1 → (m2.write (I_ L) (j + 1)) x = m1 x := fun x hx h1 h2 => by
          rw [Mem.write_ne _ _ (by addr'), fr2 x (by addr') (by addr') h1 h2]
        have hA : arrAt (m2.write (I_ L) (j + 1)) (S - 1) = q :: arrAt m S := by
          rw [← m1arr]
          refine arrAt_prepend (m := m1) (by omega) ?_ ?_ ?_
          · rw [Mem.write_ne _ _ (by addr'), m2hdr]
          · rw [Mem.write_ne _ _ (by addr'), m2S, m1X]
          · intro i hi'; exact hw _ (by omega) (by omega) (by omega)
        have hO : (m2.write (I_ L) (j + 1)) (OUT_ L) = S - 1 := by
          rw [Mem.write_ne _ _ (by addr'), m2O]
        refine ⟨m2, _, Cmd.Exec.seq f1 (Cmd.Exec.ite_false hc f2), by omega,
          by rw [fr2 _ (by addr') (by addr') (by addr') (by addr'), m1I],
          by rw [fr2 _ (by addr') (by addr') (by addr') (by addr'), m1one], ?_⟩
        refine ⟨hagree' m2 ⟨fun y _ hy => ?_, by rw [fr2 HP (by addr') (by addr') (by addr') (by addr')]⟩
          (fun x hx h1 h2 => fr2 x h2 h1 (by omega) (by omega)), by rw [Mem.write_same],
          by rw [Mem.write_ne _ _ (by addr'), fr2 _ (by addr') (by addr') (by addr') (by addr'), m1C],
          ?_, ?_, ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          exact fr2 y hy.2.2.1 hy.2.1 hy.2.2.2.1 hy.2.2.2.2
        · rw [hO, hA, List.length_cons]; constructor <;> omega
        · rw [hO, hdrop, dedupList_cons', if_neg hin, ← harr, ← hp]
          unfold pairsAt
          rw [hA, List.map_cons]
          congr 1
          · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'),
              fr2 q (by addr') (by addr') (by omega) (by omega),
              fr2 (q + 1) (by addr') (by addr') (by omega) (by omega),
              ag1.heap hVlt1 q hqIN (by omega), ag1.heap hVlt1 (q + 1) (by omega) (by omega)]
          · apply List.map_congr_left
            intro q' hq'
            have := hql q' (hsub q' hq')
            rw [hw q' this.1 (by omega) (by omega), hw (q' + 1) (by omega) (by omega) (by omega),
              ag1.heap hVlt1 q' this.1 (by omega), ag1.heap hVlt1 (q' + 1) (by omega) (by omega)]
        · rw [hO, hA]
          intro q' hq'
          simp only [List.mem_cons] at hq'
          rcases hq' with rfl | hq'
          · exact hqmem
          · exact hsub q' hq'
        · rw [Mem.write_ne _ _ (by addr'), fr2 HP (by addr') (by addr') (by addr') (by addr')]
          exact le_trans hroom ag1.2
    · -- stability of the test's precondition
      intro m' m'' hm' hag'
      obtain ⟨hctx', ⟨hOIN, hOwf, hOrec⟩, hOn, hXIN, hXwf⟩ := hm'
      have hV' : ∀ x, x ∈ memPairV (L + 1) → x < IN := fun x hx => (memPairV_range (L + 1) (by omega) x hx).2
      have hV5' : ∀ x, x ∈ memPairV (L + 1) → 5 ≤ x := fun x hx => (memPairV_range (L + 1) (by omega) x hx).1
      have hOv : m'' (OUT_ L) = m' (OUT_ L) := hag'.var (OUT_ L) (by have := hctx'.2.2; addr') (by addr') (by
        intro h
        simp only [memPairV, Lvars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          OUT_, I_, CNT_, PTR_, CONT_, X_, FLAG] at h
        omega)
      have hXv : m'' (X_ L) = m' (X_ L) := hag'.var (X_ L) (by have := hctx'.2.2; addr') (by addr') (by
        intro h
        simp only [memPairV, Lvars, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          OUT_, I_, CNT_, PTR_, CONT_, X_, FLAG] at h
        omega)
      refine ⟨hctx'.of_agree hag' hV5', ⟨by rw [hOv]; exact hOIN, ?_, ?_⟩, ?_, by rw [hXv]; exact hXIN,
        by rw [hXv]; exact le_trans hXwf hag'.2⟩
      · rw [hOv, hag'.heap hV' _ hOIN (by omega)]; exact le_trans hOwf hag'.2
      · rw [hOv]
        exact (hOrec.of_agree hag' hV' hOIN hOwf).mono le_rfl hag'.2
      · rw [hOv, hag'.heap hV' _ hOIN (by omega)]; exact hOn
  · -- the initial invariant
    have hw : ∀ x, IN ≤ x → ((m4.write (CNT_ L) l.length).write (I_ L) 0) x = m4 x := fun x hx => by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]
    have hO : ((m4.write (CNT_ L) l.length).write (I_ L) 0) (OUT_ L) = base + l.length := by
      rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m4O]
    have hA : arrAt ((m4.write (CNT_ L) l.length).write (I_ L) 0) (base + l.length) = [] := by
      simp only [arrAt, hw (base + l.length) (by omega), m4hdr, List.range_zero, List.map_nil]
    refine ⟨?_, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr'), Mem.write_same], ?_, ?_, ?_, ?_⟩
    · refine ⟨fun y hy hyV => ?_, ?_⟩
      · have hyV' := hyV
        simp only [List.mem_cons, dedupV, List.mem_append, Lvars, List.not_mem_nil, or_false, not_or] at hyV'
        rw [Mem.write_ne _ _ hyV'.2.1.1, Mem.write_ne _ _ hyV'.2.1.2.1]
        exact agree4.1 y hy hyV
      · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr')]; exact agree4.2
    · rw [hO, hA]; simp; omega
    · rw [hO, Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hpairs, List.length_map])]
      simp only [pairsAt, hA, List.map_nil]; rfl
    · rw [hO, hA]; intro q hq; simp at hq
    · rw [Mem.write_ne _ _ (by addr'), Mem.write_ne _ _ (by addr'), m4HP]; omega

end DisequalityDispersion.Machine
