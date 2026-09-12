import MLib2

/-! # Array routines, part 3: `all`, index-based loops, global variables -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### Global variables of the decision procedure (addresses `100 … 199`) -/

def KV : ℕ := 100
def BASE : ℕ := 101
def SRCS : ℕ := 102
def SYMS : ℕ := 103
def NODES : ℕ := 104
def XV : ℕ := 105
def YV : ℕ := 106
def TV : ℕ := 107
def TESTS : ℕ := 108
def OUTS : ℕ := 109
def NN : ℕ := 110
def KK : ℕ := 111
def MM : ℕ := 112
def IDS : ℕ := 113
def RESV : ℕ := 114
/-- Range arrays of index loops, one per level. -/
def RNG (L : ℕ) : ℕ := 120 + L
/-- General-purpose globals. -/
def G_ (i : ℕ) : ℕ := 130 + i

theorem KV_eq : KV = 100 := rfl
theorem BASE_eq : BASE = 101 := rfl
theorem SRCS_eq : SRCS = 102 := rfl
theorem SYMS_eq : SYMS = 103 := rfl
theorem NODES_eq : NODES = 104 := rfl
theorem XV_eq : XV = 105 := rfl
theorem YV_eq : YV = 106 := rfl
theorem TV_eq : TV = 107 := rfl
theorem TESTS_eq : TESTS = 108 := rfl
theorem OUTS_eq : OUTS = 109 := rfl
theorem NN_eq : NN = 110 := rfl
theorem KK_eq : KK = 111 := rfl
theorem MM_eq : MM = 112 := rfl
theorem IDS_eq : IDS = 113 := rfl
theorem RESV_eq : RESV = 114 := rfl

/-- Decide (in)equalities between fixed addresses, including the globals. -/
macro "addr3" : tactic => `(tactic| (first | omega | (simp only [A_, NEL, JJ, CC, I_, CNT_, PTR_,
  CONT_, X_, OUT_, RNG, G_, FLAG_eq, V2_eq, IN_eq', HP_eq', ONE_eq', POS_eq, OK_eq, VAL_eq, TMP_eq,
  N_eq, INB_eq, ZERO_eq, CNT_eq, POW_eq, PTR_eq, LAST_eq, BIT_eq, J_eq, CONT_eq, KV_eq, BASE_eq,
  SRCS_eq, SYMS_eq, NODES_eq, XV_eq, YV_eq, TV_eq, TESTS_eq, OUTS_eq, NN_eq, KK_eq, MM_eq, IDS_eq,
  RESV_eq] at * <;> omega)))

/-- Like `addr3`, but rewriting only the goal (cheap in large contexts; hypotheses about
addresses must then be stated with the numeral `200` for `IN`). -/
macro "addrg" : tactic => `(tactic| (first | omega | (simp only [A_, NEL, JJ, CC, I_, CNT_, PTR_,
  CONT_, X_, OUT_, RNG, G_, FLAG_eq, V2_eq, IN_eq', HP_eq', ONE_eq', POS_eq, OK_eq, VAL_eq, TMP_eq,
  N_eq, INB_eq, ZERO_eq, CNT_eq, POW_eq, PTR_eq, LAST_eq, BIT_eq, J_eq, CONT_eq, KV_eq, BASE_eq,
  SRCS_eq, SYMS_eq, NODES_eq, XV_eq, YV_eq, TV_eq, TESTS_eq, OUTS_eq, NN_eq, KK_eq, MM_eq, IDS_eq,
  RESV_eq] <;> omega)))

/-! ### `all` -/

/-- `allM L SRC t`: do all elements of the array at `SRC` satisfy `t`? -/
def allM (L SRC : ℕ) (t : Cmd) : Cmd := notM (anyM L SRC (notM t))

theorem allM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool} (L SRC n : ℕ)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) P) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hSF : SRC ≠ FLAG) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L)
    (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ FLAG :: V))
    (hP : StableX Pre SRC L P (LvarsX L ++ FLAG :: V)) :
    TestSpec (allM L SRC t) (FLAG :: (Lvars L ++ FLAG :: (FLAG :: V))) (n * (B + 12) + 11) Pre
      (fun m => (arrAt m (m SRC)).all (fun x => P (m.write (X_ L) x))) := by
  have hnot : TestSpec (notM t) (FLAG :: V) (B + 1) (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC))
      (fun m => !P m) :=
    notM_spec ht (fun x hx => (hV x hx).1) (fun m hm => hctx m hm.1)
  have hany := anyM_spec L SRC n hnot hL (by
      intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
      · constructor <;> addr'
      · exact hV x hx)
    hSRC (by simp only [List.mem_cons, not_or]; exact ⟨hSF, hSV⟩) hSL hSF (by
      intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
      · simp [LvarsX, FLAG, I_, CNT_, PTR_, CONT_, OUT_]; omega
      · exact hVL x hx)
    hctx harr (hPre.mono (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))
    (fun m m' hm hx ha => by rw [hP m m' hm hx (ha.mono (by
      intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))])
  have hres := notM_spec hany (by
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · have := (Lvars_range L hL x hx).1; omega
      · addr'
      · addr'
      · exact (hV x hx).1) hctx
  have hB : n * (B + 1 + 11) + 10 + 1 ≤ n * (B + 12) + 11 := by
    have : n * (B + 1 + 11) = n * (B + 12) := by ring
    omega
  refine (hres.mono (fun x hx => hx) hB (fun m hm => hm)).congr (fun m hm => ?_)
  rw [List.all_eq_not_any_not]

/-! ### Index-based loops -/

/-- `anyRangeM L N t`: does some index `i < M[N]` satisfy `t` (run with `i` in `X_ L`)? -/
def anyRangeM (L N : ℕ) (t : Cmd) : Cmd :=
  .seq (rangeM (L + 1) N) (.seq (mov (RNG L) (OUT_ (L + 1))) (anyM L (RNG L) t))

/-- The variables written by `anyRangeM L` besides those of the test. -/
def rangeV (L : ℕ) : List ℕ := Lvars (L + 1) ++ RNG L :: Lvars L

/-- The variables written by `anyRangeM L` before the scan (the test's value must not depend
on them). -/
def rangeVX (L : ℕ) : List ℕ := Lvars (L + 1) ++ [RNG L]

theorem anyRangeM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool}
    (L N n : ℕ) (hL : L + 1 ≤ 9)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) < m N) P)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hN : 5 ≤ N ∧ N < IN) (hNV : N ∉ V)
    (hNL : N ∉ Lvars L) (hNL' : N ∉ Lvars (L + 1)) (hNF : N ≠ FLAG) (hNR : N ≠ RNG L)
    (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hVR : RNG L ∉ V)
    (hctx : ∀ m, Pre m → Ctx m) (hn : ∀ m, Pre m → m N ≤ n)
    (hPre : StableP Pre (rangeV L ++ FLAG :: V))
    (hP : Stable (fun m => Pre m ∧ m (X_ L) < m N) P (LvarsX L ++ FLAG :: V ++ rangeVX L)) :
    TestSpec (anyRangeM L N t) (rangeV L ++ FLAG :: V) (n * (B + 11) + n * 6 + 20) Pre
      (fun m => (List.range (m N)).any (fun i => P (m.write (X_ L) i))) := by
  intro m0 hm0
  dsimp only
  obtain ⟨hone0, hzero0, hhp0⟩ := hctx m0 hm0
  have hn0 := hn m0 hm0
  have hL1 := Lvars_range (L + 1) hL
  have hL0 := Lvars_range L (by omega)
  have hRL : RNG L ∉ Lvars L := by simp [Lvars, RNG, I_, CNT_, PTR_, CONT_, X_, OUT_]; omega
  have hRL' : RNG L ∉ Lvars (L + 1) := by simp [Lvars, RNG, I_, CNT_, PTR_, CONT_, X_, OUT_]; omega
  -- the range array
  obtain ⟨m1, k1, e1, hk1, ag1, hout1, harr1, hhp1⟩ := rangeM_spec (L + 1) N n hL hN hNL' Pre hctx hn m0 hm0
  have m1N : m1 N = m0 N := ag1.var N (by addr3) (by addr3) hNL'
  have m1one : m1 ONE = 1 := by rw [ag1.var ONE (by addr3) (by addr3) (fun h => by have := (hL1 _ h).1; addr3), hone0]
  -- copy the pointer
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (RNG L) (m0 HP) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (mov (RNG L) (OUT_ (L + 1))) m1 m2 1 := by
    have := Exec.mov (RNG L) (OUT_ (L + 1)) m1; rwa [hout1, ← hm2] at this
  have q2 : ∀ x, x ≠ RNG L → m2 x = m1 x := fun x hx => by rw [hm2, Mem.write_ne _ _ hx]
  have ag12 : Agree m1 m2 [RNG L] := by rw [hm2]; exact Agree.write m1 (RNG L) _ (by addr3)
  have ag2 : Agree m0 m2 (Lvars (L + 1) ++ [RNG L]) := ag1.trans ag12
  have hag2 : Agree m0 m2 (rangeV L ++ FLAG :: V) := ag2.mono (by
    intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, rangeV] at hx ⊢; tauto)
  have hpre2 : Pre m2 := hPre m0 m2 hm0 hag2
  have m2R : m2 (RNG L) = m0 HP := by rw [hm2, Mem.write_same]
  have m2arr : arrAt m2 (m0 HP) = List.range (m0 N) := by
    rw [← harr1]; exact arrAt_congr (fun x h1 h2 => q2 x (by addr3))
  have m2HP : m0 HP + 1 + m0 N ≤ m2 HP := by rw [q2 HP (by addr3)]; exact hhp1
  have m2N : m2 N = m0 N := by rw [q2 N hNR, m1N]
  -- the scan, with the precondition strengthened by the range array
  obtain ⟨Pre', hPd⟩ : ∃ Pre' : Mem → Prop, ∀ m, Pre' m ↔ (Pre m ∧ m (RNG L) = m0 HP ∧
      arrAt m (m0 HP) = List.range (m0 N) ∧ m0 HP + 1 + m0 N ≤ m HP ∧ m N = m0 N) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hVlt : ∀ x, x ∈ Lvars L ++ FLAG :: V → x < IN := by
    intro x hx; simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | rfl | h
    · exact (hL0 x h).2
    · addr3
    · exact (hV x h).2
  have ht' : TestSpec t V B (fun m => Pre' m ∧ m (X_ L) ∈ arrAt m (m (RNG L))) P := by
    refine ht.mono (fun x hx => hx) le_rfl (fun m hm => ?_)
    obtain ⟨hpre, hR, harr, hhp, hN'⟩ := (hPd m).1 hm.1
    have hx := hm.2
    rw [hR, harr, List.mem_range] at hx
    exact ⟨hpre, by rw [hN']; exact hx⟩
  have harr' : ∀ m, Pre' m → IN ≤ m (RNG L) ∧ m (RNG L) + 1 + m (m (RNG L)) ≤ m HP ∧ m (m (RNG L)) ≤ n := by
    intro m hm
    obtain ⟨_, hR, harr, hhp, _⟩ := (hPd m).1 hm
    have hl := congrArg List.length harr
    rw [arrAt_length, List.length_range] at hl
    rw [hR]
    exact ⟨hhp0, by omega, by omega⟩
  have hPre' : StableP Pre' (Lvars L ++ FLAG :: V) := by
    intro m m' hm ha
    obtain ⟨hpre, hR, harr, hhp, hN'⟩ := (hPd m).1 hm
    have ha' : Agree m m' (rangeV L ++ FLAG :: V) := ha.mono (by
      intro x hx; simp only [List.mem_append, List.mem_cons, rangeV] at hx ⊢; tauto)
    have hl := congrArg List.length harr
    rw [arrAt_length, List.length_range] at hl
    refine (hPd m').2 ⟨hPre m m' hpre ha', ?_, ?_, le_trans hhp ha.2, ?_⟩
    · rw [ha.var (RNG L) (by have := (hctx m hpre).2.2; addr3) (by addr3) (by
        simp only [List.mem_append, List.mem_cons, not_or]; exact ⟨hRL, by addr3, hVR⟩), hR]
    · rw [ha.arrAt hVlt (m0 HP) hhp0 (by omega), harr]
    · rw [ha.var N (by have := (hctx m hpre).2.2; addr3) (by addr3) (by
        simp only [List.mem_append, List.mem_cons, not_or]; exact ⟨hNL, hNF, hNV⟩), hN']
  have hP' : StableX Pre' (RNG L) L P (LvarsX L ++ FLAG :: V) := by
    intro m m' hm hx ha
    obtain ⟨hpre, hR, harr, hhp, hN'⟩ := (hPd m).1 hm
    rw [hR, harr, List.mem_range] at hx
    exact hP m m' ⟨hpre, by rw [hN']; exact hx⟩ (ha.mono (by
      intro x hx; simp only [List.mem_append, List.mem_cons, rangeV] at hx ⊢; tauto))
  have hany := anyM_spec (Pre := Pre') L (RNG L) n ht' (by omega) hV (by constructor <;> addr3) hVR hRL
    (by addr3) hVL (fun m hm => hctx m ((hPd m).1 hm).1) harr' hPre' hP' m2
    ((hPd m2).2 ⟨hpre2, m2R, m2arr, m2HP, m2N⟩)
  obtain ⟨m3, k3, e3, hk3, ag3, hfl3⟩ := hany
  have hsub : ∀ x, x ∈ (rangeV L ++ FLAG :: V) ++ (Lvars L ++ FLAG :: V) → x ∈ rangeV L ++ FLAG :: V := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hx
    · rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (by simp only [rangeV, List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hx))
      · exact Or.inr hx
  refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), by omega, (hag2.trans ag3).mono hsub, ?_⟩
  rw [hfl3]
  show bitv ((arrAt m2 (m2 (RNG L))).any fun x => P (m2.write (X_ L) x)) = _
  rw [m2R, m2arr]
  congr 1
  apply any_congr_mem
  intro i hi
  rw [List.mem_range] at hi
  have hpreX : Pre (m0.write (X_ L) i) := hPre m0 _ hm0 ((Agree.write m0 (X_ L) i (by addr3)).mono (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
    simp only [rangeV, Lvars, List.mem_append, List.mem_cons, true_or, or_true]))
  have hlt : (m0.write (X_ L) i) (X_ L) < (m0.write (X_ L) i) N := by
    rw [Mem.write_same, Mem.write_ne _ _ (fun h => hNL (by rw [h]; simp [Lvars]))]; exact hi
  refine hP _ _ ⟨hpreX, hlt⟩ ⟨fun y hy hyV => ?_, ?_⟩
  · by_cases hyx : y = X_ L
    · rw [hyx, Mem.write_same, Mem.write_same]
    · rw [Mem.write_ne _ _ hyx, Mem.write_ne _ _ hyx]
      rw [Mem.write_ne _ _ (by addr3)] at hy
      have hyV' : y ∉ Lvars (L + 1) ++ [RNG L] := by
        intro h
        apply hyV
        simp only [rangeVX, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]
      have hy0 : y ≠ HP := fun h => hyV (by rw [h]; exact List.mem_cons_self)
      exact ag2.var y hy hy0 hyV'
  · rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]; exact ag2.2

/-- `allRangeM L N t`: do all indices `i < M[N]` satisfy `t`? -/
def allRangeM (L N : ℕ) (t : Cmd) : Cmd := notM (anyRangeM L N (notM t))


theorem allRangeM_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool}
    (L N n : ℕ) (hL : L + 1 ≤ 9)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) < m N) P)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hN : 5 ≤ N ∧ N < IN) (hNV : N ∉ V)
    (hNL : N ∉ Lvars L) (hNL' : N ∉ Lvars (L + 1)) (hNF : N ≠ FLAG) (hNR : N ≠ RNG L)
    (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hVR : RNG L ∉ V)
    (hctx : ∀ m, Pre m → Ctx m) (hn : ∀ m, Pre m → m N ≤ n)
    (hPre : StableP Pre (rangeV L ++ FLAG :: V))
    (hP : Stable (fun m => Pre m ∧ m (X_ L) < m N) P (LvarsX L ++ FLAG :: V ++ rangeVX L)) :
    TestSpec (allRangeM L N t) (FLAG :: (rangeV L ++ FLAG :: (FLAG :: V)))
      (n * (B + 12) + n * 6 + 21) Pre
      (fun m => (List.range (m N)).all (fun i => P (m.write (X_ L) i))) := by
  have hnot : TestSpec (notM t) (FLAG :: V) (B + 1) (fun m => Pre m ∧ m (X_ L) < m N) (fun m => !P m) :=
    notM_spec ht (fun x hx => (hV x hx).1) (fun m hm => hctx m hm.1)
  have hV' : ∀ x, x ∈ FLAG :: V → 5 ≤ x ∧ x < IN := by
    intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
    · constructor <;> addr3
    · exact hV x hx
  have hany := anyRangeM_spec L N n hL hnot hV' hN (by
      simp only [List.mem_cons, not_or]; exact ⟨hNF, hNV⟩) hNL hNL' hNF hNR (by
      intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx
      · simp [LvarsX, FLAG, I_, CNT_, PTR_, CONT_, OUT_]; omega
      · exact hVL x hx) (by
      simp only [List.mem_cons, not_or]; exact ⟨by addr3, hVR⟩) hctx hn
    (hPre.mono (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))
    (by
      intro m m' hm ha
      show (!P m') = !P m
      rw [hP m m' hm (ha.mono (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto))])
  have hres := notM_spec hany (by
      intro x hx
      simp only [List.mem_append, List.mem_cons, rangeV] at hx
      rcases hx with (hx | rfl | hx) | rfl | rfl | hx
      · have := (Lvars_range (L + 1) hL x hx).1; omega
      · addr3
      · have := (Lvars_range L (by omega) x hx).1; omega
      · addr3
      · addr3
      · exact (hV x hx).1) hctx
  have hB : n * (B + 1 + 11) + n * 6 + 20 + 1 ≤ n * (B + 12) + n * 6 + 21 := by
    have : n * (B + 1 + 11) = n * (B + 12) := by ring
    omega
  refine (hres.mono (fun x hx => hx) hB (fun m hm => hm)).congr (fun m hm => ?_)
  rw [List.all_eq_not_any_not]


/-! ### Sequencing routines and tests -/

theorem RSpec.seq {c₁ c₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre Pre₂ : Mem → Prop}
    {Post₁ Post₂ : Mem → Mem → Prop} (h₁ : RSpec c₁ V₁ B₁ Pre Post₁) (h₂ : RSpec c₂ V₂ B₂ Pre₂ Post₂)
    (h12 : ∀ m m₁, Pre m → Agree m m₁ V₁ → Post₁ m m₁ → Pre₂ m₁) :
    RSpec (.seq c₁ c₂) (V₁ ++ V₂) (B₁ + B₂) Pre
      (fun m m₂ => ∃ m₁, Agree m m₁ V₁ ∧ Post₁ m m₁ ∧ Agree m₁ m₂ V₂ ∧ Post₂ m₁ m₂) := by
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp₁⟩ := h₁ m hm
  obtain ⟨m₂, k₂, e₂, hk₂, ag₂, hp₂⟩ := h₂ m₁ (h12 m m₁ hm ag₁ hp₁)
  exact ⟨m₂, _, Cmd.Exec.seq e₁ e₂, by omega, ag₁.trans ag₂, m₁, ag₁, hp₁, ag₂, hp₂⟩

/-- A routine followed by a test, whose value is a function `Q` of the initial state. -/
theorem TestSpec.after {c t : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre Pre' : Mem → Prop}
    {Post : Mem → Mem → Prop} {P' Q : Mem → Bool} (hc : RSpec c V₁ B₁ Pre Post)
    (ht : TestSpec t V₂ B₂ Pre' P') (h1 : ∀ m m₁, Pre m → Agree m m₁ V₁ → Post m m₁ → Pre' m₁)
    (h2 : ∀ m m₁, Pre m → Agree m m₁ V₁ → Post m m₁ → P' m₁ = Q m) :
    TestSpec (.seq c t) (V₁ ++ V₂) (B₁ + B₂) Pre Q := by
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp₁⟩ := hc m hm
  obtain ⟨m₂, k₂, e₂, hk₂, ag₂, hfl⟩ := ht m₁ (h1 m m₁ hm ag₁ hp₁)
  refine ⟨m₂, _, Cmd.Exec.seq e₁ e₂, by omega, ag₁.trans ag₂, ?_⟩
  show m₂ FLAG = bitv (Q m)
  rw [hfl, h2 m m₁ hm ag₁ hp₁]

/-- Conditional between two tests. -/
theorem TestSpec.ite {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {P₁ P₂ : Mem → Bool} (a b : ℕ) (h₁ : TestSpec t₁ V₁ B₁ Pre P₁) (h₂ : TestSpec t₂ V₂ B₂ Pre P₂) :
    TestSpec (.ite (.eq a b) t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 2) Pre
      (fun m => if m a = m b then P₁ m else P₂ m) := by
  intro m hm
  dsimp only
  by_cases h : m a = m b
  · have hc : (Cond.eq a b).eval m = true := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₁ m hm
    exact ⟨m₁, _, Cmd.Exec.ite_true hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_left _ hx),
      by rw [hfl, if_pos h]⟩
  · have hc : (Cond.eq a b).eval m = false := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₂ m hm
    exact ⟨m₁, _, Cmd.Exec.ite_false hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_right _ hx),
      by rw [hfl, if_neg h]⟩

/-- Conditional on `M[a] < M[b]`. -/
theorem TestSpec.iteLt {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {P₁ P₂ : Mem → Bool} (a b : ℕ) (h₁ : TestSpec t₁ V₁ B₁ Pre P₁) (h₂ : TestSpec t₂ V₂ B₂ Pre P₂) :
    TestSpec (.ite (.lt a b) t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 2) Pre
      (fun m => if m a < m b then P₁ m else P₂ m) := by
  intro m hm
  dsimp only
  by_cases h : m a < m b
  · have hc : (Cond.lt a b).eval m = true := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₁ m hm
    exact ⟨m₁, _, Cmd.Exec.ite_true hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_left _ hx),
      by rw [hfl, if_pos h]⟩
  · have hc : (Cond.lt a b).eval m = false := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₂ m hm
    exact ⟨m₁, _, Cmd.Exec.ite_false hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_right _ hx),
      by rw [hfl, if_neg h]⟩

/-- `FLAG := 1`. -/
theorem trueTest_spec (Pre : Mem → Prop) : TestSpec (setc FLAG 1) [FLAG] 1 Pre (fun _ => true) :=
  fun m _ => ⟨m.write FLAG 1, 1, Exec.setc _ _ _, le_rfl, Agree.write_flag m 1, Mem.write_same _ _ _⟩

/-- `FLAG := 0`. -/
theorem falseTest_spec (Pre : Mem → Prop) : TestSpec (setc FLAG 0) [FLAG] 1 Pre (fun _ => false) :=
  fun m _ => ⟨m.write FLAG 0, 1, Exec.setc _ _ _, le_rfl, Agree.write_flag m 0, Mem.write_same _ _ _⟩

/-! ### Elementary loads -/

/-- `D := M[M[A] + 1 + M[I]]` (element `M[I]` of the array whose address is in `A`). -/
def elemM (A I D : ℕ) : Cmd := .seq (add D A I) (.seq (add D D ONE) (load D D))

theorem elemM_spec (A I D : ℕ) (hD : 5 ≤ D ∧ D < IN) (hDA : D ≠ A) (hDI : D ≠ I)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hA : ∀ m, Pre m → IN ≤ m A) :
    RSpec (elemM A I D) [D] 3 Pre (fun m m' => m' D = m (m A + 1 + m I) ∧ m' HP = m HP) := by
  intro m hm
  obtain ⟨hone, _, hhp⟩ := hctx m hm
  have hAm := hA m hm
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write D (m A + m I) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (add D A I) m m1 1 := by rw [hm1]; exact Exec.add _ _ _ _
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m.write D (m A + 1 + m I) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add D D ONE) m1 m2 1 := by
    have := Exec.add D D ONE m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr3), hone, Mem.write_write,
      show m A + m I + 1 = m A + 1 + m I by omega] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m.write D (m (m A + 1 + m I)) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (load D D) m2 m3 1 := by
    have := Exec.load D D m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr3), Mem.write_write] at this
    rw [hm3, hm2]; exact this
  refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), by omega, ?_, ?_, ?_⟩
  · rw [hm3]; exact Agree.write m D _ (by addr3)
  · rw [hm3, Mem.write_same]
  · rw [hm3, Mem.write_ne _ _ (by addr3)]

/-- `D := M[M[Q] + 1]`. -/
def field1M (Q D : ℕ) : Cmd := .seq (add D Q ONE) (load D D)

theorem field1M_spec (Q D : ℕ) (hD : 5 ≤ D ∧ D < IN) (hDQ : D ≠ Q)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hQ : ∀ m, Pre m → IN ≤ m Q) :
    RSpec (field1M Q D) [D] 2 Pre (fun m m' => m' D = m (m Q + 1) ∧ m' HP = m HP) := by
  intro m hm
  obtain ⟨hone, _, hhp⟩ := hctx m hm
  have hQm := hQ m hm
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write D (m Q + 1) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (add D Q ONE) m m1 1 := by
    have := Exec.add D Q ONE m; rwa [hone, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m.write D (m (m Q + 1)) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (load D D) m1 m2 1 := by
    have := Exec.load D D m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr3), Mem.write_write] at this
    rw [hm2, hm1]; exact this
  refine ⟨m2, _, Cmd.Exec.seq e1 e2, by omega, ?_, ?_, ?_⟩
  · rw [hm2]; exact Agree.write m D _ (by addr3)
  · rw [hm2, Mem.write_same]
  · rw [hm2, Mem.write_ne _ _ (by addr3)]

/-- `D := M[M[Q] + 2]`. -/
def field2M (Q D : ℕ) : Cmd := .seq (add D Q ONE) (.seq (add D D ONE) (load D D))

theorem field2M_spec (Q D : ℕ) (hD : 5 ≤ D ∧ D < IN) (hDQ : D ≠ Q)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hQ : ∀ m, Pre m → IN ≤ m Q) :
    RSpec (field2M Q D) [D] 3 Pre (fun m m' => m' D = m (m Q + 2) ∧ m' HP = m HP) := by
  intro m hm
  obtain ⟨hone, _, hhp⟩ := hctx m hm
  have hQm := hQ m hm
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write D (m Q + 1) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (add D Q ONE) m m1 1 := by
    have := Exec.add D Q ONE m; rwa [hone, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m.write D (m Q + 2) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add D D ONE) m1 m2 1 := by
    have := Exec.add D D ONE m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr3), hone, Mem.write_write] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m.write D (m (m Q + 2)) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (load D D) m2 m3 1 := by
    have := Exec.load D D m2
    rw [hm2, Mem.write_same, Mem.write_ne _ _ (by addr3), Mem.write_write] at this
    rw [hm3, hm2]; exact this
  refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), by omega, ?_, ?_, ?_⟩
  · rw [hm3]; exact Agree.write m D _ (by addr3)
  · rw [hm3, Mem.write_same]
  · rw [hm3, Mem.write_ne _ _ (by addr3)]

/-- `D := M[M[Q]]`. -/
theorem loadM_spec (Q D : ℕ) (hD : 5 ≤ D ∧ D < IN) (Pre : Mem → Prop) :
    RSpec (load D Q) [D] 1 Pre (fun m m' => m' D = m (m Q) ∧ m' HP = m HP) := by
  intro m _
  exact ⟨m.write D (m (m Q)), 1, Exec.load _ _ _, le_rfl, Agree.write m D _ (by addr3),
    Mem.write_same _ _ _, Mem.write_ne _ _ (by addr3)⟩

/-- `D := M[Q]`. -/
theorem movM_spec (Q D : ℕ) (hD : 5 ≤ D ∧ D < IN) (Pre : Mem → Prop) :
    RSpec (mov D Q) [D] 1 Pre (fun m m' => m' D = m Q ∧ m' HP = m HP) := by
  intro m _
  exact ⟨m.write D (m Q), 1, Exec.mov _ _ _, le_rfl, Agree.write m D _ (by addr3),
    Mem.write_same _ _ _, Mem.write_ne _ _ (by addr3)⟩

end DisequalityDispersion.Machine
