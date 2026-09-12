import MNet
import UnitFlow

/-! # Maximum flow on the machine

`Network.maxflow` (augmenting paths with breadth-first layers, `UnitFlow`) is replicated
step by step on the machine: residual tests, the new frontier, the layers, the reachability
test, the augmenting path, its steps, the augmentation, and the fuelled outer loop. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded Flow

/-! ### Globals of the flow phase -/

def UARR : ℕ := 190
def SEEN : ℕ := 191
def FRONT : ℕ := 192
def LAYS : ℕ := 193
def PATH : ℕ := 194
def STEPS : ℕ := 195
def MDE : ℕ := 196
def CUR : ℕ := 197
def FUEL : ℕ := 198
def NEWU : ℕ := 199

theorem UARR_eq : UARR = 190 := rfl
theorem SEEN_eq : SEEN = 191 := rfl
theorem FRONT_eq : FRONT = 192 := rfl
theorem LAYS_eq : LAYS = 193 := rfl
theorem PATH_eq : PATH = 194 := rfl
theorem STEPS_eq : STEPS = 195 := rfl
theorem MODE_eq : MDE = 196 := rfl
theorem CUR_eq : CUR = 197 := rfl
theorem FUEL_eq : FUEL = 198 := rfl
theorem NEWU_eq : NEWU = 199 := rfl

/-- `addrn` extended with the flow globals. -/
macro "addrf" : tactic => `(tactic| (first | omega | (simp only [A_, NEL, JJ, CC, I_, CNT_, PTR_,
  CONT_, X_, OUT_, RNG, G_, FLAG_eq, V2_eq, IN_eq', HP_eq', ONE_eq', POS_eq, OK_eq, VAL_eq, TMP_eq,
  N_eq, INB_eq, ZERO_eq, CNT_eq, POW_eq, PTR_eq, LAST_eq, BIT_eq, J_eq, CONT_eq, KV_eq, BASE_eq,
  SRCS_eq, SYMS_eq, NODES_eq, XV_eq, YV_eq, TV_eq, TESTS_eq, OUTS_eq, NN_eq, KK_eq, MM_eq, IDS_eq,
  RESV_eq, NETS_eq, NETT_eq, NETN_eq, ARCS_eq, REPS_eq, RNGN_eq, UARR_eq, SEEN_eq, FRONT_eq, LAYS_eq,
  PATH_eq, STEPS_eq, MODE_eq, CUR_eq, FUEL_eq, NEWU_eq] at * <;> omega)))

/-! ### Membership of a value in an array -/

/-- `FLAG := M[Y] ∈ array at M[SRC]`. -/
def memValM (L SRC Y : ℕ) : Cmd := anyM L SRC (eqTest (X_ L) Y)

theorem any_eq_mem (l : List ℕ) (a : ℕ) : l.any (fun x => decide (x = a)) = decide (a ∈ l) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨x, hx, h⟩; rw [decide_eq_true_iff] at h; rw [← h]; exact hx
  · intro h; exact ⟨a, h, by simp⟩

theorem memValM_spec (L SRC Y n : ℕ) (hL : L ≤ 9) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hY : 5 ≤ Y ∧ Y < IN)
    (hSL : SRC ∉ Lvars L) (hSF : SRC ≠ FLAG) (hYL : Y ∉ Lvars L) (hYF : Y ≠ FLAG)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m)
    (harr : ∀ m, Pre m → IN ≤ m SRC ∧ m SRC + 1 + m (m SRC) ≤ m HP ∧ m (m SRC) ≤ n)
    (hPre : StableP Pre (Lvars L ++ FLAG :: [FLAG])) :
    TestSpec (memValM L SRC Y) (Lvars L ++ FLAG :: [FLAG]) (n * (3 + 11) + 10) Pre
      (fun m => decide (m Y ∈ arrAt m (m SRC))) := by
  have hYX : Y ≠ X_ L := fun h => hYL (by rw [h]; simp [Lvars])
  have h := anyM_spec L SRC n (eqTest_spec (X_ L) Y (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC))) hL
    (by intro x hx; simp at hx; subst hx; constructor <;> addr3) hSRC (by simp; exact hSF) hSL hSF
    (by intro x hx; simp at hx; subst hx; simp [LvarsX, FLAG, I_, CNT_, PTR_, CONT_, OUT_]; omega)
    hctx harr hPre
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := (hctx m hm).2.2
      have hXlt : X_ L < 200 := (Lvars_range L hL (X_ L) (by simp [Lvars])).2
      have hXV : X_ L ∉ LvarsX L ++ FLAG :: [FLAG] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by simp [LvarsX, X_, I_, CNT_, PTR_, CONT_, OUT_], by addr3, by addr3⟩
      have hYV : Y ∉ LvarsX L ++ FLAG :: [FLAG] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨?_, hYF, hYF⟩
        intro h
        exact hYL (by simp only [LvarsX, List.mem_cons, List.not_mem_nil, or_false] at h; simp [Lvars]; tauto)
      show decide (m' (X_ L) = m' Y) = decide (m (X_ L) = m Y)
      rw [hag.var (X_ L) (lt_hp hhp hXlt) (by addr3) hXV, hag.var Y (lt_hp hhp hY.2) (by addr3) hYV])
  unfold memValM
  refine h.congr (fun m hm => ?_)
  dsimp only
  rw [← any_eq_mem]
  apply any_congr_mem
  intro x _
  rw [Mem.write_same, Mem.write_ne _ _ hYX]


/-! ### The flow context and residual tests -/

/-- The context of the flow phase: the network, and the current flow `U` at `UARR`. -/
def FCtx (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (m : Mem) : Prop := NetCtx k g m ∧ PArrIs m UARR U

theorem FCtx.stableP {k : ℕ} {g : GInstance} {U : List (ℕ × ℕ)} {V : List ℕ} (hV : SafeVars V) (hI : IDS ∉ V)
    (hR : RNGN ∉ V) (hP : REPS ∉ V) (hS : NETS ∉ V) (hT : NETT ∉ V) (hN : NETN ∉ V) (hA : ARCS ∉ V)
    (hU : UARR ∉ V) : StableP (FCtx k g U) V :=
  (NetCtx.stableP hV hI hR hP hS hT hN hA).and
    (PArrIs.stableP (P := UARR) (fun x hx => (hV x hx).2.1) (by addrf) (by addrf) hU)

theorem FCtx.ctx {k : ℕ} {g : GInstance} {U : List (ℕ × ℕ)} {m : Mem} (h : FCtx k g U m) : Ctx m :=
  h.1.1.1.1.1.ctx

theorem FCtx.inst {k : ℕ} {g : GInstance} {U : List (ℕ × ℕ)} {m : Mem} (h : FCtx k g U m) : InstCtx k g m :=
  h.1.1.1.1.1

/-- The size bound of the arc list. -/
def arcBound (n : ℕ) : ℕ := n * n + 3 * n + 2

theorem arcs_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) :
    (g.networkL g.base.canonIds).arcs.length ≤ arcBound n := by
  show (g.nodeArcsL _ ++ g.edgeArcsL _ ++ g.srcArcsL _ ++ g.snkArcsL _).length ≤ _
  simp only [List.length_append]
  have := nodeArcsL_length_le hn; have := edgeArcsL_length_le hn; have := srcArcsL_length_le hn
  have := snkArcsL_length_le hn
  unfold arcBound; omega

theorem netNodes_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) :
    (g.networkL g.base.canonIds).nodes.length ≤ 2 * n + 2 := by
  show (g.netNodesL _).length ≤ _
  unfold GInstance.netNodesL
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  have := repsL_length_le g g.base.canonIds; have := hn.nodes; omega

/-- A fresh two-cell record `(M[A], M[B])`; its address in `D`. -/
def mkPairM (A B D : ℕ) : Cmd :=
  .seq (mov D HP) (.seq (store HP A) (.seq (add HP HP ONE) (.seq (store HP B) (add HP HP ONE))))

theorem mkPairM_spec (A B D : ℕ) (hA : 5 ≤ A ∧ A < IN) (hB : 5 ≤ B ∧ B < IN) (hD : 5 ≤ D ∧ D < IN)
    (hAD : A ≠ D) (hBD : B ≠ D) (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) :
    RSpec (mkPairM A B D) [D] 5 Pre
      (fun m m' => m' D = m HP ∧ m' (m HP) = m A ∧ m' (m HP + 1) = m B ∧ m' HP = m HP + 2) := by
  intro m hm
  obtain ⟨hone, _, hhp⟩ := hctx m hm
  have hDH : D ≠ HP := by addr3
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write D (m HP) := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov D HP) m m1 1 := by rw [hm1]; exact Exec.mov _ _ _
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (m HP) (m A) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (store HP A) m1 m2 1 := by
    have := Exec.store HP A m1
    rw [hm1, Mem.write_ne _ _ (Ne.symm hDH), Mem.write_ne _ _ hAD] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write HP (m HP + 1) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add HP HP ONE) m2 m3 1 := by
    have := Exec.add HP HP ONE m2
    rw [hm2, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm1, Mem.write_ne _ _ (Ne.symm hDH),
      Mem.write_ne _ _ (by addr3), hone] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (m HP + 1) (m B) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (store HP B) m3 m4 1 := by
    have := Exec.store HP B m3
    rw [hm3, Mem.write_same, Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by addr3), hm1,
      Mem.write_ne _ _ hBD] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write HP (m HP + 2) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm3, Mem.write_same,
      Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by addr3), hm1, Mem.write_ne _ _ (by addr3), hone] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  have q5 : ∀ x, x ≠ HP → x ≠ m HP + 1 → x ≠ m HP → x ≠ D → m5 x = m x := fun x h1 h2 h3 h4 => by
    rw [hm5, Mem.write_ne _ _ h1, hm4, Mem.write_ne _ _ h2, hm3, Mem.write_ne _ _ h1, hm2, Mem.write_ne _ _ h3,
      hm1, Mem.write_ne _ _ h4]
  refine ⟨m5, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e5))), by omega, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x hx hxV => ?_, by rw [hm5, Mem.write_same]; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
    exact q5 x hxV.1 (by omega) (by omega) hxV.2
  · rw [hm5, Mem.write_ne _ _ hDH, hm4, Mem.write_ne _ _ (by addr3), hm3, Mem.write_ne _ _ hDH, hm2,
      Mem.write_ne _ _ (by addr3), hm1, Mem.write_same]
  · rw [hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_ne _ _ (by omega), hm3, Mem.write_ne _ _ (by addr3), hm2,
      Mem.write_same]
  · rw [hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_same]
  · rw [hm5, Mem.write_same]


/-- `FLAG := ResL U M[X] M[Y]` (fresh records for the two candidate arcs). -/
def resTest (X Y : ℕ) : Cmd :=
  .seq (mkPairM X Y (G_ 10)) (.seq (mkPairM Y X (G_ 11))
    (orM (andM (memPairM 2 ARCS (G_ 10)) (notM (memPairM 2 UARR (G_ 10)))) (memPairM 2 UARR (G_ 11))))

def resV : List ℕ := [G_ 10] ++ ([G_ 11] ++ ((memPairV 2 ++ (FLAG :: memPairV 2)) ++ memPairV 2))

theorem resV_safe : SafeVars resV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (SafeVars.append (safeVars_memPairV 2 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (safeVars_memPairV 2 (by norm_num)))) (safeVars_memPairV 2 (by norm_num))))

/-- The record facts after the two allocations. -/
def RecAt (m : Mem) (D A B : ℕ) : Prop :=
  IN ≤ m D ∧ m D + 2 ≤ m HP ∧ m (m D) = m A ∧ m (m D + 1) = m B

theorem RecAt.stable {m m' : Mem} {V : List ℕ} {D A B : ℕ} (hag : Agree m m' V) (hV : ∀ x, x ∈ V → x < IN)
    (hhp : 200 ≤ m HP) (hD : D < 200) (hDH : D ≠ HP) (hDV : D ∉ V) (hA : A < 200) (hAH : A ≠ HP) (hAV : A ∉ V)
    (hB : B < 200) (hBH : B ≠ HP) (hBV : B ∉ V) (h : RecAt m D A B) : RecAt m' D A B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hD' : m' D = m D := hag.var D (lt_hp hhp hD) hDH hDV
  refine ⟨by rw [hD']; exact h1, by rw [hD']; exact le_trans h2 hag.2, ?_, ?_⟩
  · rw [hD', hag.heap hV _ h1 (by omega), hag.var A (lt_hp hhp hA) hAH hAV]; exact h3
  · rw [hD', hag.heap hV _ (by omega) (by omega), hag.var B (lt_hp hhp hB) hBH hBV]; exact h4

theorem resTest_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n UB : ℕ) (hn : Sized n g)
    (hU : U.length ≤ UB) (X Y : ℕ) (hX : 5 ≤ X ∧ X < IN) (hY : 5 ≤ Y ∧ Y < IN) (hXV : X ∉ resV) (hYV : Y ∉ resV)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → FCtx k g U m) (hPre : StableP Pre resV) :
    TestSpec (resTest X Y) resV (5 + (5 + ((arcBound n * 23 + 10) + (UB * 23 + 10 + 1) + 3 + (UB * 23 + 10) + 3)))
      Pre (fun m => decide ((g.networkL g.base.canonIds).ResL U (m X) (m Y))) := by
  have hsV : ∀ x, x ∈ resV → x < IN := fun x hx => (resV_safe x hx).2.1
  have hX10 : X ≠ G_ 10 := fun h => hXV (by rw [h]; simp [resV])
  have hX11 : X ≠ G_ 11 := fun h => hXV (by rw [h]; simp [resV])
  have hY10 : Y ≠ G_ 10 := fun h => hYV (by rw [h]; simp [resV])
  have hY11 : Y ≠ G_ 11 := fun h => hYV (by rw [h]; simp [resV])
  have hXM : X ∉ memPairV 2 := fun h => hXV (by simp [resV]; tauto)
  have hYM : Y ∉ memPairV 2 := fun h => hYV (by simp [resV]; tauto)
  have hXF : X ≠ FLAG := fun h => hXV (by rw [h]; simp [resV, memPairV])
  have hYF : Y ≠ FLAG := fun h => hYV (by rw [h]; simp [resV, memPairV])
  have hsub1 : ∀ x, x ∈ [G_ 10] → x ∈ resV := fun x hx => by simp [resV] at hx ⊢; tauto
  have hsub2 : ∀ x, x ∈ [G_ 11] → x ∈ resV := fun x hx => by simp [resV] at hx ⊢; tauto
  have hsubM : ∀ x, x ∈ memPairV 2 → x ∈ resV := fun x hx => by simp [resV] at hx ⊢; tauto
  have hsubF : ∀ x, x ∈ FLAG :: memPairV 2 → x ∈ resV := fun x hx => by simp [resV, memPairV] at hx ⊢; tauto
  -- the two records
  let Pre1 : Mem → Prop := fun m => Pre m ∧ RecAt m (G_ 10) X Y
  let Pre2 : Mem → Prop := fun m => Pre1 m ∧ RecAt m (G_ 11) Y X
  have hstab2 : ∀ {V : List ℕ}, (∀ x, x ∈ V → x ∈ resV) → G_ 10 ∉ V → G_ 11 ∉ V → StableP Pre2 V := by
    intro V hV h10 h11 m m' hm hag
    have hhp : 200 ≤ m HP := (hctx m hm.1.1).ctx.2.2
    have hV' : ∀ x, x ∈ V → x < IN := fun x hx => hsV x (hV x hx)
    refine ⟨⟨hPre m m' hm.1.1 (hag.mono hV), ?_⟩, ?_⟩
    · exact hm.1.2.stable hag hV' hhp (by decide) (by decide) h10 hX.2 (by addr3) (fun h => hXV (hV _ h))
        hY.2 (by addr3) (fun h => hYV (hV _ h))
    · exact hm.2.stable hag hV' hhp (by decide) (by decide) h11 hY.2 (by addr3) (fun h => hYV (hV _ h))
        hX.2 (by addr3) (fun h => hXV (hV _ h))
  -- the membership tests
  have hA : ∀ m, Pre2 m → PairsWF m (m ARCS) ∧ m (m ARCS) ≤ arcBound n ∧ IN ≤ m (G_ 10) ∧ m (G_ 10) + 2 ≤ m HP :=
    fun m hm => ⟨(hctx m hm.1.1).1.2.1, by rw [(hctx m hm.1.1).1.2.len]; exact arcs_length_le hn, hm.1.2.1, hm.1.2.2.1⟩
  have hU1 : ∀ m, Pre2 m → PairsWF m (m UARR) ∧ m (m UARR) ≤ UB ∧ IN ≤ m (G_ 10) ∧ m (G_ 10) + 2 ≤ m HP :=
    fun m hm => ⟨(hctx m hm.1.1).2.1, by rw [(hctx m hm.1.1).2.len]; exact hU, hm.1.2.1, hm.1.2.2.1⟩
  have hU2 : ∀ m, Pre2 m → PairsWF m (m UARR) ∧ m (m UARR) ≤ UB ∧ IN ≤ m (G_ 11) ∧ m (G_ 11) + 2 ≤ m HP :=
    fun m hm => ⟨(hctx m hm.1.1).2.1, by rw [(hctx m hm.1.1).2.len]; exact hU, hm.2.1, hm.2.2.1⟩
  have tA := memPairM_spec 2 ARCS (G_ 10) (arcBound n) (by norm_num) (by constructor <;> addrn)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) Pre2
    (fun m hm => (hctx m hm.1.1).ctx) hA (hstab2 hsubM (by decide) (by decide))
  have tU1 := memPairM_spec 2 UARR (G_ 10) UB (by norm_num) (by constructor <;> addrf)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) Pre2
    (fun m hm => (hctx m hm.1.1).ctx) hU1 (hstab2 hsubM (by decide) (by decide))
  have tU2 := memPairM_spec 2 UARR (G_ 11) UB (by norm_num) (by constructor <;> addrf)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) Pre2
    (fun m hm => (hctx m hm.1.1).ctx) hU2 (hstab2 hsubM (by decide) (by decide))
  have tN := notM_spec tU1 (fun x hx => (memPairV_range 2 (by norm_num) x hx).1) (fun m hm => (hctx m hm.1.1).ctx)
  -- values are stable under the test variables
  have hval : ∀ (D : ℕ) (A B : ℕ), D = G_ 10 ∧ A = X ∧ B = Y ∨ D = G_ 11 ∧ A = Y ∧ B = X →
      ∀ (S : ℕ) (l : List (ℕ × ℕ)), (∀ m, Pre2 m → PArrIs m S l) → S ∉ resV → 5 ≤ S → S < IN →
      ∀ {V : List ℕ}, (∀ x, x ∈ V → x ∈ resV) → G_ 10 ∉ V → G_ 11 ∉ V → ∀ m m', Pre2 m → Agree m m' V →
      decide ((m' (m' D), m' (m' D + 1)) ∈ pairsAt m' (m' S)) = decide ((m (m D), m (m D + 1)) ∈ pairsAt m (m S)) := by
    intro D A B hD S l hS hSV hS5 hSlt V hV h10 h11 m m' hm hag
    have hhp : 200 ≤ m HP := (hctx m hm.1.1).ctx.2.2
    have hV' : ∀ x, x ∈ V → x < IN := fun x hx => hsV x (hV x hx)
    obtain ⟨h1, h2, h3, h4⟩ : RecAt m D A B := by
      rcases hD with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact hm.1.2
      · exact hm.2
    have hDV : D ∉ V := by rcases hD with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> assumption
    have hD' : m' D = m D := hag.var D (lt_hp hhp (by rcases hD with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> decide))
      (by rcases hD with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> decide) hDV
    have hSl := hS m hm
    rw [hD', hag.heap hV' (m D) h1 (lt_of_lt_of_le (Nat.lt_add_of_pos_right (by norm_num)) h2),
      hag.heap hV' (m D + 1) (le_trans h1 (Nat.le_succ _)) (lt_of_lt_of_le (by omega) h2),
      hag.var S (lt_hp hhp hSlt) (by addr3) (fun h => hSV (hV _ h)), hag.pairsAt hV' _ hSl.1.1 hSl.1.2.1 hSl.1.2.2]
  have hArcs : ∀ m, Pre2 m → PArrIs m ARCS (g.networkL g.base.canonIds).arcs := fun m hm => (hctx m hm.1.1).1.2
  have hUarr : ∀ m, Pre2 m → PArrIs m UARR U := fun m hm => (hctx m hm.1.1).2
  have tAnd := andM_spec tA tN (fun x hx => (memPairV_range 2 (by norm_num) x hx).1) (fun m hm => (hctx m hm.1.1).ctx)
    (hstab2 hsubM (by decide) (by decide))
    (fun m m' hm hag => by
      show (!decide ((m' (m' (G_ 10)), m' (m' (G_ 10) + 1)) ∈ pairsAt m' (m' UARR))) =
        !decide ((m (m (G_ 10)), m (m (G_ 10) + 1)) ∈ pairsAt m (m UARR))
      rw [hval (G_ 10) X Y (Or.inl ⟨rfl, rfl, rfl⟩) UARR U hUarr (by decide) (by addrf) (by addrf) hsubM (by decide) (by decide)
        m m' hm hag])
  have hsubAF : ∀ x, x ∈ memPairV 2 ++ FLAG :: memPairV 2 → x ∈ resV := fun x hx => by
    rw [List.mem_append, List.mem_cons] at hx
    rcases hx with h | rfl | h
    · exact hsubM x h
    · simp [resV, memPairV]
    · exact hsubM x h
  have tOr := orM_spec tAnd tU2 (fun x hx => (resV_safe x (hsubAF x hx)).1)
    (fun m hm => (hctx m hm.1.1).ctx) (hstab2 hsubAF (by decide) (by decide))
    (hval (G_ 11) Y X (Or.inr ⟨rfl, rfl, rfl⟩) UARR U hUarr (by decide) (by addrf) (by addrf) hsubAF (by decide) (by decide))
  -- the allocations
  have e2 := mkPairM_spec Y X (G_ 11) hY hX (by constructor <;> addr3) hY11 hX11 Pre1 (fun m hm => (hctx m hm.1).ctx)
  have t2 := TestSpec.after e2 tOr
    (Q := fun m => (decide ((m X, m Y) ∈ (g.networkL g.base.canonIds).arcs) && !decide ((m X, m Y) ∈ U)) ||
      decide ((m Y, m X) ∈ U))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm.1).ctx.2.2
      have hV' : ∀ x, x ∈ [G_ 11] → x < IN := fun x hx => hsV x (hsub2 x hx)
      refine ⟨⟨hPre m m₁ hm.1 (hag.mono hsub2), hm.2.stable hag hV' hhp (by decide) (by decide) (by decide) hX.2
        (by addr3) (by simp; exact hX11) hY.2 (by addr3) (by simp; exact hY11)⟩, ?_⟩
      refine ⟨by rw [hp.1]; exact hhp, by rw [hp.1, hp.2.2.2], ?_, ?_⟩
      · rw [hp.1, hp.2.1, hag.var Y (lt_hp hhp hY.2) (by addr3) (by simp; exact hY11)]
      · rw [hp.1, hp.2.2.1, hag.var X (lt_hp hhp hX.2) (by addr3) (by simp; exact hX11)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm.1).ctx.2.2
      have hV' : ∀ x, x ∈ [G_ 11] → x < IN := fun x hx => hsV x (hsub2 x hx)
      obtain ⟨r1, r2, r3, r4⟩ := hm.2
      have hc := hctx m hm.1
      dsimp only
      rw [hp.1, hp.2.1, hp.2.2.1, hag.var (G_ 10) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.heap hV' (m (G_ 10)) r1 (by omega), hag.heap hV' (m (G_ 10) + 1) (le_trans r1 (Nat.le_succ _)) (by omega),
        r3, r4,
        hag.var ARCS (lt_hp hhp (by decide)) (by decide) (by decide), hag.var UARR (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.pairsAt hV' _ hc.1.2.1.1 hc.1.2.1.2.1 hc.1.2.1.2.2, hag.pairsAt hV' _ hc.2.1.1 hc.2.1.2.1 hc.2.1.2.2,
        hc.1.2.2, hc.2.2])
  have e1 := mkPairM_spec X Y (G_ 10) hX hY (by constructor <;> addr3) hX10 hY10 Pre (fun m hm => (hctx m hm).ctx)
  have t1 := TestSpec.after e1 t2
    (Q := fun m => (decide ((m X, m Y) ∈ (g.networkL g.base.canonIds).arcs) && !decide ((m X, m Y) ∈ U)) ||
      decide ((m Y, m X) ∈ U))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm).ctx.2.2
      refine ⟨hPre m m₁ hm (hag.mono hsub1), ?_⟩
      refine ⟨by rw [hp.1]; exact hhp, by rw [hp.1, hp.2.2.2], ?_, ?_⟩
      · rw [hp.1, hp.2.1, hag.var X (lt_hp hhp hX.2) (by addr3) (by simp; exact hX10)]
      · rw [hp.1, hp.2.2.1, hag.var Y (lt_hp hhp hY.2) (by addr3) (by simp; exact hY10)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := (hctx m hm).ctx.2.2
      dsimp only
      rw [hag.var X (lt_hp hhp hX.2) (by addr3) (by simp; exact hX10),
        hag.var Y (lt_hp hhp hY.2) (by addr3) (by simp; exact hY10)])
  unfold resTest
  refine (t1.mono (fun x hx => hx) (by omega) (fun m hm => hm)).congr (fun m hm => ?_)
  dsimp only
  unfold Network.ResL
  simp only [Bool.decide_or, Bool.decide_and, decide_not]


/-! ### The new frontier -/

/-- Size bounds of the flow phase, as functions of the instance size. -/
def nodeBound (n : ℕ) : ℕ := 2 * n + 2
def seenBound (n : ℕ) : ℕ := (2 * n + 2) * (2 * n + 3)
def flowBound (n : ℕ) : ℕ := (arcBound n + 1) * (2 * n + 3)

/-- The context of the layer computation: the flow context with the arrays `seen` and `front`. -/
def LCtx (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (seen front : List ℕ) (m : Mem) : Prop :=
  FCtx k g U m ∧ ArrIs m SEEN seen ∧ ArrIs m FRONT front

theorem LCtx.stableP {k : ℕ} {g : GInstance} {U : List (ℕ × ℕ)} {seen front : List ℕ} {V : List ℕ}
    (hV : SafeVars V) (hI : IDS ∉ V) (hR : RNGN ∉ V) (hP : REPS ∉ V) (hS : NETS ∉ V) (hT : NETT ∉ V)
    (hN : NETN ∉ V) (hA : ARCS ∉ V) (hU : UARR ∉ V) (hSe : SEEN ∉ V) (hF : FRONT ∉ V) :
    StableP (LCtx k g U seen front) V :=
  (FCtx.stableP hV hI hR hP hS hT hN hA hU).and
    ((ArrIs.stableP (P := SEEN) (fun x hx => (hV x hx).2.1) (by addrf) (by addrf) hSe).and
      (ArrIs.stableP (P := FRONT) (fun x hx => (hV x hx).2.1) (by addrf) (by addrf) hF))

theorem LCtx.ctx {k : ℕ} {g : GInstance} {U : List (ℕ × ℕ)} {seen front : List ℕ} {m : Mem}
    (h : LCtx k g U seen front m) : Ctx m := h.1.ctx

/-- Is `X_ 0` a new node reached from the frontier? -/
def frontTest : Cmd :=
  andM (notM (memValM 1 SEEN (X_ 0)))
    (andM (notM (memValM 1 FRONT (X_ 0))) (anyM 1 FRONT (resTest (X_ 1) (X_ 0))))

def frontV : List ℕ :=
  (FLAG :: (Lvars 1 ++ FLAG :: [FLAG])) ++ ((FLAG :: (Lvars 1 ++ FLAG :: [FLAG])) ++ (Lvars 1 ++ FLAG :: resV))

theorem frontV_safe : SafeVars frontV :=
  SafeVars.append (SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_Lvars 1 (by norm_num))
      (safeVars_of_decide _ (by decide))))
    (SafeVars.append (SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_Lvars 1 (by norm_num))
      (safeVars_of_decide _ (by decide))))
      (SafeVars.append (safeVars_Lvars 1 (by norm_num)) (SafeVars.cons safeVars_FLAG resV_safe)))

/-- The step bound of `frontTest`. -/
def frontB (n : ℕ) : ℕ :=
  (seenBound n * (3 + 11) + 10 + 1) +
    ((nodeBound n * (3 + 11) + 10 + 1) +
      (nodeBound n * ((5 + (5 + ((arcBound n * 23 + 10) + (flowBound n * 23 + 10 + 1) + 3 +
        (flowBound n * 23 + 10) + 3))) + 11) + 10) + 3) + 3

theorem frontTest_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (seen front : List ℕ) (n : ℕ)
    (hn : Sized n g) (hU : U.length ≤ flowBound n) (hseen : seen.length ≤ seenBound n)
    (hfront : front.length ≤ nodeBound n) :
    TestSpec frontTest frontV (frontB n)
      (fun m => LCtx k g U seen front m ∧ m (X_ 0) ∈ arrAt m (m NETN))
      (fun m => decide (m (X_ 0) ∉ seen ∧ m (X_ 0) ∉ front ∧
        front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m (X_ 0)))) = true)) := by
  let Pre : Mem → Prop := fun m => LCtx k g U seen front m ∧ m (X_ 0) ∈ arrAt m (m NETN)
  have hPre : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V →
      NETN ∉ V → ARCS ∉ V → UARR ∉ V → SEEN ∉ V → FRONT ∉ V → X_ 0 ∉ V → StableP Pre V := by
    intro V hV h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hX m m' hm hag
    have hhp : 200 ≤ m HP := hm.1.ctx.2.2
    refine ⟨LCtx.stableP hV h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 m m' hm.1 hag, ?_⟩
    have hN := hm.1.1.1.1.2.2.2
    rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) hX, hag.var NETN (lt_hp hhp (by decide)) (by decide) h6,
      hag.arrAt (fun x hx => (hV x hx).2.1) _ hN.1 hN.2.1]
    exact hm.2
  have hs1 : SafeVars (Lvars 1 ++ FLAG :: [FLAG]) :=
    SafeVars.append (safeVars_Lvars 1 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hs1' : SafeVars (FLAG :: (Lvars 1 ++ FLAG :: [FLAG])) := SafeVars.cons safeVars_FLAG hs1
  -- `X_ 0 ∉ seen`
  have t1 := notM_spec (memValM_spec 1 SEEN (X_ 0) (seenBound n) (by norm_num) (by constructor <;> addrf)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) Pre (fun m hm => hm.1.ctx)
    (fun m hm => ⟨hm.1.2.1.1, hm.1.2.1.2.1, by rw [hm.1.2.1.len]; exact hseen⟩)
    (hPre hs1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
    (fun x hx => (hs1 x hx).1) (fun m hm => hm.1.ctx) |>.congr (Q := fun m => !decide (m (X_ 0) ∈ seen))
    (fun m hm => by dsimp only; rw [hm.1.2.1.2.2])
  -- `X_ 0 ∉ front`
  have t2 := notM_spec (memValM_spec 1 FRONT (X_ 0) (nodeBound n) (by norm_num) (by constructor <;> addrf)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) Pre (fun m hm => hm.1.ctx)
    (fun m hm => ⟨hm.1.2.2.1, hm.1.2.2.2.1, by rw [hm.1.2.2.len]; exact hfront⟩)
    (hPre hs1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
    (fun x hx => (hs1 x hx).1) (fun m hm => hm.1.ctx) |>.congr (Q := fun m => !decide (m (X_ 0) ∈ front))
    (fun m hm => by dsimp only; rw [hm.1.2.2.2.2])
  -- some `x ∈ front` with `ResL U x (X_ 0)`
  have hsR : SafeVars (Lvars 1 ++ FLAG :: resV) :=
    SafeVars.append (safeVars_Lvars 1 (by norm_num)) (SafeVars.cons safeVars_FLAG resV_safe)
  have hsRX : SafeVars (LvarsX 1 ++ FLAG :: resV) :=
    SafeVars.append (safeVars_LvarsX 1 (by norm_num)) (SafeVars.cons safeVars_FLAG resV_safe)
  have tr := resTest_spec k g U n (flowBound n) hn hU (X_ 1) (X_ 0) (by constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (fun m => Pre m ∧ m (X_ 1) ∈ arrAt m (m FRONT))
    (fun m hm => hm.1.1.1)
    (fun m m' hm hag => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      refine ⟨hPre resV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m' hm.1 hag, ?_⟩
      have hF := hm.1.1.2.2
      rw [hag.var (X_ 1) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var FRONT (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.arrAt (fun x hx => (resV_safe x hx).2.1) _ hF.1 hF.2.1]
      exact hm.2)
  have t3 := anyM_spec 1 FRONT (nodeBound n) tr (by norm_num) (fun x hx => ⟨(resV_safe x hx).1, (resV_safe x hx).2.1⟩)
    (by constructor <;> addrf) (by decide) (by decide) (by decide) (by decide) (fun m hm => hm.1.ctx)
    (fun m hm => ⟨hm.1.2.2.1, hm.1.2.2.2.1, by rw [hm.1.2.2.len]; exact hfront⟩)
    (hPre hsR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show decide ((g.networkL g.base.canonIds).ResL U (m' (X_ 1)) (m' (X_ 0))) =
        decide ((g.networkL g.base.canonIds).ResL U (m (X_ 1)) (m (X_ 0)))
      rw [hag.var (X_ 1) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t3' := t3.congr (Q := fun m => front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m (X_ 0)))))
    (fun m hm => by
      dsimp only
      rw [hm.1.2.2.2.2]
      apply any_congr_mem
      intro x _
      rw [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide)])
  have t23 := andM_spec t2 t3' (fun x hx => (hs1' x hx).1) (fun m hm => hm.1.ctx)
    (hPre hs1' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (fun m m' hm hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m' (X_ 0)))) =
        front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m (X_ 0))))
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t123 := andM_spec t1 t23 (fun x hx => (hs1' x hx).1) (fun m hm => hm.1.ctx)
    (hPre hs1' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (fun m m' hm hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show ((!decide (m' (X_ 0) ∈ front)) && front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m' (X_ 0))))) =
        ((!decide (m (X_ 0) ∈ front)) && front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m (X_ 0)))))
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
  unfold frontTest frontV frontB
  refine (t123.mono (fun x hx => hx) (by omega) (fun m hm => hm)).congr (fun m hm => ?_)
  dsimp only
  rw [Bool.decide_and, Bool.decide_and, decide_not, decide_not, Bool.decide_eq_true]


/-- `G_ 12 := newFront U seen front`. -/
def newFrontM : Cmd := .seq (filterM 0 NETN frontTest) (mov (G_ 12) (OUT_ 0))

def newFrontV : List ℕ := Lvars 0 ++ FLAG :: frontV ++ [G_ 12]

theorem newFrontV_safe : SafeVars newFrontV :=
  SafeVars.append (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG frontV_safe))
    (safeVars_of_decide _ (by decide))

theorem newFrontM_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (seen front : List ℕ) (n : ℕ)
    (hn : Sized n g) (hU : U.length ≤ flowBound n) (hseen : seen.length ≤ seenBound n)
    (hfront : front.length ≤ nodeBound n) :
    RSpec newFrontM newFrontV (nodeBound n * (frontB n + 14) + 9 + 1) (LCtx k g U seen front)
      (fun _ m' => ArrIs m' (G_ 12) ((g.networkL g.base.canonIds).newFront U seen front)) := by
  have hsF : SafeVars (Lvars 0 ++ FLAG :: frontV) :=
    SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG frontV_safe)
  have h := filterM_arr_spec 0 NETN (G_ 12) (nodeBound n) (g.networkL g.base.canonIds).nodes
    (fun y => decide (y ∉ seen ∧ y ∉ front ∧
      front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x y)) = true))
    (frontTest_spec k g U seen front n hn hU hseen hfront) (by norm_num)
    (fun x hx => ⟨(frontV_safe x hx).1, (frontV_safe x hx).2.1⟩) (by constructor <;> addrn) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by constructor <;> addr3) (fun m hm => hm.ctx)
    (fun m hm => hm.1.1.1.2.2.2) (netNodes_length_le hn)
    (LCtx.stableP hsF (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.ctx.2.2
      show decide (m' (X_ 0) ∉ seen ∧ m' (X_ 0) ∉ front ∧
          front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m' (X_ 0)))) = true) =
        decide (m (X_ 0) ∉ seen ∧ m (X_ 0) ∉ front ∧
          front.any (fun x => decide ((g.networkL g.base.canonIds).ResL U x (m (X_ 0)))) = true)
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x _ _ => by simp only [Mem.write_same])
  unfold newFrontM newFrontV
  exact h


/-! ### The layers -/

/-- The `(seen, front)` state of the breadth-first search after `i` rounds. -/
def layerState (N : Network ℕ) (U : List (ℕ × ℕ)) : ℕ → List ℕ × List ℕ
  | 0 => ([], [N.s])
  | i + 1 => ((layerState N U i).1 ++ (layerState N U i).2, N.newFront U (layerState N U i).1 (layerState N U i).2)

theorem layersAux_eq (N : Network ℕ) (U : List (ℕ × ℕ)) (j : ℕ) : ∀ i,
    N.layersAux U j (layerState N U i).1 (layerState N U i).2 =
      (List.range (j + 1)).map (fun t => (layerState N U (i + t)).2) := by
  induction j with
  | zero => intro i; simp [Network.layersAux]
  | succ j ih =>
    intro i
    simp only [Network.layersAux]
    have := ih (i + 1)
    simp only [layerState] at this
    rw [this]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    show (layerState N U (i + 1 + a)).2 = (layerState N U (i + (a + 1))).2
    rw [Nat.add_right_comm, Nat.add_assoc]

theorem layers_eq (N : Network ℕ) (U : List (ℕ × ℕ)) :
    N.layers U = (List.range (N.nodes.length + 1)).map (fun t => (layerState N U t).2) := by
  unfold Network.layers
  have := layersAux_eq N U N.nodes.length 0
  simp only [layerState, Nat.zero_add] at this
  exact this

theorem layerState_front_le (N : Network ℕ) (U : List (ℕ × ℕ)) (hN : 1 ≤ N.nodes.length) (i : ℕ) :
    (layerState N U i).2.length ≤ N.nodes.length := by
  cases i with
  | zero => simpa [layerState] using hN
  | succ i => simp only [layerState, Network.newFront]; exact List.length_filter_le _ _

theorem layerState_seen_le (N : Network ℕ) (U : List (ℕ × ℕ)) (hN : 1 ≤ N.nodes.length) (i : ℕ) :
    (layerState N U i).1.length ≤ i * N.nodes.length := by
  induction i with
  | zero => simp [layerState]
  | succ i ih =>
    simp only [layerState, List.length_append]
    have := layerState_front_le N U hN i
    rw [Nat.succ_mul]; omega



theorem netNodes_length_pos (g : GInstance) : 1 ≤ (g.networkL g.base.canonIds).nodes.length := by
  show 1 ≤ (g.netNodesL _).length
  unfold GInstance.netNodesL
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem layerState_seen_eq (N : Network ℕ) (U : List (ℕ × ℕ)) (j : ℕ) :
    (layerState N U j).1 = ((List.range j).map (fun t => (layerState N U t).2)).flatten := by
  induction j with
  | zero => simp [layerState]
  | succ j ih =>
    simp only [layerState]
    rw [ih, List.range_succ, List.map_append, List.flatten_append]
    simp

/-- A generic counted loop with an invariant indexed by the counter, and a body given as a
resource specification. -/
theorem loopR_spec (L : ℕ) (hL : L ≤ 9) (body : Cmd) (V : List ℕ) (B N : ℕ) (Inv : ℕ → Mem → Prop)
    (hV : ∀ x, x ∈ V → x < IN) (hIV : I_ L ∉ V) (hOV : ONE ∉ V)
    (hInv : ∀ j m, Inv j m → m (I_ L) = j ∧ m (CNT_ L) = N ∧ m ONE = 1 ∧ IN ≤ m HP)
    (hbody : ∀ j m, j < N → Inv j m → ∃ m' k, Cmd.Exec body m m' k ∧ k ≤ B ∧ Agree m m' V ∧
      Inv (j + 1) (m'.write (I_ L) (j + 1))) :
    ∀ j m, j ≤ N → Inv j m → ∃ m' k, Cmd.Exec (forLoop (I_ L) (CNT_ L) body) m m' k ∧ Inv N m' ∧
      k ≤ (N - j) * (B + 3) + 2 := by
  have hLv := Lvars_range L hL
  refine forLoop_spec (I_ L) (CNT_ L) body Inv N B (fun j m hm => ⟨(hInv j m hm).1, (hInv j m hm).2.1⟩) ?_
  intro j m hj hm
  obtain ⟨hi, _, hone, hhp⟩ := hInv j m hm
  obtain ⟨m', k, e, hk, hag, hinv'⟩ := hbody j m hj hm
  refine ⟨m', k, e, hk, ?_, ?_, hinv'⟩
  · rw [hag.var (I_ L) (lt_of_lt_of_le (hLv _ (by simp [Lvars])).2 hhp) (by addr') hIV, hi]
  · rw [hag.var ONE (lt_of_lt_of_le (by addr') hhp) (by addr') hOV, hone]

/-! ### The layers -/

/-- The entries of `ptrs` point to arrays holding the lists `ls`. -/
def Ptrs (m : Mem) (ptrs : List ℕ) (ls : List (List ℕ)) : Prop :=
  ptrs.length = ls.length ∧ ∀ i, (h : i < ptrs.length) → IN ≤ ptrs[i] ∧ ptrs[i] + 1 + m ptrs[i] ≤ m HP ∧
    arrAt m ptrs[i] = ls.getD i []

theorem Ptrs.stable {m m' : Mem} {V : List ℕ} {ptrs : List ℕ} {ls : List (List ℕ)} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (h : Ptrs m ptrs ls) : Ptrs m' ptrs ls := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i hi => ?_⟩
  obtain ⟨c1, c2, c3⟩ := h2 i hi
  refine ⟨c1, ?_, ?_⟩
  · rw [hag.heap hV _ c1 (by omega)]; exact le_trans c2 hag.2
  · rw [hag.arrAt hV _ c1 c2]; exact c3

theorem Ptrs.stableP {V : List ℕ} {ptrs : List ℕ} {ls : List (List ℕ)} (hV : ∀ x, x ∈ V → x < IN) :
    StableP (fun m => Ptrs m ptrs ls) V := fun m m' hm hag => hm.stable hag hV

theorem Ptrs.push {m : Mem} {ptrs : List ℕ} {ls : List (List ℕ)} {F : ℕ} {front : List ℕ}
    (h : Ptrs m ptrs ls) (hf : ArrIs m F front) : Ptrs m (ptrs ++ [m F]) (ls ++ [front]) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [h1], fun i hi => ?_⟩
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i ptrs.length with hlt | hge
  · rw [List.getElem_append_left hlt, List.getD_append _ _ _ _ (by omega)]
    exact h2 i hlt
  · have hi' : i = ptrs.length := by omega
    subst hi'
    rw [List.getElem_append_right (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.sub_self, List.getElem_cons_zero, h1, List.getD_cons_zero]
    exact hf

theorem Ptrs.nil (m : Mem) : Ptrs m [] [] := ⟨rfl, fun i hi => by simp at hi⟩

/-- `LAYS` holds the layers `ls` (an array of pointers to arrays). -/
def LaysAt (m : Mem) (ls : List (List ℕ)) : Prop := ∃ ptrs, ArrIs m LAYS ptrs ∧ Ptrs m ptrs ls

/-- `D := [M[A]]` (a fresh one-element array). -/
def arr1M (D A : ℕ) : Cmd :=
  .seq (mov D HP) (.seq (store D ONE) (.seq (add HP HP ONE) (.seq (store HP A) (add HP HP ONE))))

theorem arr1M_spec (D A : ℕ) (hD : 5 ≤ D ∧ D < IN) (hA : 5 ≤ A ∧ A < IN) (hAD : A ≠ D) (Pre : Mem → Prop)
    (hctx : ∀ m, Pre m → Ctx m) :
    RSpec (arr1M D A) [D] 5 Pre
      (fun m m' => m' D = m HP ∧ m' (m HP) = 1 ∧ m' (m HP + 1) = m A ∧ m' HP = m HP + 2) := by
  intro m0 hm0
  obtain ⟨hone, _, hhp⟩ := hctx m0 hm0
  obtain ⟨hdr, hhdr⟩ : ∃ hdr, hdr = m0 HP := ⟨_, rfl⟩
  have hhdrIN : IN ≤ hdr := by rw [hhdr]; exact hhp
  have hDH : D ≠ HP := by addr3
  have hDhdr : D ≠ hdr := by omega
  have hDhdr1 : D ≠ hdr + 1 := by omega
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m0.write D hdr := ⟨_, rfl⟩
  have e1 : Cmd.Exec (mov D HP) m0 m1 1 := by
    have := Exec.mov D HP m0; rwa [← hhdr, ← hm1] at this
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write hdr 1 := ⟨_, rfl⟩
  have e2 : Cmd.Exec (store D ONE) m1 m2 1 := by
    have := Exec.store D ONE m1
    rw [hm1, Mem.write_same, Mem.write_ne _ _ (by addr3), hone] at this
    rw [hm2, hm1]; exact this
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write HP (hdr + 1) := ⟨_, rfl⟩
  have e3 : Cmd.Exec (add HP HP ONE) m2 m3 1 := by
    have := Exec.add HP HP ONE m2
    rw [hm2, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm1, Mem.write_ne _ _ (Ne.symm hDH),
      Mem.write_ne _ _ (by addr3), hone, ← hhdr] at this
    rw [hm3, hm2, hm1]; exact this
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (hdr + 1) (m0 A) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (store HP A) m3 m4 1 := by
    have := Exec.store HP A m3
    rw [hm3, Mem.write_same, Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by omega), hm1,
      Mem.write_ne _ _ hAD] at this
    rw [hm4, hm3, hm2, hm1]; exact this
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write HP (hdr + 2) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add HP HP ONE) m4 m5 1 := by
    have := Exec.add HP HP ONE m4
    rw [hm4, Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3), hm3, Mem.write_same,
      Mem.write_ne _ _ (by addr3), hm2, Mem.write_ne _ _ (by addr3), hm1, Mem.write_ne _ _ (by addr3), hone] at this
    rw [hm5, hm4, hm3, hm2, hm1]; exact this
  have q5 : ∀ x, x ≠ HP → x ≠ hdr → x ≠ hdr + 1 → x ≠ D → m5 x = m0 x :=
    fun x h1 h2 h3 h4 => by
      rw [hm5, Mem.write_ne _ _ h1, hm4, Mem.write_ne _ _ h3, hm3, Mem.write_ne _ _ h1, hm2, Mem.write_ne _ _ h2,
        hm1, Mem.write_ne _ _ h4]
  refine ⟨m5, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 e5))), by omega, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x hx hxV => ?_, by rw [hm5, Mem.write_same]; omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxV
    exact q5 x hxV.1 (by omega) (by omega) hxV.2
  · rw [← hhdr, hm5, Mem.write_ne _ _ hDH, hm4, Mem.write_ne _ _ hDhdr1, hm3, Mem.write_ne _ _ hDH, hm2,
      Mem.write_ne _ _ hDhdr, hm1, Mem.write_same]
  · rw [← hhdr, hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_ne _ _ (by omega), hm3, Mem.write_ne _ _ (by addr3),
      hm2, Mem.write_same]
  · rw [← hhdr, hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_same]
  · rw [hm5, Mem.write_same, hhdr]


theorem arrAt_one {m : Mem} {a : ℕ} (h : m a = 1) : arrAt m a = [m (a + 1)] :=
  arrAt_of_cells (by rw [h]; rfl) (fun i hi => by
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi; rfl)

theorem arrAt_nil {m : Mem} {a : ℕ} (h : m a = 0) : arrAt m a = [] := by
  unfold arrAt; rw [h]; rfl

theorem ArrIs.mov {m m' : Mem} {V : List ℕ} {P Q : ℕ} {l : List ℕ} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (hP : m' P = m Q) (h : ArrIs m Q l) : ArrIs m' P l := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hP]; exact h1, ?_, by rw [hP, hag.arrAt hV _ h1 h2]; exact h3⟩
  rw [hP, hag.heap hV _ h1 (by omega)]; exact le_trans h2 hag.2

theorem LaysAt.stable {m m' : Mem} {V : List ℕ} {ls : List (List ℕ)} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (hL : LAYS ∉ V) (h : LaysAt m ls) : LaysAt m' ls := by
  obtain ⟨ptrs, h1, h2⟩ := h
  exact ⟨ptrs, h1.stable hag hV (by addrf) (by addrf) hL, h2.stable hag hV⟩

theorem nodeBound_le_seenBound (n : ℕ) : nodeBound n ≤ seenBound n :=
  Nat.le_mul_of_pos_right _ (by omega)

/-- One round of the layer loop: record the frontier, compute the next one. -/
def layerBody : Cmd :=
  .seq (arr1M (G_ 14) FRONT)
    (.seq (.seq (appendM 4 LAYS (G_ 14)) (mov (G_ 13) (OUT_ 4)))
      (.seq (mov LAYS (G_ 13))
        (.seq newFrontM
          (.seq (.seq (appendM 4 SEEN FRONT) (mov (G_ 13) (OUT_ 4)))
            (.seq (mov SEEN (G_ 13)) (mov FRONT (G_ 12)))))))

def layerBodyV : List ℕ :=
  [G_ 14] ++ ((Lvars 4 ++ [G_ 13]) ++ ([LAYS] ++ (newFrontV ++ ((Lvars 4 ++ [G_ 13]) ++ ([SEEN] ++ [FRONT])))))

theorem layerBodyV_safe : SafeVars layerBodyV :=
  SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)))
      (SafeVars.append (safeVars_of_decide _ (by decide))
        (SafeVars.append newFrontV_safe
          (SafeVars.append (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)))
            (SafeVars.append (safeVars_of_decide _ (by decide)) (safeVars_of_decide _ (by decide)))))))

def layerBodyB (n : ℕ) : ℕ :=
  5 + ((2 * (2 * n + 3) * 12 + 15 + 1) + (1 + ((nodeBound n * (frontB n + 14) + 9 + 1) +
    ((2 * seenBound n * 12 + 15 + 1) + (1 + 1)))))

theorem layerBody_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (seen front : List ℕ) (ls : List (List ℕ))
    (n f : ℕ) (ptrs : List ℕ) (hn : Sized n g) (hU : U.length ≤ flowBound n)
    (hseen : seen.length ≤ seenBound n) (hfront : front.length ≤ nodeBound n) (hls : ls.length ≤ 2 * n + 3) :
    RSpec layerBody layerBodyV (layerBodyB n)
      (fun m => LCtx k g U seen front m ∧ m FRONT = f ∧ ArrIs m LAYS ptrs ∧ Ptrs m ptrs ls)
      (fun _ m' => LCtx k g U (seen ++ front) ((g.networkL g.base.canonIds).newFront U seen front) m' ∧
        LaysAt m' (ls ++ [front])) := by
  intro m0 hm0
  obtain ⟨hL0, hf0, hlays0, hptrs0⟩ := hm0
  have hctx0 := hL0.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hptrs0' : Ptrs m0 (ptrs ++ [f]) (ls ++ [front]) := by rw [← hf0]; exact hptrs0.push hL0.2.2
  have hlen : ptrs.length = ls.length := hptrs0.1
  have hs2 : SafeVars (Lvars 4 ++ [G_ 13]) :=
    SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hV2 : ∀ x, x ∈ Lvars 4 ++ [G_ 13] → x < IN := fun x hx => (hs2 x hx).2.1
  -- `G_ 14 := [FRONT]`
  obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b, h1c, h1d⟩ :=
    arr1M_spec (G_ 14) FRONT (by constructor <;> addr3) (by constructor <;> addrf) (by addrf) Ctx
      (fun m hm => hm) m0 hctx0
  have hV1 : ∀ x, x ∈ [G_ 14] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addr3
  have hL1 : LCtx k g U seen front m1 :=
    LCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) m0 m1 hL0 ag1
  have hlays1 : ArrIs m1 LAYS ptrs := hlays0.stable ag1 hV1 (by addrf) (by addrf) (by decide)
  have hptrs1 := hptrs0'.stable ag1 hV1
  have harr1 : ArrIs m1 (G_ 14) [f] :=
    ArrIs.of_out hctx0.2.2 h1a (by rw [arrAt_one h1b, h1c, hf0]) (by rw [List.length_singleton]; omega)
  -- `G_ 13 := LAYS ++ G_ 14`
  obtain ⟨m2, k2, e2, hk2, ag2, harr2⟩ :=
    appendM_arr_spec 4 LAYS (G_ 14) (G_ 13) (2 * n + 3) ptrs [f] (by norm_num) (by constructor <;> addrf)
      (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addr3)
      (fun m => Ctx m ∧ ArrIs m LAYS ptrs ∧ ArrIs m (G_ 14) [f]) (fun m hm => hm.1) (fun m hm => hm.2.1)
      (fun m hm => hm.2.2) ⟨by omega, by simp⟩ m1 ⟨hL1.ctx, hlays1, harr1⟩
  have hL2 : LCtx k g U seen front m2 :=
    LCtx.stableP hs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m1 m2 hL1 ag2
  have hptrs2 := hptrs1.stable ag2 hV2
  -- `LAYS := G_ 13`
  obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b⟩ := movM_spec (G_ 13) LAYS (by constructor <;> addrf) Ctx m2 hL2.ctx
  have hV3 : ∀ x, x ∈ [LAYS] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hL3 : LCtx k g U seen front m3 :=
    LCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) m2 m3 hL2 ag3
  have hlays3 : ArrIs m3 LAYS (ptrs ++ [f]) := harr2.mov ag3 hV3 h3a
  have hptrs3 := hptrs2.stable ag3 hV3
  -- `G_ 12 := newFront U seen front`
  obtain ⟨m4, k4, e4, hk4, ag4, hnf4⟩ := newFrontM_spec k g U seen front n hn hU hseen hfront m3 hL3
  have hV4 : ∀ x, x ∈ newFrontV → x < IN := fun x hx => (newFrontV_safe x hx).2.1
  have hL4 : LCtx k g U seen front m4 :=
    LCtx.stableP newFrontV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) m3 m4 hL3 ag4
  have hlays4 : ArrIs m4 LAYS (ptrs ++ [f]) := hlays3.stable ag4 hV4 (by addrf) (by addrf) (by decide)
  have hptrs4 := hptrs3.stable ag4 hV4
  -- `G_ 13 := SEEN ++ FRONT`
  obtain ⟨m5, k5, e5, hk5, ag5, harr5⟩ :=
    appendM_arr_spec 4 SEEN FRONT (G_ 13) (seenBound n) seen front (by norm_num) (by constructor <;> addrf)
      (by constructor <;> addrf) (by decide) (by decide) (by constructor <;> addr3)
      (fun m => Ctx m ∧ ArrIs m SEEN seen ∧ ArrIs m FRONT front) (fun m hm => hm.1) (fun m hm => hm.2.1)
      (fun m hm => hm.2.2) ⟨hseen, le_trans hfront (nodeBound_le_seenBound n)⟩ m4 ⟨hL4.ctx, hL4.2.1, hL4.2.2⟩
  have hF5 : FCtx k g U m5 :=
    FCtx.stableP hs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) m4 m5 hL4.1 ag5
  have hnf5 := hnf4.stable ag5 hV2 (by addr3) (by addr3) (by decide)
  have hlays5 := hlays4.stable ag5 hV2 (by addrf) (by addrf) (by decide)
  have hptrs5 := hptrs4.stable ag5 hV2
  -- `SEEN := G_ 13`
  obtain ⟨m6, k6, e6, hk6, ag6, h6a, h6b⟩ := movM_spec (G_ 13) SEEN (by constructor <;> addrf) Ctx m5 hF5.ctx
  have hV6 : ∀ x, x ∈ [SEEN] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hF6 : FCtx k g U m6 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m5 m6 hF5 ag6
  have hseen6 : ArrIs m6 SEEN (seen ++ front) := harr5.mov ag6 hV6 h6a
  have hnf6 := hnf5.stable ag6 hV6 (by addr3) (by addr3) (by decide)
  have hlays6 := hlays5.stable ag6 hV6 (by addrf) (by addrf) (by decide)
  have hptrs6 := hptrs5.stable ag6 hV6
  -- `FRONT := G_ 12`
  obtain ⟨m7, k7, e7, hk7, ag7, h7a, h7b⟩ := movM_spec (G_ 12) FRONT (by constructor <;> addrf) Ctx m6 hF6.ctx
  have hV7 : ∀ x, x ∈ [FRONT] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hF7 : FCtx k g U m7 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m6 m7 hF6 ag7
  have hseen7 := hseen6.stable ag7 hV7 (by addrf) (by addrf) (by decide)
  have hfront7 : ArrIs m7 FRONT ((g.networkL g.base.canonIds).newFront U seen front) := hnf6.mov ag7 hV7 h7a
  have hlays7 := hlays6.stable ag7 hV7 (by addrf) (by addrf) (by decide)
  have hptrs7 := hptrs6.stable ag7 hV7
  refine ⟨m7, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5
    (Cmd.Exec.seq e6 e7))))), ?_, ag1.trans (ag2.trans (ag3.trans (ag4.trans (ag5.trans (ag6.trans ag7))))),
    ⟨hF7, hseen7, hfront7⟩, ptrs ++ [f], hlays7, hptrs7⟩
  simp only [layerBodyB]; omega

/-- The invariant of the layer loop after `j` rounds (relative to the state `m6` before the loop). -/
def LayInv (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (m6 : Mem) (j : ℕ) (m : Mem) : Prop :=
  Agree m6 m (layerBodyV ++ [I_ 5]) ∧
    LCtx k g U (layerState (g.networkL g.base.canonIds) U j).1 (layerState (g.networkL g.base.canonIds) U j).2 m ∧
    LaysAt m ((List.range j).map (fun t => (layerState (g.networkL g.base.canonIds) U t).2)) ∧
    m (I_ 5) = j ∧ m (CNT_ 5) = (g.networkL g.base.canonIds).nodes.length + 1

/-- The layers: `SEEN := []`, `FRONT := [s]`, `LAYS := []`, then `|nodes| + 1` rounds. -/
def layersM : Cmd :=
  .seq (emptyArrM SEEN) (.seq (arr1M FRONT NETS) (.seq (emptyArrM LAYS) (.seq (load (CNT_ 5) NETN)
    (.seq (add (CNT_ 5) (CNT_ 5) ONE) (.seq (setc (I_ 5) 0) (forLoop (I_ 5) (CNT_ 5) layerBody))))))

def layersV : List ℕ :=
  [SEEN] ++ ([FRONT] ++ ([LAYS] ++ (([CNT_ 5] ++ ([CNT_ 5] ++ [I_ 5])) ++ (layerBodyV ++ [I_ 5]))))

theorem layersV_safe : SafeVars layersV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
      (SafeVars.append layerBodyV_safe (safeVars_of_decide _ (by decide))))))

def layersB (n : ℕ) : ℕ := 3 + 5 + 3 + 1 + 1 + 1 + ((2 * n + 3) * (layerBodyB n + 3) + 2)

theorem layersM_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hn : Sized n g)
    (hU : U.length ≤ flowBound n) :
    RSpec layersM layersV (layersB n) (FCtx k g U)
      (fun _ m' => FCtx k g U m' ∧ ArrIs m' SEEN ((g.networkL g.base.canonIds).seen U) ∧
        LaysAt m' ((g.networkL g.base.canonIds).layers U)) := by
  intro m0 hm0
  have hctx0 := hm0.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hNL := netNodes_length_le hn
  have hNL1 := netNodes_length_pos g
  have hnetn0 : ArrIs m0 NETN (g.networkL g.base.canonIds).nodes := hm0.1.1.2.2.2
  have hnets0 : m0 NETS = g.netS := hm0.1.1.2.1
  -- `SEEN := []`
  obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b, h1c⟩ := emptyArrM_spec SEEN (by constructor <;> addrf) Ctx (fun m hm => hm) m0 hctx0
  have hV1 : ∀ x, x ∈ [SEEN] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hF1 : FCtx k g U m1 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m0 m1 hm0 ag1
  have hseen1 : ArrIs m1 SEEN [] := ArrIs.of_out hctx0.2.2 h1a (arrAt_nil h1b) (by rw [List.length_nil]; omega)
  have hnets1 : m1 NETS = g.netS := by rw [ag1.var NETS (lt_hp hhp0 (by decide)) (by decide) (by decide), hnets0]
  -- `FRONT := [s]`
  obtain ⟨m2, k2, e2, hk2, ag2, h2a, h2b, h2c, h2d⟩ :=
    arr1M_spec FRONT NETS (by constructor <;> addrf) (by constructor <;> addrn) (by addrf) Ctx (fun m hm => hm) m1 hF1.ctx
  have hV2 : ∀ x, x ∈ [FRONT] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hF2 : FCtx k g U m2 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m1 m2 hF1 ag2
  have hseen2 := hseen1.stable ag2 hV2 (by addrf) (by addrf) (by decide)
  have hfront2 : ArrIs m2 FRONT [(g.networkL g.base.canonIds).s] :=
    ArrIs.of_out hF1.ctx.2.2 h2a (by rw [arrAt_one h2b, h2c, hnets1]; rfl) (by rw [List.length_singleton]; omega)
  -- `LAYS := []`
  obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b, h3c⟩ := emptyArrM_spec LAYS (by constructor <;> addrf) Ctx (fun m hm => hm) m2 hF2.ctx
  have hV3 : ∀ x, x ∈ [LAYS] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hF3 : FCtx k g U m3 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m2 m3 hF2 ag3
  have hseen3 := hseen2.stable ag3 hV3 (by addrf) (by addrf) (by decide)
  have hfront3 := hfront2.stable ag3 hV3 (by addrf) (by addrf) (by decide)
  have hlays3 : LaysAt m3 [] :=
    ⟨[], ArrIs.of_out hF2.ctx.2.2 h3a (arrAt_nil h3b) (by rw [List.length_nil]; omega), Ptrs.nil m3⟩
  -- `CNT_ 5 := M[M[NETN]] + 1`, `I_ 5 := 0`
  obtain ⟨m4, k4, e4, hk4, ag4, h4a, h4b⟩ := loadM_spec NETN (CNT_ 5) (by constructor <;> addr3) Ctx m3 hF3.ctx
  have hV4 : ∀ x, x ∈ [CNT_ 5] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addr3
  have hF4 : FCtx k g U m4 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m3 m4 hF3 ag4
  have hnetn3 : ArrIs m3 NETN (g.networkL g.base.canonIds).nodes := hF3.1.1.2.2.2
  have h4cnt : m4 (CNT_ 5) = (g.networkL g.base.canonIds).nodes.length := by rw [h4a, hnetn3.len]
  have hone4 : m4 ONE = 1 := hF4.ctx.1
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (CNT_ 5) ((g.networkL g.base.canonIds).nodes.length + 1) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (add (CNT_ 5) (CNT_ 5) ONE) m4 m5 1 := by
    have := Exec.add (CNT_ 5) (CNT_ 5) ONE m4; rwa [h4cnt, hone4, ← hm5] at this
  have ag5 : Agree m4 m5 [CNT_ 5] := by rw [hm5]; exact Agree.write _ _ _ (by addr3)
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write (I_ 5) 0 := ⟨_, rfl⟩
  have e6 : Cmd.Exec (setc (I_ 5) 0) m5 m6 1 := by rw [hm6]; exact Exec.setc _ _ _
  have ag6 : Agree m5 m6 [I_ 5] := by rw [hm6]; exact Agree.write _ _ _ (by addr3)
  have hV5 : ∀ x, x ∈ [I_ 5] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addr3
  have ag46 : Agree m3 m6 ([CNT_ 5] ++ ([CNT_ 5] ++ [I_ 5])) := ag4.trans (ag5.trans ag6)
  have hV46 : ∀ x, x ∈ [CNT_ 5] ++ ([CNT_ 5] ++ [I_ 5]) → x < IN := fun x hx => by
    simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with h | h | h <;> subst h <;> addr3
  have hF6 : FCtx k g U m6 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m3 m6 hF3 ag46
  have hseen6 := hseen3.stable ag46 hV46 (by addrf) (by addrf) (by decide)
  have hfront6 := hfront3.stable ag46 hV46 (by addrf) (by addrf) (by decide)
  have hlays6 := hlays3.stable ag46 hV46 (by decide)
  have h6cnt : m6 (CNT_ 5) = (g.networkL g.base.canonIds).nodes.length + 1 := by
    rw [hm6, Mem.write_ne _ _ (by addr3), hm5, Mem.write_same]
  have h6i : m6 (I_ 5) = 0 := by rw [hm6, Mem.write_same]
  -- the loop
  have hVb : ∀ x, x ∈ layerBodyV → x < IN := fun x hx => (layerBodyV_safe x hx).2.1
  have hVb' : ∀ x, x ∈ layerBodyV ++ [I_ 5] → x < IN := fun x hx => by
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h | h
    · exact hVb x h
    · subst h; addr3
  have main := loopR_spec 5 (by norm_num) layerBody layerBodyV (layerBodyB n)
    ((g.networkL g.base.canonIds).nodes.length + 1) (LayInv k g U m6) hVb (by decide) (by decide)
    (fun j m hm => ⟨hm.2.2.2.1, hm.2.2.2.2, hm.2.1.ctx.1, hm.2.1.ctx.2.2⟩) ?_ 0 m6 (Nat.zero_le _)
    ⟨Agree.refl _ _, ⟨hF6, hseen6, hfront6⟩, hlays6, h6i, h6cnt⟩
  · obtain ⟨m', kk, e, inv', hk⟩ := main
    obtain ⟨ag', hL', hlays', _, _⟩ := inv'
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5
      (Cmd.Exec.seq e6 e))))), ?_, ?_, hL'.1, ?_, ?_⟩
    · have : ((g.networkL g.base.canonIds).nodes.length + 1 - 0) * (layerBodyB n + 3) ≤ (2 * n + 3) * (layerBodyB n + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [layersB]; omega
    · exact ag1.trans (ag2.trans (ag3.trans (ag46.trans ag')))
    · have : (g.networkL g.base.canonIds).seen U = (layerState (g.networkL g.base.canonIds) U
          ((g.networkL g.base.canonIds).nodes.length + 1)).1 := by
        rw [Network.seen, layers_eq, layerState_seen_eq]
      rw [this]; exact hL'.2.1
    · rw [layers_eq]; exact hlays'
  · -- the body
    intro j m hj hm
    obtain ⟨hag, hL, hlays, hi, hcnt⟩ := hm
    obtain ⟨ptrs, hlaysP, hptrs⟩ := hlays
    have hhp : 200 ≤ m HP := hL.ctx.2.2
    have hseenj : (layerState (g.networkL g.base.canonIds) U j).1.length ≤ seenBound n := by
      have := layerState_seen_le (g.networkL g.base.canonIds) U hNL1 j
      have : j * (g.networkL g.base.canonIds).nodes.length ≤ (2 * n + 2) * (2 * n + 3) :=
        Nat.mul_le_mul (by omega) (by omega)
      unfold seenBound; omega
    have hfrontj : (layerState (g.networkL g.base.canonIds) U j).2.length ≤ nodeBound n := by
      have := layerState_front_le (g.networkL g.base.canonIds) U hNL1 j
      unfold nodeBound; omega
    obtain ⟨m', kk, e, hk, agB, hL', hlays'⟩ := layerBody_spec k g U _ _ _ n (m FRONT) ptrs hn hU hseenj hfrontj
      (by rw [List.length_map, List.length_range]; omega) m ⟨hL, rfl, hlaysP, hptrs⟩
    have agW : Agree m' (m'.write (I_ 5) (j + 1)) [I_ 5] := Agree.write _ _ _ (by addr3)
    refine ⟨m', kk, e, hk, agB, ?_, ?_, ?_, by rw [Mem.write_same], ?_⟩
    · refine (hag.trans (agB.trans agW)).mono (fun x hx => ?_)
      simp only [List.mem_append, List.mem_singleton] at hx ⊢
      tauto
    · show LCtx k g U ((layerState (g.networkL g.base.canonIds) U j).1 ++ (layerState (g.networkL g.base.canonIds) U j).2)
        ((g.networkL g.base.canonIds).newFront U (layerState (g.networkL g.base.canonIds) U j).1
          (layerState (g.networkL g.base.canonIds) U j).2) _
      exact LCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) m' _ hL' agW
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact hlays'.stable agW hV5 (by decide)
    · rw [Mem.write_ne _ _ (by addr3), agB.var (CNT_ 5) (lt_hp hhp (by decide)) (by decide) (by decide), hcnt]


/-! ### The augmenting path -/

/-- One step of the path extraction on a (reversed) layer: mode `0` searches for the layer
containing the current node, mode `1` descends, any other mode is inert. The accumulated
path is kept reversed. -/
def exStep (N : Network ℕ) (U : List (ℕ × ℕ)) (st : ℕ × ℕ × List ℕ) (L : List ℕ) : ℕ × ℕ × List ℕ :=
  if st.1 = 0 then (if st.2.1 ∈ L then (1, st.2.1, st.2.1 :: st.2.2) else st)
  else if st.1 = 1 then
    (match L.find? (fun x => decide (N.ResL U x st.2.1)) with
      | some x => (1, x, x :: st.2.2)
      | none => (2, st.2.1, st.2.2))
  else st

theorem foldl_exStep_two (N : Network ℕ) (U : List (ℕ × ℕ)) (y : ℕ) (acc : List ℕ) :
    ∀ rls, List.foldl (exStep N U) (2, y, acc) rls = (2, y, acc)
  | [] => rfl
  | L :: rls => by
      simp only [List.foldl_cons]
      rw [show exStep N U (2, y, acc) L = (2, y, acc) by simp [exStep]]
      exact foldl_exStep_two N U y acc rls

theorem foldl_exStep_one (N : Network ℕ) (U : List (ℕ × ℕ)) :
    ∀ (rls : List (List ℕ)) (y : ℕ) (acc : List ℕ),
      (List.foldl (exStep N U) (1, y, y :: acc) rls).2.2 = (N.descendR U rls y).reverse ++ acc
  | [], y, acc => by simp [Network.descendR]
  | L :: rls, y, acc => by
      simp only [List.foldl_cons, Network.descendR]
      cases hf : L.find? (fun x => decide (N.ResL U x y)) with
      | none =>
        rw [show exStep N U (1, y, y :: acc) L = (2, y, y :: acc) by simp [exStep, hf], foldl_exStep_two]
        simp
      | some x =>
        rw [show exStep N U (1, y, y :: acc) L = (1, x, x :: (y :: acc)) by simp [exStep, hf],
          foldl_exStep_one N U rls x (y :: acc)]
        simp

theorem foldl_exStep_zero (N : Network ℕ) (U : List (ℕ × ℕ)) :
    ∀ (rls : List (List ℕ)) (y : ℕ),
      (List.foldl (exStep N U) (0, y, []) rls).2.2 = (N.extractR U rls y).reverse
  | [], y => by simp [Network.extractR]
  | L :: rls, y => by
      simp only [List.foldl_cons, Network.extractR]
      by_cases hy : y ∈ L
      · rw [show exStep N U (0, y, []) L = (1, y, [y]) by simp [exStep, hy], if_pos hy,
          foldl_exStep_one N U rls y []]
        simp
      · rw [show exStep N U (0, y, []) L = (0, y, []) by simp [exStep, hy], if_neg hy]
        exact foldl_exStep_zero N U rls y

theorem augPath_eq (N : Network ℕ) (U : List (ℕ × ℕ)) :
    N.augPath U = (List.foldl (exStep N U) (0, N.t, []) (N.layers U).reverse).2.2 := by
  rw [Network.augPath, foldl_exStep_zero]

theorem exStep_length (N : Network ℕ) (U : List (ℕ × ℕ)) (st : ℕ × ℕ × List ℕ) (L : List ℕ) :
    (exStep N U st L).2.2.length ≤ st.2.2.length + 1 := by
  unfold exStep
  split
  · split <;> simp
  · split
    · split <;> simp
    · simp

theorem foldl_exStep_length (N : Network ℕ) (U : List (ℕ × ℕ)) :
    ∀ (rls : List (List ℕ)) (st : ℕ × ℕ × List ℕ),
      (List.foldl (exStep N U) st rls).2.2.length ≤ st.2.2.length + rls.length
  | [], st => by simp
  | L :: rls, st => by
      simp only [List.foldl_cons, List.length_cons]
      have := foldl_exStep_length N U rls (exStep N U st L)
      have := exStep_length N U st L
      omega

theorem find?_of_first (p : ℕ → Bool) : ∀ (l : List ℕ) (i : ℕ) (hi : i < l.length), p l[i] = true →
    (∀ j, (hj : j < i) → p (l[j]'(by omega)) = false) → l.find? p = some l[i]
  | [], i, hi, _, _ => by simp at hi
  | a :: l, 0, _, hp, _ => by simp at hp; simp [hp]
  | a :: l, i + 1, hi, hp, hmin => by
      have ha : p a = false := hmin 0 (by omega)
      rw [List.find?_cons_of_neg (by simp [ha])]
      simp only [List.getElem_cons_succ] at hp ⊢
      exact find?_of_first p l i (by simp at hi; omega) hp (fun j hj => by
        have := hmin (j + 1) (by omega); simpa using this)

theorem find?_eq_firstIndex (p : ℕ → Bool) (l : List ℕ) :
    l.find? p = if Instance.firstIndex (fun i => p (l.getD i 0)) l.length < l.length
      then some (l.getD (Instance.firstIndex (fun i => p (l.getD i 0)) l.length) 0) else none := by
  rcases Instance.firstIndex_spec (fun i => p (l.getD i 0)) l.length with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, List.getD_eq_getElem _ _ h1]
    apply find?_of_first p l _ h1
    · rw [← List.getD_eq_getElem _ _ h1]; exact h2
    · intro j hj
      have := h3 j hj
      rw [List.getD_eq_getElem _ _ (by omega)] at this
      exact this
  · rw [if_neg (by omega), List.find?_eq_none]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    have := h2 j hj
    rw [List.getD_eq_getElem _ _ hj] at this
    simp [this]

theorem RSpec.ite' {c₁ c₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {Post₁ Post₂ : Mem → Mem → Prop} (a b : ℕ) (h₁ : RSpec c₁ V₁ B₁ (fun m => Pre m ∧ m a = m b) Post₁)
    (h₂ : RSpec c₂ V₂ B₂ (fun m => Pre m ∧ m a ≠ m b) Post₂) :
    RSpec (.ite (.eq a b) c₁ c₂) (V₁ ++ V₂) (B₁ + B₂ + 2) Pre
      (fun m m' => if m a = m b then Post₁ m m' else Post₂ m m') := by
  intro m hm
  dsimp only
  by_cases h : m a = m b
  · have hc : (Cond.eq a b).eval m = true := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp⟩ := h₁ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_true hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_left _ hx),
      by rw [if_pos h]; exact hp⟩
  · have hc : (Cond.eq a b).eval m = false := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp⟩ := h₂ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_false hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_right _ hx),
      by rw [if_neg h]; exact hp⟩

theorem RSpec.iteLt' {c₁ c₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {Post₁ Post₂ : Mem → Mem → Prop} (a b : ℕ) (h₁ : RSpec c₁ V₁ B₁ (fun m => Pre m ∧ m a < m b) Post₁)
    (h₂ : RSpec c₂ V₂ B₂ (fun m => Pre m ∧ ¬ m a < m b) Post₂) :
    RSpec (.ite (.lt a b) c₁ c₂) (V₁ ++ V₂) (B₁ + B₂ + 2) Pre
      (fun m m' => if m a < m b then Post₁ m m' else Post₂ m m') := by
  intro m hm
  dsimp only
  by_cases h : m a < m b
  · have hc : (Cond.lt a b).eval m = true := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp⟩ := h₁ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_true hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_left _ hx),
      by rw [if_pos h]; exact hp⟩
  · have hc : (Cond.lt a b).eval m = false := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hp⟩ := h₂ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_false hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_right _ hx),
      by rw [if_neg h]; exact hp⟩

theorem nopM_spec (Pre : Mem → Prop) : RSpec nop [] 1 Pre (fun m m' => m' = m) :=
  fun m _ => ⟨m, 1, Exec.nop m, le_rfl, Agree.refl m [], rfl⟩

theorem setcM_spec (D v : ℕ) (hD : 5 ≤ D ∧ D < IN) (Pre : Mem → Prop) :
    RSpec (setc D v) [D] 1 Pre (fun m m' => m' D = v ∧ m' HP = m HP) := by
  intro m _
  exact ⟨m.write D v, 1, Exec.setc _ _ _, le_rfl, Agree.write m D _ (by addr3),
    Mem.write_same _ _ _, Mem.write_ne _ _ (by addr3)⟩

/-- `PATH := [M[Y]] ++ PATH`. -/
def consPathM (Y : ℕ) : Cmd :=
  .seq (arr1M (G_ 14) Y) (.seq (.seq (appendM 4 (G_ 14) PATH) (mov (G_ 13) (OUT_ 4))) (mov PATH (G_ 13)))

def consPathV : List ℕ := [G_ 14] ++ ((Lvars 4 ++ [G_ 13]) ++ [PATH])

theorem consPathV_safe : SafeVars consPathV :=
  SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)))
      (safeVars_of_decide _ (by decide)))

def consPathB (n : ℕ) : ℕ := 5 + ((2 * (n + 1) * 12 + 15 + 1) + 1)

theorem consPathM_spec (Y n : ℕ) (hY : 5 ≤ Y ∧ Y < IN) (hYV : Y ∉ consPathV) (acc : List ℕ) (y : ℕ)
    (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m) (hacc : ∀ m, Pre m → ArrIs m PATH acc ∧ m Y = y)
    (hn : acc.length ≤ n) :
    RSpec (consPathM Y) consPathV (consPathB n) Pre (fun _ m' => ArrIs m' PATH (y :: acc)) := by
  intro m0 hm0
  have hctx0 := hctx m0 hm0
  obtain ⟨hacc0, hy0⟩ := hacc m0 hm0
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hY14 : Y ≠ G_ 14 := fun h => hYV (by rw [h]; simp [consPathV])
  have hYP : Y ≠ PATH := fun h => hYV (by rw [h]; simp [consPathV])
  have hV1 : ∀ x, x ∈ [G_ 14] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addr3
  have hs2 : SafeVars (Lvars 4 ++ [G_ 13]) :=
    SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide))
  have hV2 : ∀ x, x ∈ Lvars 4 ++ [G_ 13] → x < IN := fun x hx => (hs2 x hx).2.1
  obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b, h1c, h1d⟩ :=
    arr1M_spec (G_ 14) Y (by constructor <;> addr3) hY hY14 Ctx (fun m hm => hm) m0 hctx0
  have hctx1 : Ctx m1 := Ctx.of_agree hctx0 ag1 (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; addr3)
  have harr1 : ArrIs m1 (G_ 14) [y] :=
    ArrIs.of_out hctx0.2.2 h1a (by rw [arrAt_one h1b, h1c, hy0]) (by rw [List.length_singleton]; omega)
  have hacc1 : ArrIs m1 PATH acc := hacc0.stable ag1 hV1 (by addrf) (by addrf) (by decide)
  obtain ⟨m2, k2, e2, hk2, ag2, harr2⟩ :=
    appendM_arr_spec 4 (G_ 14) PATH (G_ 13) (n + 1) [y] acc (by norm_num) (by constructor <;> addr3)
      (by constructor <;> addrf) (by decide) (by decide) (by constructor <;> addr3)
      (fun m => Ctx m ∧ ArrIs m (G_ 14) [y] ∧ ArrIs m PATH acc) (fun m hm => hm.1) (fun m hm => hm.2.1)
      (fun m hm => hm.2.2) ⟨by simp, by omega⟩ m1 ⟨hctx1, harr1, hacc1⟩
  have hctx2 : Ctx m2 := Ctx.of_agree hctx1 ag2 (fun x hx => (hs2 x hx).1)
  obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b⟩ := movM_spec (G_ 13) PATH (by constructor <;> addrf) Ctx m2 hctx2
  have hV3 : ∀ x, x ∈ [PATH] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), ?_, ag1.trans (ag2.trans ag3), ?_⟩
  · simp only [consPathB]; omega
  · rw [← List.singleton_append]; exact harr2.mov ag3 hV3 h3a


/-- `FLAG := ResL U layer[X_ 4] CUR`, where the layer is the array at `X_ 5`. -/
def descTest : Cmd := .seq (elemM (X_ 5) (X_ 4) (G_ 22)) (resTest (G_ 22) CUR)

def descV : List ℕ := [G_ 22] ++ resV

theorem descV_safe : SafeVars descV := SafeVars.append (safeVars_of_decide _ (by decide)) resV_safe

def descB (n : ℕ) : ℕ :=
  3 + (5 + (5 + ((arcBound n * 23 + 10) + (flowBound n * 23 + 10 + 1) + 3 + (flowBound n * 23 + 10) + 3)))

theorem descTest_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hn : Sized n g)
    (hU : U.length ≤ flowBound n) (L : List ℕ) :
    TestSpec descTest descV (descB n)
      (fun m => (FCtx k g U m ∧ ArrIs m (X_ 5) L ∧ m (G_ 21) = L.length) ∧ m (X_ 4) < m (G_ 21))
      (fun m => decide ((g.networkL g.base.canonIds).ResL U (L.getD (m (X_ 4)) 0) (m CUR))) := by
  have hc := elemM_spec (X_ 5) (X_ 4) (G_ 22) (by constructor <;> addr3) (by addr3) (by addr3)
    (fun m => (FCtx k g U m ∧ ArrIs m (X_ 5) L ∧ m (G_ 21) = L.length) ∧ m (X_ 4) < m (G_ 21))
    (fun m hm => hm.1.1.ctx) (fun m hm => hm.1.2.1.1)
  have ht := resTest_spec k g U n (flowBound n) hn hU (G_ 22) CUR (by constructor <;> addr3)
    (by constructor <;> addrf) (by decide) (by decide) (FCtx k g U) (fun m hm => hm)
    (FCtx.stableP resV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  refine (TestSpec.after hc ht ?_ ?_).mono (fun x hx => hx) le_rfl (fun m hm => hm)
  · intro m m₁ hm hag _
    exact FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) m m₁ hm.1.1 hag
  · intro m m₁ hm hag hp
    have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
    obtain ⟨hIN, hroom, harr⟩ := hm.1.2.1
    have hlt : m (X_ 4) < L.length := by rw [← hm.1.2.2]; exact hm.2
    subst harr
    show decide ((g.networkL g.base.canonIds).ResL U (m₁ (G_ 22)) (m₁ CUR)) = _
    rw [hp.1, hag.var CUR (lt_hp hhp (by decide)) (by decide) (by decide), List.getD_eq_getElem _ _ hlt,
      arrAt_getElem]

/-- The machine state of the path extraction: `MDE`, `CUR`, and the array `PATH`. -/
def XState (st : ℕ × ℕ × List ℕ) (m : Mem) : Prop := m MDE = st.1 ∧ m CUR = st.2.1 ∧ ArrIs m PATH st.2.2

theorem XState.stable {m m' : Mem} {V : List ℕ} {st : ℕ × ℕ × List ℕ} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (hM : MDE ∉ V) (hC : CUR ∉ V) (hP : PATH ∉ V) (hhp : 200 ≤ m HP)
    (h : XState st m) : XState st m' :=
  ⟨by rw [hag.var MDE (lt_hp hhp (by decide)) (by decide) hM]; exact h.1,
    by rw [hag.var CUR (lt_hp hhp (by decide)) (by decide) hC]; exact h.2.1,
    h.2.2.stable hag hV (by addrf) (by addrf) hP⟩

/-- One (reversed) layer of the path extraction; the layer is the array at `X_ 5`. -/
def pathBody : Cmd :=
  .ite (.eq MDE ZERO)
    (.seq (memValM 4 (X_ 5) CUR) (.ite (.eq FLAG ONE) (.seq (setc MDE 1) (consPathM CUR)) nop))
    (.ite (.eq MDE ONE)
      (.seq (load (G_ 21) (X_ 5)) (.seq (firstIndexM 4 (G_ 20) (G_ 21) descTest)
        (.ite (.lt (G_ 20) (G_ 21)) (.seq (elemM (X_ 5) (G_ 20) CUR) (consPathM CUR)) (setc MDE 2))))
      nop)

def pathV0 : List ℕ := (Lvars 4 ++ FLAG :: [FLAG]) ++ ([MDE] ++ consPathV)
def pathV1 : List ℕ := [G_ 21] ++ (fiV 4 (G_ 20) descV ++ ([CUR] ++ (consPathV ++ [MDE])))
def pathV : List ℕ := pathV0 ++ pathV1

theorem pathV0_safe : SafeVars pathV0 :=
  SafeVars.append (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)))
    (SafeVars.append (safeVars_of_decide _ (by decide)) consPathV_safe)

theorem fiV_safe' (L R : ℕ) (hL : L ≤ 9) (hR : 5 ≤ R ∧ R < IN ∧ R ∉ instVars) {V : List ℕ} (hV : SafeVars V) :
    SafeVars (fiV L R V) := by
  have hLv := safeVars_Lvars L hL
  intro x hx
  simp only [fiV, List.mem_cons] at hx
  rcases hx with h | h | h | h | h | h
  · subst h; exact hR
  · subst h; exact hLv _ (by simp [Lvars])
  · subst h; exact hLv _ (by simp [Lvars])
  · subst h; exact hLv _ (by simp [Lvars])
  · subst h; exact safeVars_FLAG
  · exact hV x h

theorem pathV1_safe : SafeVars pathV1 :=
  SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (fiV_safe' 4 (G_ 20) (by norm_num) (safeVars_G 20 (by norm_num)) descV_safe)
      (SafeVars.append (safeVars_of_decide _ (by decide))
        (SafeVars.append consPathV_safe (safeVars_of_decide _ (by decide)))))

theorem pathV_safe : SafeVars pathV := SafeVars.append pathV0_safe pathV1_safe

def pathB (n : ℕ) : ℕ :=
  (nodeBound n * (3 + 11) + 10) + consPathB (2 * n + 3) + (nodeBound n * (descB n + 9) + 5) +
    consPathB (2 * n + 3) + 20

theorem pathBody_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hn : Sized n g)
    (hU : U.length ≤ flowBound n) (st : ℕ × ℕ × List ℕ) (L : List ℕ) (hL : L.length ≤ nodeBound n)
    (hacc : st.2.2.length ≤ 2 * n + 3) :
    RSpec pathBody pathV (pathB n) (fun m => FCtx k g U m ∧ XState st m ∧ ArrIs m (X_ 5) L)
      (fun _ m' => FCtx k g U m' ∧ XState (exStep (g.networkL g.base.canonIds) U st L) m') := by
  obtain ⟨mode, y, acc⟩ := st
  intro m0 hm0
  obtain ⟨hF0, ⟨hM0, hC0, hP0⟩, hL0⟩ := hm0
  simp only at hM0 hC0 hP0 hacc
  have hctx0 := hF0.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hzero0 : m0 ZERO = 0 := hctx0.2.1
  have hone0 : m0 ONE = 1 := hctx0.1
  have hV0 : ∀ x, x ∈ Lvars 4 ++ FLAG :: [FLAG] → x < IN := fun x hx =>
    (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)) x hx).2.1
  have hVc : ∀ x, x ∈ consPathV → x < IN := fun x hx => (consPathV_safe x hx).2.1
  have hVfi : ∀ x, x ∈ fiV 4 (G_ 20) descV → x < IN := fun x hx =>
    (fiV_safe' 4 (G_ 20) (by norm_num) (safeVars_G 20 (by norm_num)) descV_safe x hx).2.1
  by_cases h0 : mode = 0
  · subst h0
    have hc0 : (Cond.eq MDE ZERO).eval m0 = true := by simp [Cond.eval, hM0, hzero0]
    -- `FLAG := (CUR ∈ layer)`
    obtain ⟨m1, k1, e1, hk1, ag1, hfl1⟩ := memValM_spec 4 (X_ 5) CUR (nodeBound n) (by norm_num)
      (by constructor <;> addr3) (by constructor <;> addrf) (by decide) (by decide) (by decide) (by decide)
      (fun m => FCtx k g U m ∧ ArrIs m (X_ 5) L) (fun m hm => hm.1.ctx)
      (fun m hm => ⟨hm.2.1, hm.2.2.1, by rw [hm.2.len]; exact hL⟩)
      ((FCtx.stableP (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).and
        (ArrIs.stableP (P := X_ 5) hV0 (by addr3) (by addr3) (by decide))) m0 ⟨hF0, hL0⟩
    have hF1 : FCtx k g U m1 :=
      FCtx.stableP (SafeVars.append (safeVars_Lvars 4 (by norm_num)) (safeVars_of_decide _ (by decide)))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m0 m1 hF0 ag1
    have hM1 : m1 MDE = 0 := by rw [ag1.var MDE (lt_hp hhp0 (by decide)) (by decide) (by decide)]; exact hM0
    have hC1 : m1 CUR = y := by rw [ag1.var CUR (lt_hp hhp0 (by decide)) (by decide) (by decide)]; exact hC0
    have hP1 : ArrIs m1 PATH acc := hP0.stable ag1 hV0 (by addrf) (by addrf) (by decide)
    have hone1 : m1 ONE = 1 := hF1.ctx.1
    dsimp only at hfl1
    rw [hC0, hL0.2.2] at hfl1
    by_cases hy : y ∈ L
    · have hc1 : (Cond.eq FLAG ONE).eval m1 = true := by
        simp only [Cond.eval, hfl1, hone1, hy, decide_true, bitv]; rfl
      obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write MDE 1 := ⟨_, rfl⟩
      have e2 : Cmd.Exec (setc MDE 1) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
      have ag2 : Agree m1 m2 [MDE] := by rw [hm2]; exact Agree.write _ _ _ (by addrf)
      have hVm : ∀ x, x ∈ [MDE] → x < IN := fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; addrf
      have hF2 : FCtx k g U m2 :=
        FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) m1 m2 hF1 ag2
      have hM2 : m2 MDE = 1 := by rw [hm2, Mem.write_same]
      have hC2 : m2 CUR = y := by rw [hm2, Mem.write_ne _ _ (by addrf)]; exact hC1
      have hP2 : ArrIs m2 PATH acc := hP1.stable ag2 hVm (by addrf) (by addrf) (by decide)
      obtain ⟨m3, k3, e3, hk3, ag3, hP3⟩ := consPathM_spec CUR (2 * n + 3) (by constructor <;> addrf) (by decide)
        acc y (fun m => Ctx m ∧ ArrIs m PATH acc ∧ m CUR = y) (fun m hm => hm.1) (fun m hm => hm.2) hacc m2
        ⟨hF2.ctx, hP2, hC2⟩
      have hhp2 : 200 ≤ m2 HP := hF2.ctx.2.2
      have hF3 : FCtx k g U m3 :=
        FCtx.stableP consPathV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) m2 m3 hF2 ag3
      refine ⟨m3, _, Cmd.Exec.ite_true hc0 (Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc1 (Cmd.Exec.seq e2 e3))), ?_,
        (ag1.trans (ag2.trans ag3)).mono (fun x hx => List.mem_append_left _ hx), hF3, ?_⟩
      · simp only [pathB]; omega
      · rw [show exStep (g.networkL g.base.canonIds) U (0, y, acc) L = (1, y, y :: acc) by simp [exStep, hy]]
        exact ⟨by rw [ag3.var MDE (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact hM2,
          by rw [ag3.var CUR (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact hC2, hP3⟩
    · have hc1 : (Cond.eq FLAG ONE).eval m1 = false := by
        simp only [Cond.eval, hfl1, hone1, hy, decide_false, bitv]; rfl
      refine ⟨m1, _, Cmd.Exec.ite_true hc0 (Cmd.Exec.seq e1 (Cmd.Exec.ite_false hc1 (Exec.nop m1))), ?_,
        ag1.mono (fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)), hF1, ?_⟩
      · simp only [pathB]; omega
      · rw [show exStep (g.networkL g.base.canonIds) U (0, y, acc) L = (0, y, acc) by simp [exStep, hy]]
        exact ⟨hM1, hC1, hP1⟩
  · have hc0 : (Cond.eq MDE ZERO).eval m0 = false := by simp [Cond.eval, hM0, hzero0, h0]
    by_cases h1 : mode = 1
    · subst h1
      have hc1 : (Cond.eq MDE ONE).eval m0 = true := by simp [Cond.eval, hM0, hone0]
      -- `G_ 21 := |layer|`
      obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b⟩ := loadM_spec (X_ 5) (G_ 21) (by constructor <;> addr3) Ctx m0 hctx0
      have hV1 : ∀ x, x ∈ [G_ 21] → x < IN := fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; addr3
      have hF1 : FCtx k g U m1 :=
        FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) m0 m1 hF0 ag1
      have hL1 : ArrIs m1 (X_ 5) L := hL0.stable ag1 hV1 (by addr3) (by addr3) (by decide)
      have h21 : m1 (G_ 21) = L.length := by rw [h1a, hL0.len]
      have hM1 : m1 MDE = 1 := by rw [ag1.var MDE (lt_hp hhp0 (by decide)) (by decide) (by decide)]; exact hM0
      have hC1 : m1 CUR = y := by rw [ag1.var CUR (lt_hp hhp0 (by decide)) (by decide) (by decide)]; exact hC0
      have hP1 : ArrIs m1 PATH acc := hP0.stable ag1 hV1 (by addrf) (by addrf) (by decide)
      have hhp1 : 200 ≤ m1 HP := hF1.ctx.2.2
      -- `G_ 20 := first index of a residual predecessor`
      have hPreS : StableP (fun m => FCtx k g U m ∧ ArrIs m (X_ 5) L ∧ m (G_ 21) = L.length) (fiV 4 (G_ 20) descV) :=
        fun m m' hm hag => by
          have hhp : 200 ≤ m HP := hm.1.ctx.2.2
          refine ⟨FCtx.stableP (fiV_safe' 4 (G_ 20) (by norm_num) (safeVars_G 20 (by norm_num)) descV_safe)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m m' hm.1 hag,
            hm.2.1.stable hag hVfi (by addr3) (by addr3) (by decide), ?_⟩
          rw [hag.var (G_ 21) (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2.2
      obtain ⟨m2, k2, e2, hk2, ag2, h2r⟩ := firstIndexM_spec 4 (G_ 20) (G_ 21) (nodeBound n) (by norm_num)
        (descTest_spec k g U n hn hU L) (fun x hx => ⟨(descV_safe x hx).1, (descV_safe x hx).2.1⟩)
        (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by constructor <;> addr3)
        (by decide) (by decide) (by decide)
        (by decide)
        (fun m hm => hm.1.ctx) (fun m hm => by rw [hm.2.2]; exact hL) hPreS
        (fun m m' hm hag => by
          have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
          show decide ((g.networkL g.base.canonIds).ResL U (L.getD (m' (X_ 4)) 0) (m' CUR)) =
            decide ((g.networkL g.base.canonIds).ResL U (L.getD (m (X_ 4)) 0) (m CUR))
          rw [hag.var (X_ 4) (lt_hp hhp (by decide)) (by decide) (by decide),
            hag.var CUR (lt_hp hhp (by decide)) (by decide) (by decide)])
        m1 ⟨hF1, hL1, h21⟩
      have h2r' : m2 (G_ 20) = Instance.firstIndex (fun i =>
          decide ((g.networkL g.base.canonIds).ResL U (L.getD i 0) y)) L.length := by
        rw [h2r, h21]; congr 1; funext i
        show decide ((g.networkL g.base.canonIds).ResL U (L.getD ((m1.write (X_ 4) i) (X_ 4)) 0)
          ((m1.write (X_ 4) i) CUR)) = _
        rw [Mem.write_same, Mem.write_ne _ _ (by addrf), hC1]
      obtain ⟨hF2, hL2, h22⟩ := hPreS m1 m2 ⟨hF1, hL1, h21⟩ ag2
      have hM2 : m2 MDE = 1 := by rw [ag2.var MDE (lt_hp hhp1 (by decide)) (by decide) (by decide)]; exact hM1
      have hC2 : m2 CUR = y := by rw [ag2.var CUR (lt_hp hhp1 (by decide)) (by decide) (by decide)]; exact hC1
      have hP2 : ArrIs m2 PATH acc := hP1.stable ag2 hVfi (by addrf) (by addrf) (by decide)
      have hhp2 : 200 ≤ m2 HP := hF2.ctx.2.2
      have hfind := find?_eq_firstIndex (fun x => decide ((g.networkL g.base.canonIds).ResL U x y)) L
      simp only at hfind
      rw [← h2r'] at hfind
      by_cases hr : m2 (G_ 20) < L.length
      · have hc2 : (Cond.lt (G_ 20) (G_ 21)).eval m2 = true := by simp [Cond.eval, h22, hr]
        rw [if_pos hr] at hfind
        -- `CUR := layer[G_ 20]`
        obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b⟩ := elemM_spec (X_ 5) (G_ 20) CUR (by constructor <;> addrf)
          (by addrf) (by addrf) (fun m => Ctx m ∧ IN ≤ m (X_ 5)) (fun m hm => hm.1) (fun m hm => hm.2) m2
          ⟨hF2.ctx, hL2.1⟩
        have hVc' : ∀ x, x ∈ [CUR] → x < IN := fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; addrf
        have hF3 : FCtx k g U m3 :=
          FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) m2 m3 hF2 ag3
        have hC3 : m3 CUR = L.getD (m2 (G_ 20)) 0 := by
          have := arrAt_getElem m2 (m2 (X_ 5)) (m2 (G_ 20)) (by rw [hL2.2.2]; exact hr)
          rw [h3a, List.getD_eq_getElem _ _ hr, ← this]
          simp only [hL2.2.2]
        have hM3 : m3 MDE = 1 := by rw [ag3.var MDE (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact hM2
        have hP3 : ArrIs m3 PATH acc := hP2.stable ag3 hVc' (by addrf) (by addrf) (by decide)
        obtain ⟨m4, k4, e4, hk4, ag4, hP4⟩ := consPathM_spec CUR (2 * n + 3) (by constructor <;> addrf) (by decide)
          acc (L.getD (m2 (G_ 20)) 0) (fun m => Ctx m ∧ ArrIs m PATH acc ∧ m CUR = L.getD (m2 (G_ 20)) 0)
          (fun m hm => hm.1) (fun m hm => hm.2) hacc m3 ⟨hF3.ctx, hP3, hC3⟩
        have hhp3 : 200 ≤ m3 HP := hF3.ctx.2.2
        have hF4 : FCtx k g U m4 :=
          FCtx.stableP consPathV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) m3 m4 hF3 ag4
        refine ⟨m4, _, Cmd.Exec.ite_false hc0 (Cmd.Exec.ite_true hc1 (Cmd.Exec.seq e1 (Cmd.Exec.seq e2
          (Cmd.Exec.ite_true hc2 (Cmd.Exec.seq e3 e4))))), ?_,
          (ag1.trans (ag2.trans (ag3.trans (ag4.trans (Agree.refl m4 ([MDE])))))).mono
            (fun x hx => List.mem_append_right _ hx), hF4, ?_⟩
        · simp only [pathB]; omega
        · rw [show exStep (g.networkL g.base.canonIds) U (1, y, acc) L =
            (1, L.getD (m2 (G_ 20)) 0, L.getD (m2 (G_ 20)) 0 :: acc) by simp [exStep, hfind]]
          exact ⟨by rw [ag4.var MDE (lt_hp hhp3 (by decide)) (by decide) (by decide)]; exact hM3,
            by rw [ag4.var CUR (lt_hp hhp3 (by decide)) (by decide) (by decide)]; exact hC3, hP4⟩
      · have hc2 : (Cond.lt (G_ 20) (G_ 21)).eval m2 = false := by simp [Cond.eval, h22, hr]
        rw [if_neg hr] at hfind
        obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write MDE 2 := ⟨_, rfl⟩
        have e3 : Cmd.Exec (setc MDE 2) m2 m3 1 := by rw [hm3]; exact Exec.setc _ _ _
        have ag3 : Agree m2 m3 [MDE] := by rw [hm3]; exact Agree.write _ _ _ (by addrf)
        have hVm : ∀ x, x ∈ [MDE] → x < IN := fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; addrf
        have hF3 : FCtx k g U m3 :=
          FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) m2 m3 hF2 ag3
        refine ⟨m3, _, Cmd.Exec.ite_false hc0 (Cmd.Exec.ite_true hc1 (Cmd.Exec.seq e1 (Cmd.Exec.seq e2
          (Cmd.Exec.ite_false hc2 e3)))), ?_,
          (ag1.trans (ag2.trans ag3)).mono (fun x hx => List.mem_append_right _ (?_ : x ∈ pathV1)), hF3, ?_⟩
        · simp only [pathB]; omega
        · rcases List.mem_append.1 hx with h | h
          · exact List.mem_append_left _ h
          · rcases List.mem_append.1 h with h | h
            · exact List.mem_append_right _ (List.mem_append_left _ h)
            · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
                (List.mem_append_right _ h)))
        · rw [show exStep (g.networkL g.base.canonIds) U (1, y, acc) L = (2, y, acc) by simp [exStep, hfind]]
          exact ⟨by rw [hm3, Mem.write_same], by rw [hm3, Mem.write_ne _ _ (by addrf)]; exact hC2,
            hP2.stable ag3 hVm (by addrf) (by addrf) (by decide)⟩
    · have hc1 : (Cond.eq MDE ONE).eval m0 = false := by simp [Cond.eval, hM0, hone0, h1]
      refine ⟨m0, _, Cmd.Exec.ite_false hc0 (Cmd.Exec.ite_false hc1 (Exec.nop m0)), ?_, Agree.refl m0 pathV,
        hF0, ?_⟩
      · simp only [pathB]; omega
      · rw [show exStep (g.networkL g.base.canonIds) U (mode, y, acc) L = (mode, y, acc) by simp [exStep, h0, h1]]
        exact ⟨hM0, hC0, hP0⟩


theorem Agree.write_mem {m0 m : Mem} {V : List ℕ} (hag : Agree m0 m V) (x v : ℕ) (hx : x ∈ V) (hxH : x ≠ HP) :
    Agree m0 (m.write x v) V :=
  (hag.trans (Agree.write m x v hxH)).mono (fun y hy => by
    rcases List.mem_append.1 hy with h | h
    · exact h
    · simp only [List.mem_singleton] at h; subst h; exact hx)

theorem layers_length (g : GInstance) (U : List (ℕ × ℕ)) :
    ((g.networkL g.base.canonIds).layers U).length = (g.networkL g.base.canonIds).nodes.length + 1 := by
  rw [layers_eq, List.length_map, List.length_range]

theorem layers_getD_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) (U : List (ℕ × ℕ)) (i : ℕ) :
    (((g.networkL g.base.canonIds).layers U).getD i []).length ≤ nodeBound n := by
  have hNL := netNodes_length_le hn
  have hNL1 := netNodes_length_pos g
  rw [layers_eq]
  by_cases hi : i < (List.range ((g.networkL g.base.canonIds).nodes.length + 1)).length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact le_trans (layerState_front_le _ _ hNL1 _) hNL
  · rw [List.getD_eq_default _ _ (by simpa using hi)]; simp [nodeBound]

/-- The augmenting path: `MDE := 0`, `CUR := t`, `PATH := []`, then one pass over the layers
in reverse. -/
def augPathM : Cmd :=
  .seq (setc MDE 0) (.seq (mov CUR NETT) (.seq (emptyArrM PATH) (forEachRevM 5 LAYS pathBody)))

def augPathV : List ℕ := [MDE] ++ ([CUR] ++ ([PATH] ++ (Lvars 5 ++ pathV)))

theorem augPathV_safe : SafeVars augPathV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_Lvars 5 (by norm_num)) pathV_safe)))

def augPathB (n : ℕ) : ℕ := 1 + 1 + 3 + ((2 * n + 3) * (pathB n + 6) + 4)

/-- The invariant of the path loop after `j` reversed layers (relative to the state `m3`
before the loop). -/
def PathInv (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (m3 : Mem) (len : ℕ) (j : ℕ) (m : Mem) : Prop :=
  Agree m3 m (Lvars 5 ++ pathV) ∧ FCtx k g U m ∧
    XState (List.foldl (exStep (g.networkL g.base.canonIds) U) (0, (g.networkL g.base.canonIds).t, [])
      (((g.networkL g.base.canonIds).layers U).reverse.take j)) m ∧
    m (I_ 5) = j ∧ m (CNT_ 5) = len

theorem augPathM_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hn : Sized n g)
    (hU : U.length ≤ flowBound n) :
    RSpec augPathM augPathV (augPathB n) (fun m => FCtx k g U m ∧ LaysAt m ((g.networkL g.base.canonIds).layers U))
      (fun _ m' => FCtx k g U m' ∧ ArrIs m' PATH ((g.networkL g.base.canonIds).augPath U)) := by
  intro m0 hm0
  obtain ⟨hF0, ptrs, hlays0, hptrs0⟩ := hm0
  have hctx0 := hF0.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hNL := netNodes_length_le hn
  have hnett0 : m0 NETT = g.netT := hF0.1.1.2.2.1
  have hlen : ptrs.length = ((g.networkL g.base.canonIds).layers U).length := hptrs0.1
  have hlen' : ptrs.length ≤ 2 * n + 3 := by rw [hlen, layers_length]; omega
  have hVL5 : ∀ x, x ∈ Lvars 5 ++ pathV → x < IN := fun x hx =>
    (SafeVars.append (safeVars_Lvars 5 (by norm_num)) pathV_safe x hx).2.1
  have hVp : ∀ x, x ∈ pathV → x < IN := fun x hx => (pathV_safe x hx).2.1
  -- `MDE := 0`
  obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b⟩ := setcM_spec MDE 0 (by constructor <;> addrf) Ctx m0 hctx0
  have hVm : ∀ x, x ∈ [MDE] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hF1 : FCtx k g U m1 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m0 m1 hF0 ag1
  have hlays1 := hlays0.stable ag1 hVm (by addrf) (by addrf) (by decide)
  have hptrs1 := hptrs0.stable ag1 hVm
  have hnett1 : m1 NETT = g.netT := by rw [ag1.var NETT (lt_hp hhp0 (by decide)) (by decide) (by decide)]; exact hnett0
  -- `CUR := t`
  obtain ⟨m2, k2, e2, hk2, ag2, h2a, h2b⟩ := movM_spec NETT CUR (by constructor <;> addrf) Ctx m1 hF1.ctx
  have hVc : ∀ x, x ∈ [CUR] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hhp1 : 200 ≤ m1 HP := hF1.ctx.2.2
  have hF2 : FCtx k g U m2 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m1 m2 hF1 ag2
  have hlays2 := hlays1.stable ag2 hVc (by addrf) (by addrf) (by decide)
  have hptrs2 := hptrs1.stable ag2 hVc
  have hM2 : m2 MDE = 0 := by rw [ag2.var MDE (lt_hp hhp1 (by decide)) (by decide) (by decide)]; exact h1a
  have hC2 : m2 CUR = g.netT := by rw [h2a, hnett1]
  -- `PATH := []`
  obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b, h3c⟩ :=
    emptyArrM_spec PATH (by constructor <;> addrf) Ctx (fun m hm => hm) m2 hF2.ctx
  have hVp3 : ∀ x, x ∈ [PATH] → x < IN := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; addrf
  have hhp2 : 200 ≤ m2 HP := hF2.ctx.2.2
  have hF3 : FCtx k g U m3 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m2 m3 hF2 ag3
  have hlays3 := hlays2.stable ag3 hVp3 (by addrf) (by addrf) (by decide)
  have hptrs3 := hptrs2.stable ag3 hVp3
  have hM3 : m3 MDE = 0 := by rw [ag3.var MDE (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact hM2
  have hC3 : m3 CUR = g.netT := by rw [ag3.var CUR (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact hC2
  have hP3 : ArrIs m3 PATH [] := ArrIs.of_out hF2.ctx.2.2 h3a (arrAt_nil h3b) (by rw [List.length_nil]; omega)
  have hhp3 : 200 ≤ m3 HP := hF3.ctx.2.2
  -- the loop
  have hI : ∀ j m, PathInv k g U m3 ptrs.length j m → m (I_ 5) = j ∧ m (CNT_ 5) = ptrs.length ∧ m LAYS = m3 LAYS ∧
      m ONE = 1 ∧ m3 LAYS + 1 + ptrs.length ≤ m HP ∧ (∀ i, (h : i < ptrs.length) → m (m3 LAYS + 1 + i) = ptrs[i]) := by
    intro j m hm
    obtain ⟨hag, hF, _, hi, hc⟩ := hm
    have hroom := hlays3.2.1
    rw [hlays3.len] at hroom
    refine ⟨hi, hc, hag.var LAYS (lt_hp hhp3 (by decide)) (by decide) (by decide), hF.ctx.1, le_trans hroom hag.2,
      fun i hi' => ?_⟩
    rw [hag.heap hVL5 _ (by have := hlays3.1; omega) (by omega), ← arrAt_getElem m3 (m3 LAYS) i (by rw [hlays3.2.2]; exact hi')]
    simp only [hlays3.2.2]
  have hstable : ∀ j m v w, PathInv k g U m3 ptrs.length j m →
      PathInv k g U m3 ptrs.length j ((m.write (PTR_ 5) v).write (X_ 5) w) := by
    intro j m v w hm
    obtain ⟨hag, hF, hX, hi, hc⟩ := hm
    have hhp : 200 ≤ m HP := hF.ctx.2.2
    have agw : Agree m ((m.write (PTR_ 5) v).write (X_ 5) w) ([PTR_ 5] ++ [X_ 5]) :=
      (Agree.write m (PTR_ 5) v (by addr3)).trans (Agree.write _ (X_ 5) w (by addr3))
    have hVw : ∀ x, x ∈ [PTR_ 5] ++ [X_ 5] → x < IN := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with h | h <;> subst h <;> addr3
    refine ⟨(hag.write_mem (PTR_ 5) v (by decide) (by addr3)).write_mem (X_ 5) w (by decide) (by addr3),
      FCtx.stableP (SafeVars.append (safeVars_of_decide _ (by decide)) (safeVars_of_decide _ (by decide)))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m _ hF agw,
      hX.stable agw hVw (by decide) (by decide) (by decide) hhp, ?_, ?_⟩
    · rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]; exact hi
    · rw [Mem.write_ne _ _ (by addr3), Mem.write_ne _ _ (by addr3)]; exact hc
  have hbody : ∀ j m, (h : j < ptrs.length) → PathInv k g U m3 ptrs.length j m →
      m (X_ 5) = ptrs[ptrs.length - 1 - j] → m (PTR_ 5) = m3 LAYS + ptrs.length - j →
      ∃ m' kk, Cmd.Exec pathBody m m' kk ∧ kk ≤ pathB n ∧ m' (I_ 5) = j ∧ m' ONE = 1 ∧
        PathInv k g U m3 ptrs.length (j + 1) (m'.write (I_ 5) (j + 1)) := by
    intro j m hj hm hx _
    obtain ⟨hag, hF, hX, hi, hc⟩ := hm
    have hhp : 200 ≤ m HP := hF.ctx.2.2
    have hptrs := hptrs3.stable hag hVL5
    obtain ⟨c1, c2, c3⟩ := hptrs.2 (ptrs.length - 1 - j) (by omega)
    have hArr : ArrIs m (X_ 5) (((g.networkL g.base.canonIds).layers U).getD (ptrs.length - 1 - j) []) := by
      rw [ArrIs, hx]; exact ⟨c1, c2, c3⟩
    have hjr : j < ((g.networkL g.base.canonIds).layers U).reverse.length := by rw [List.length_reverse]; omega
    have hL : ((g.networkL g.base.canonIds).layers U).reverse[j] =
        ((g.networkL g.base.canonIds).layers U).getD (ptrs.length - 1 - j) [] := by
      rw [List.getElem_reverse, List.getD_eq_getElem _ _ (by omega)]
      congr 2; omega
    obtain ⟨m', kk, e, hk, agB, hF', hX'⟩ := pathBody_spec k g U n hn hU _ _ (layers_getD_length_le hn U _)
      (by
        have := foldl_exStep_length (g.networkL g.base.canonIds) U
          (((g.networkL g.base.canonIds).layers U).reverse.take j) (0, (g.networkL g.base.canonIds).t, [])
        simp only [List.length_nil, List.length_take, List.length_reverse] at this
        omega) m ⟨hF, hX, hArr⟩
    have agW : Agree m' (m'.write (I_ 5) (j + 1)) [I_ 5] := Agree.write _ _ _ (by addr3)
    have hhp' : 200 ≤ m' HP := hF'.ctx.2.2
    refine ⟨m', kk, e, hk, by rw [agB.var (I_ 5) (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hi,
      hF'.ctx.1, ?_, ?_, ?_, by rw [Mem.write_same], ?_⟩
    · refine ((hag.trans agB).mono (fun x hx => ?_)).write_mem (I_ 5) (j + 1) (by decide) (by addr3)
      rcases List.mem_append.1 hx with h | h
      · exact h
      · exact List.mem_append_right _ h
    · exact FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) m' _ hF' agW
    · rw [← List.take_append_getElem hjr, List.foldl_append, List.foldl_cons, List.foldl_nil, hL]
      exact hX'.stable agW (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; addr3) (by decide)
        (by decide) (by decide) hhp'
    · rw [Mem.write_ne _ _ (by addr3), agB.var (CNT_ 5) (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hc
  have hinv0 : PathInv k g U m3 ptrs.length 0 ((m3.write (CNT_ 5) ptrs.length).write (I_ 5) 0) := by
    have agw : Agree m3 ((m3.write (CNT_ 5) ptrs.length).write (I_ 5) 0) ([CNT_ 5] ++ [I_ 5]) :=
      (Agree.write m3 (CNT_ 5) _ (by addr3)).trans (Agree.write _ (I_ 5) 0 (by addr3))
    have hVw : ∀ x, x ∈ [CNT_ 5] ++ [I_ 5] → x < IN := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with h | h <;> subst h <;> addr3
    refine ⟨((Agree.refl m3 _).write_mem (CNT_ 5) _ (by decide) (by addr3)).write_mem (I_ 5) 0 (by decide) (by addr3),
      FCtx.stableP (SafeVars.append (safeVars_of_decide _ (by decide)) (safeVars_of_decide _ (by decide)))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m3 _ hF3 agw,
      ?_, by rw [Mem.write_same], by rw [Mem.write_ne _ _ (by addr3), Mem.write_same]⟩
    simp only [List.take_zero, List.foldl_nil]
    refine ⟨?_, ?_, hP3.stable agw hVw (by addrf) (by addrf) (by decide)⟩
    · rw [Mem.write_ne _ _ (by addrf), Mem.write_ne _ _ (by addrf)]; exact hM3
    · rw [Mem.write_ne _ _ (by addrf), Mem.write_ne _ _ (by addrf)]; exact hC3
  obtain ⟨m', kk, e, inv', hk⟩ := forEachRevM_spec 5 LAYS (by norm_num) (by addrf) (by decide) pathBody
    (PathInv k g U m3 ptrs.length) (m3 LAYS) hlays3.1 ptrs (pathB n) hI hstable hbody m3 rfl hlays3.len hinv0
  obtain ⟨ag', hF', hX', _, _⟩ := inv'
  refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 e)), ?_,
    ag1.trans (ag2.trans (ag3.trans ag')), hF', ?_⟩
  · have : ptrs.length * (pathB n + 6) ≤ (2 * n + 3) * (pathB n + 6) := Nat.mul_le_mul_right _ hlen'
    simp only [augPathB]; omega
  · rw [augPath_eq]
    have htake : ((g.networkL g.base.canonIds).layers U).reverse.take ptrs.length =
        ((g.networkL g.base.canonIds).layers U).reverse := by
      rw [hlen, ← List.length_reverse, List.take_length]
    rw [htake] at hX'
    exact hX'.2.2




/-- Filtering a pair array by a test on the record at `X_ L`. -/
theorem filterM_parr_spec {t : Cmd} {V : List ℕ} {B : ℕ} {Pre : Mem → Prop} {P : Mem → Bool} (L SRC Q n : ℕ)
    (l : List (ℕ × ℕ)) (G : ℕ × ℕ → Bool)
    (ht : TestSpec t V B (fun m => Pre m ∧ m (X_ L) ∈ arrAt m (m SRC)) P) (hL : L ≤ 9)
    (hV : ∀ x, x ∈ V → 5 ≤ x ∧ x < IN) (hSRC : 5 ≤ SRC ∧ SRC < IN) (hSV : SRC ∉ V)
    (hSL : SRC ∉ Lvars L) (hSF : SRC ≠ FLAG) (hVL : ∀ x, x ∈ V → x ∉ LvarsX L) (hXV : X_ L ∉ V)
    (hQ : 5 ≤ Q ∧ Q < IN)
    (hctx : ∀ m, Pre m → Ctx m) (harr : ∀ m, Pre m → PArrIs m SRC l) (hn : l.length ≤ n)
    (hPre : StableP Pre (Lvars L ++ FLAG :: V)) (hP : StableX Pre SRC L P (LvarsX L ++ FLAG :: V))
    (hG : ∀ m x, Pre m → x ∈ arrAt m (m SRC) → P (m.write (X_ L) x) = G (m x, m (x + 1))) :
    RSpec (.seq (filterM L SRC t) (mov Q (OUT_ L))) (Lvars L ++ FLAG :: V ++ [Q]) (n * (B + 14) + 9 + 1) Pre
      (fun _ m' => PArrIs m' Q (l.filter G)) := by
  have hf := filterM_spec L SRC n ht hL hV hSRC hSV hSL hSF hVL hXV hctx
    (fun m hm => ⟨(harr m hm).1.1, (harr m hm).1.2.1, by rw [(harr m hm).len]; exact hn⟩) hPre hP
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hO, harr', hroom⟩ := hf m hm
  have hhp := (hctx m hm).2.2
  have hl := harr m hm
  have hLv := Lvars_range L hL
  have hVlt : ∀ x, x ∈ Lvars L ++ FLAG :: V → x < IN := by
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with h | h | h
    · exact (hLv x h).2
    · subst h; addr3
    · exact (hV x h).2
  have hptrs : arrAt m₁ (m HP) = (arrAt m (m SRC)).filter (fun x => G (m x, m (x + 1))) := by
    rw [harr']; apply List.filter_congr; intro x hx; exact hG m x hm hx
  have hlen : ((arrAt m (m SRC)).filter (fun x => G (m x, m (x + 1)))).length ≤ m (m SRC) := by
    have := List.length_filter_le (fun x => G (m x, m (x + 1))) (arrAt m (m SRC))
    rw [arrAt_length] at this; exact this
  have hrec := hl.1.2.2
  have hcell : ∀ q, q ∈ arrAt m (m SRC) → m₁ q = m q ∧ m₁ (q + 1) = m (q + 1) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hrec q hq
    exact ⟨ag₁.heap hVlt q h1 (by omega), ag₁.heap hVlt (q + 1) (by omega) (by omega)⟩
  refine ⟨m₁.write Q (m₁ (OUT_ L)), _, Cmd.Exec.seq e₁ (Exec.mov _ _ _), by omega,
    ag₁.trans (Agree.write m₁ Q _ (by addr3)), ?_⟩
  have hQ' : (m₁.write Q (m₁ (OUT_ L))) Q = m HP := by rw [Mem.write_same, hO]
  have hHP' : (m₁.write Q (m₁ (OUT_ L))) HP = m₁ HP := Mem.write_ne _ _ (by addr3)
  have harr'' : arrAt (m₁.write Q (m₁ (OUT_ L))) (m HP) = arrAt m₁ (m HP) := arrAt_write_lo _ _ _ _ hQ.2 hhp
  have hhdr : (m₁.write Q (m₁ (OUT_ L))) (m HP) = m₁ (m HP) := Mem.write_ne _ _ (by omega)
  have hlen1 : m₁ (m HP) = ((arrAt m (m SRC)).filter (fun x => G (m x, m (x + 1)))).length := by
    rw [← hptrs, arrAt_length]
  refine ⟨⟨by rw [hQ']; exact hhp, ?_, ?_⟩, ?_⟩
  · rw [hQ', hHP', hhdr, hlen1]; omega
  · intro q hq
    rw [hQ', harr'', hptrs, List.mem_filter] at hq
    obtain ⟨h1, h2⟩ := hrec q hq.1
    rw [hHP']
    exact ⟨h1, le_trans h2 ag₁.2⟩
  · rw [hQ', pairsAt, harr'', hptrs]
    rw [← hl.2, pairsAt, List.filter_map]
    apply List.map_congr_left
    intro q hq
    rw [List.mem_filter] at hq
    obtain ⟨h1, h2⟩ := hrec q hq.1
    obtain ⟨c1, c2⟩ := hcell q hq.1
    rw [Mem.write_ne _ _ (by omega), Mem.write_ne _ _ (by omega), c1, c2]


/-! ### The steps of the path -/

theorem steps_eq_range (p : List ℕ) :
    Network.steps p = (List.range (p.length - 1)).map (fun i => (p.getD i 0, p.getD (i + 1) 0)) := by
  apply List.ext_getElem
  · simp only [Network.steps, List.length_zip, List.length_tail, List.length_map, List.length_range]
    omega
  · intro i h1 h2
    simp only [Network.steps, List.length_zip, List.length_tail] at h1
    simp only [Network.steps, List.getElem_zip, List.getElem_tail, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

/-- `(VAL, V2) := (PATH.getD i 0, PATH.getD (i + 1) 0)` for the index `i = X_ 6`. -/
def stepPairM : Cmd := .seq (getDM PATH (X_ 6) VAL) (.seq (add (G_ 24) (X_ 6) ONE) (getDM PATH (G_ 24) V2))

theorem stepPairM_spec (Pre : Mem → Prop) (hctx : ∀ m, Pre m → Ctx m ∧ IN ≤ m PATH ∧ m PATH + 1 + m (m PATH) ≤ m HP) :
    FunSpec2 stepPairM [VAL, G_ 24, V2] 13 Pre
      (fun m => ((arrAt m (m PATH)).getD (m (X_ 6)) 0, (arrAt m (m PATH)).getD (m (X_ 6) + 1) 0)) := by
  intro m hm
  obtain ⟨hctx0, hpath, hroom⟩ := hctx m hm
  have hhp : 200 ≤ m HP := hctx0.2.2
  obtain ⟨m1, k1, e1, hk1, ag1, hv1, hHP1⟩ := getDM_spec PATH (X_ 6) VAL (by constructor <;> addr3) (by addrf)
    (by addr3) (fun m => Ctx m ∧ IN ≤ m PATH) (fun m hm => hm.1) (fun m hm => hm.2) m ⟨hctx0, hpath⟩
  have hV1 : ∀ x, x ∈ [VAL] → x < IN := fun x hx => by simp at hx; subst hx; addr3
  have hone1 : m1 ONE = 1 := by rw [ag1.var ONE (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hctx0.1
  have hx1 : m1 (X_ 6) = m (X_ 6) := ag1.var (X_ 6) (lt_hp hhp (by decide)) (by decide) (by decide)
  have hpath1 : m1 PATH = m PATH := ag1.var PATH (lt_hp hhp (by decide)) (by decide) (by decide)
  have harr1 : arrAt m1 (m PATH) = arrAt m (m PATH) := ag1.arrAt hV1 _ hpath hroom
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (G_ 24) (m (X_ 6) + 1) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (add (G_ 24) (X_ 6) ONE) m1 m2 1 := by
    have := Exec.add (G_ 24) (X_ 6) ONE m1; rwa [hx1, hone1, ← hm2] at this
  have ag2 : Agree m1 m2 [G_ 24] := by rw [hm2]; exact Agree.write m1 (G_ 24) _ (by addr3)
  have hctx2 : Ctx m2 := Ctx.of_agree (Ctx.of_agree hctx0 ag1 (fun x hx => by simp at hx; subst hx; addr3)) ag2
    (fun x hx => by simp at hx; subst hx; addr3)
  have hpath2 : m2 PATH = m PATH := by rw [hm2, Mem.write_ne _ _ (by addrf), hpath1]
  have harr2 : arrAt m2 (m PATH) = arrAt m (m PATH) := by
    rw [hm2, arrAt_write_lo _ _ _ _ (by addr3) hpath, harr1]
  have h24 : m2 (G_ 24) = m (X_ 6) + 1 := by rw [hm2, Mem.write_same]
  obtain ⟨m3, k3, e3, hk3, ag3, hv3, hHP3⟩ := getDM_spec PATH (G_ 24) V2 (by constructor <;> addr3) (by addrf)
    (by addr3) (fun m => Ctx m ∧ IN ≤ m PATH) (fun m hm => hm.1) (fun m hm => hm.2) m2
    ⟨hctx2, by rw [hpath2]; exact hpath⟩
  have hhp2 : 200 ≤ m2 HP := hctx2.2.2
  refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), by omega, ?_, ?_⟩
  · exact (ag1.trans (ag2.trans ag3)).mono (fun x hx => by simp at hx ⊢; tauto)
  · show (m3 VAL, m3 V2) = _
    rw [hv3, hpath2, harr2, h24, ag3.var VAL (lt_hp hhp2 (by decide)) (by decide) (by decide), hm2,
      Mem.write_ne _ _ (by addr3), hv1]


/-- `STEPS := steps PATH`. -/
def stepsM : Cmd :=
  .seq (load (G_ 25) PATH) (.seq (sub (G_ 25) (G_ 25) ONE) (.seq (.seq (rangeM 6 (G_ 25)) (mov (G_ 26) (OUT_ 6)))
    (.seq (mapPairM 6 (G_ 26) stepPairM) (mov STEPS (OUT_ 6)))))

def stepsV : List ℕ := [G_ 25] ++ ([G_ 25] ++ ((Lvars 6 ++ [G_ 26]) ++ (Lvars 6 ++ [VAL, G_ 24, V2] ++ [STEPS])))

theorem stepsV_safe : SafeVars stepsV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (SafeVars.append (safeVars_Lvars 6 (by norm_num)) (safeVars_of_decide _ (by decide)))
      (SafeVars.append (SafeVars.append (safeVars_Lvars 6 (by norm_num)) (safeVars_of_decide _ (by decide)))
        (safeVars_of_decide _ (by decide)))))

def stepsB (n : ℕ) : ℕ := 1 + 1 + ((2 * n + 3) * 6 + 8 + 1) + ((2 * n + 3) * (13 + 14) + 9 + 1)

theorem stepsM_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (p : List ℕ) (hp : p.length ≤ 2 * n + 3) :
    RSpec stepsM stepsV (stepsB n) (fun m => FCtx k g U m ∧ ArrIs m PATH p)
      (fun _ m' => FCtx k g U m' ∧ PArrIs m' STEPS (Network.steps p)) := by
  intro m0 hm0
  obtain ⟨hF0, hP0⟩ := hm0
  have hctx0 := hF0.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hV25 : ∀ x, x ∈ [G_ 25] → x < IN := fun x hx => by simp at hx; subst hx; addr3
  -- `G_ 25 := |PATH| - 1`
  obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b⟩ := loadM_spec PATH (G_ 25) (by constructor <;> addr3) Ctx m0 hctx0
  have hF1 : FCtx k g U m1 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m0 m1 hF0 ag1
  have hP1 : ArrIs m1 PATH p := hP0.stable ag1 hV25 (by addrf) (by addrf) (by decide)
  have h25 : m1 (G_ 25) = p.length := by rw [h1a, hP0.len]
  have hone1 : m1 ONE = 1 := hF1.ctx.1
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (G_ 25) (p.length - 1) := ⟨_, rfl⟩
  have e2 : Cmd.Exec (sub (G_ 25) (G_ 25) ONE) m1 m2 1 := by
    have := Exec.sub (G_ 25) (G_ 25) ONE m1; rwa [h25, hone1, ← hm2] at this
  have ag2 : Agree m1 m2 [G_ 25] := by rw [hm2]; exact Agree.write m1 (G_ 25) _ (by addr3)
  have hF2 : FCtx k g U m2 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m1 m2 hF1 ag2
  have hP2 : ArrIs m2 PATH p := hP1.stable ag2 hV25 (by addrf) (by addrf) (by decide)
  have h25' : m2 (G_ 25) = p.length - 1 := by rw [hm2, Mem.write_same]
  have hctx2 := hF2.ctx
  have hhp2 : 200 ≤ m2 HP := hctx2.2.2
  -- `G_ 26 := range (|PATH| - 1)`
  obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b, h3c⟩ := rangeM_spec 6 (G_ 25) (2 * n + 3) (by norm_num)
    (by constructor <;> addr3) (by decide) (fun m => Ctx m ∧ m (G_ 25) = p.length - 1) (fun m hm => hm.1)
    (fun m hm => by rw [hm.2]; omega) m2 ⟨hctx2, h25'⟩
  have hs6 : SafeVars (Lvars 6) := safeVars_Lvars 6 (by norm_num)
  have hV6 : ∀ x, x ∈ Lvars 6 → x < IN := fun x hx => (hs6 x hx).2.1
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (G_ 26) (m3 (OUT_ 6)) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (mov (G_ 26) (OUT_ 6)) m3 m4 1 := by rw [hm4]; exact Exec.mov _ _ _
  have ag4 : Agree m3 m4 [G_ 26] := by rw [hm4]; exact Agree.write m3 (G_ 26) _ (by addr3)
  have ag34 : Agree m2 m4 (Lvars 6 ++ [G_ 26]) := ag3.trans ag4
  have hV6' : ∀ x, x ∈ Lvars 6 ++ [G_ 26] → x < IN := fun x hx =>
    (SafeVars.append hs6 (safeVars_of_decide _ (by decide)) x hx).2.1
  have hF4 : FCtx k g U m4 :=
    FCtx.stableP (SafeVars.append hs6 (safeVars_of_decide _ (by decide))) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) m2 m4 hF2 ag34
  have hP4 : ArrIs m4 PATH p := hP2.stable ag34 hV6' (by addrf) (by addrf) (by decide)
  have hR4 : ArrIs m4 (G_ 26) (List.range (p.length - 1)) := by
    refine ArrIs.of_out hctx2.2.2 (by rw [hm4, Mem.write_same, h3a]) ?_ ?_
    · rw [hm4, arrAt_write_lo _ _ _ _ (by addr3) hctx2.2.2, h3b, h25']
    · rw [hm4, Mem.write_ne _ _ (by addr3), List.length_range, ← h25']; exact h3c
  -- `STEPS := map stepPair (G_ 26)`
  let Pre : Mem → Prop := fun m => FCtx k g U m ∧ ArrIs m PATH p ∧ ArrIs m (G_ 26) (List.range (p.length - 1))
  have hs' : SafeVars (Lvars 6 ++ [VAL, G_ 24, V2]) := SafeVars.append hs6 (safeVars_of_decide _ (by decide))
  have hsX : SafeVars (LvarsX 6 ++ [VAL, G_ 24, V2]) :=
    SafeVars.append (safeVars_LvarsX 6 (by norm_num)) (safeVars_of_decide _ (by decide))
  obtain ⟨m5, k5, e5, hk5, ag5, hS5⟩ := mapPairM_parr_spec 6 (G_ 26) STEPS (2 * n + 3) (List.range (p.length - 1))
    (fun i => (p.getD i 0, p.getD (i + 1) 0))
    (stepPairM_spec (fun m => Pre m ∧ m (X_ 6) ∈ arrAt m (m (G_ 26)))
      (fun m hm => ⟨hm.1.1.ctx, hm.1.2.1.1, hm.1.2.1.2.1⟩))
    (by norm_num) (fun x hx => ⟨(safeVars_of_decide _ (by decide) x hx).1, (safeVars_of_decide _ (by decide) x hx).2.1⟩)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by constructor <;> addrf)
    (fun m hm => hm.1.ctx) (fun m hm => hm.2.2) (by rw [List.length_range]; omega)
    ((FCtx.stableP hs' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).and
      ((ArrIs.stableP (P := PATH) (fun x hx => (hs' x hx).2.1) (by addrf) (by addrf) (by decide)).and
        (ArrIs.stableP (P := G_ 26) (fun x hx => (hs' x hx).2.1) (by addr3) (by addr3) (by decide))))
    (fun m m' hm _ hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show ((arrAt m' (m' PATH)).getD (m' (X_ 6)) 0, (arrAt m' (m' PATH)).getD (m' (X_ 6) + 1) 0) =
        ((arrAt m (m PATH)).getD (m (X_ 6)) 0, (arrAt m (m PATH)).getD (m (X_ 6) + 1) 0)
      rw [hag.var (X_ 6) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var PATH (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.arrAt (fun x hx => (hsX x hx).2.1) _ hm.2.1.1 hm.2.1.2.1])
    (fun m x hm _ => by
      show ((arrAt (m.write (X_ 6) x) ((m.write (X_ 6) x) PATH)).getD ((m.write (X_ 6) x) (X_ 6)) 0,
        (arrAt (m.write (X_ 6) x) ((m.write (X_ 6) x) PATH)).getD ((m.write (X_ 6) x) (X_ 6) + 1) 0) = _
      rw [Mem.write_same, Mem.write_ne _ _ (by addrf), arrAt_write_lo _ _ _ _ (by addr3) hm.2.1.1, hm.2.1.2.2])
    m4 ⟨hF4, hP4, hR4⟩
  have hF5 : FCtx k g U m5 :=
    FCtx.stableP (SafeVars.append hs' (safeVars_of_decide _ (by decide))) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) m4 m5 hF4 ag5
  refine ⟨m5, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq (Cmd.Exec.seq e3 e4) e5)), ?_,
    ag1.trans (ag2.trans (ag34.trans ag5)), hF5, ?_⟩
  · simp only [stepsB]; omega
  · rw [steps_eq_range]; exact hS5


/-! ### The reachability test -/

theorem seen_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) (U : List (ℕ × ℕ)) :
    ((g.networkL g.base.canonIds).seen U).length ≤ seenBound n := by
  have hNL := netNodes_length_le hn
  have hNL1 := netNodes_length_pos g
  rw [Network.seen, layers_eq, ← layerState_seen_eq]
  have := layerState_seen_le (g.networkL g.base.canonIds) U hNL1 ((g.networkL g.base.canonIds).nodes.length + 1)
  have h2 : ((g.networkL g.base.canonIds).nodes.length + 1) * (g.networkL g.base.canonIds).nodes.length ≤
      (2 * n + 3) * (2 * n + 2) := Nat.mul_le_mul (by omega) hNL
  unfold seenBound
  rw [Nat.mul_comm]; omega

/-- `FLAG := (t ∈ SEEN)`. -/
def seenTest : Cmd := memValM 3 SEEN NETT

def seenV : List ℕ := Lvars 3 ++ FLAG :: [FLAG]

theorem seenV_safe : SafeVars seenV :=
  SafeVars.append (safeVars_Lvars 3 (by norm_num)) (safeVars_of_decide _ (by decide))

theorem seenTest_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hn : Sized n g) :
    TestSpec seenTest seenV (seenBound n * (3 + 11) + 10)
      (fun m => FCtx k g U m ∧ ArrIs m SEEN ((g.networkL g.base.canonIds).seen U))
      (fun _ => decide ((g.networkL g.base.canonIds).t ∈ (g.networkL g.base.canonIds).seen U)) := by
  have h := memValM_spec 3 SEEN NETT (seenBound n) (by norm_num) (by constructor <;> addrf)
    (by constructor <;> addrn) (by decide) (by decide) (by decide) (by decide)
    (fun m => FCtx k g U m ∧ ArrIs m SEEN ((g.networkL g.base.canonIds).seen U)) (fun m hm => hm.1.ctx)
    (fun m hm => ⟨hm.2.1, hm.2.2.1, by rw [hm.2.len]; exact seen_length_le hn U⟩)
    ((FCtx.stableP seenV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).and
      (ArrIs.stableP (P := SEEN) (fun x hx => (seenV_safe x hx).2.1) (by addrf) (by addrf) (by decide)))
  refine h.congr (fun m hm => ?_)
  have ht : m NETT = g.netT := hm.1.1.1.2.2.1
  show decide (m NETT ∈ arrAt m (m SEEN)) = _
  rw [ht, hm.2.2.2]
  rfl

/-! ### Augmentation -/

theorem pairsAt_write_lo (m : Mem) (a x v hi : ℕ) (hx : x < IN) (ha : IN ≤ a) (hrec : RecsIn m a IN hi) :
    pairsAt (m.write x v) a = pairsAt m a :=
  pairsAt_congr (arrAt_write_lo _ _ _ _ hx ha) (fun q hq => by
    have := hrec q hq
    exact ⟨Mem.write_ne _ _ (by omega), Mem.write_ne _ _ (by omega)⟩)

theorem PArrIs.mov {m m' : Mem} {V : List ℕ} {P Q : ℕ} {l : List (ℕ × ℕ)} (hag : Agree m m' V)
    (hV : ∀ x, x ∈ V → x < IN) (hP : m' P = m Q) (h : PArrIs m Q l) : PArrIs m' P l := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  refine ⟨⟨by rw [hP]; exact h1, ?_, ?_⟩, by rw [hP, hag.pairsAt hV _ h1 h2 h3]; exact h4⟩
  · rw [hP, hag.heap hV _ h1 (by omega)]; exact le_trans h2 hag.2
  · rw [hP]; exact (RecsIn.of_agree hag hV h1 h2 h3).mono le_rfl hag.2

/-- `FLAG := ((a.2, a.1) ∉ STEPS)` for the record `a` at `X_ 6`. -/
def keepTest : Cmd :=
  .seq (.seq (load (G_ 29) (X_ 6)) (.seq (field1M (X_ 6) (G_ 30)) (mkPairM (G_ 30) (G_ 29) (G_ 31))))
    (notM (memPairM 7 STEPS (G_ 31)))

def keepV : List ℕ := [G_ 29] ++ ([G_ 30] ++ ([G_ 31] ++ FLAG :: memPairV 7))

theorem keepV_safe : SafeVars keepV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.cons safeVars_FLAG (safeVars_memPairV 7 (by norm_num)))))

def keepB (n : ℕ) : ℕ := 1 + (2 + (5 + ((2 * n + 3) * 23 + 10 + 1)))

theorem keepTest_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (p : List ℕ) (hp : p.length ≤ 2 * n + 3) :
    TestSpec keepTest keepV (keepB n)
      (fun m => (FCtx k g U m ∧ PArrIs m STEPS (Network.steps p)) ∧ m (X_ 6) ∈ arrAt m (m UARR))
      (fun m => !decide ((m (m (X_ 6) + 1), m (m (X_ 6))) ∈ Network.steps p)) := by
  have hsteps : (Network.steps p).length ≤ 2 * n + 3 := by
    rw [steps_eq_range, List.length_map, List.length_range]; omega
  -- the prefix: the swapped record at `G_ 31`
  have hc : RSpec (.seq (load (G_ 29) (X_ 6)) (.seq (field1M (X_ 6) (G_ 30)) (mkPairM (G_ 30) (G_ 29) (G_ 31))))
      ([G_ 29] ++ ([G_ 30] ++ [G_ 31])) (1 + (2 + 5))
      (fun m => (FCtx k g U m ∧ PArrIs m STEPS (Network.steps p)) ∧ m (X_ 6) ∈ arrAt m (m UARR))
      (fun m m' => (FCtx k g U m' ∧ PArrIs m' STEPS (Network.steps p)) ∧ IN ≤ m' (G_ 31) ∧ m' (G_ 31) + 2 ≤ m' HP ∧
        m' (m' (G_ 31)) = m (m (X_ 6) + 1) ∧ m' (m' (G_ 31) + 1) = m (m (X_ 6))) := by
    intro m0 hm0
    obtain ⟨⟨hF0, hS0⟩, hx0⟩ := hm0
    have hctx0 := hF0.ctx
    have hhp0 : 200 ≤ m0 HP := hctx0.2.2
    obtain ⟨hq1, hq2⟩ := hF0.2.1.2.2 _ hx0
    obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b⟩ := loadM_spec (X_ 6) (G_ 29) (by constructor <;> addr3) Ctx m0 hctx0
    have hV29 : ∀ x, x ∈ [G_ 29] → x < IN := fun x hx => by simp at hx; subst hx; addr3
    have hx1 : m1 (X_ 6) = m0 (X_ 6) := ag1.var (X_ 6) (lt_hp hhp0 (by decide)) (by decide) (by decide)
    obtain ⟨m2, k2, e2, hk2, ag2, h2a, h2b⟩ := field1M_spec (X_ 6) (G_ 30) (by constructor <;> addr3) (by addr3)
      (fun m => Ctx m ∧ IN ≤ m (X_ 6)) (fun m hm => hm.1) (fun m hm => hm.2) m1
      ⟨Ctx.of_agree hctx0 ag1 (fun x hx => by simp at hx; subst hx; addr3), by rw [hx1]; exact hq1⟩
    have hV30 : ∀ x, x ∈ [G_ 30] → x < IN := fun x hx => by simp at hx; subst hx; addr3
    have hhp1 : 200 ≤ m1 HP := by rw [h1b]; exact hhp0
    obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b, h3c, h3d⟩ := mkPairM_spec (G_ 30) (G_ 29) (G_ 31) (by constructor <;> addr3)
      (by constructor <;> addr3) (by constructor <;> addr3) (by addr3) (by addr3) Ctx (fun m hm => hm) m2
      (Ctx.of_agree (Ctx.of_agree hctx0 ag1 (fun x hx => by simp at hx; subst hx; addr3)) ag2
        (fun x hx => by simp at hx; subst hx; addr3))
    have hV31 : ∀ x, x ∈ [G_ 31] → x < IN := fun x hx => by simp at hx; subst hx; addr3
    have hhp2 : 200 ≤ m2 HP := by rw [h2b]; exact hhp1
    have ag := ag1.trans (ag2.trans ag3)
    have hVall : ∀ x, x ∈ [G_ 29] ++ ([G_ 30] ++ [G_ 31]) → x < IN := fun x hx => by
      simp at hx; rcases hx with h | h | h <;> subst h <;> addr3
    refine ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3), by omega, ag, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m0 m3 hF0 ag,
        hS0.stable ag hVall (by addrf) (by addrf) (by decide)⟩
    · rw [h3a, h2b, h1b]; exact hhp0
    · rw [h3a, h3d, h2b, h1b]
    · rw [h3a, h3b, h2a, hx1, ag1.heap hV29 _ (by omega) (by omega)]
    · rw [h3a, h3c, ag2.var (G_ 29) (lt_hp hhp1 (by decide)) (by decide) (by decide), h1a]
  have ht := notM_spec (memPairM_spec 7 STEPS (G_ 31) (2 * n + 3) (by norm_num) (by constructor <;> addrf)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun m => (FCtx k g U m ∧ PArrIs m STEPS (Network.steps p)) ∧ IN ≤ m (G_ 31) ∧ m (G_ 31) + 2 ≤ m HP)
    (fun m hm => hm.1.1.ctx) (fun m hm => ⟨hm.1.2.1, by rw [hm.1.2.len]; exact hsteps, hm.2.1, hm.2.2⟩)
    (fun m m' hm hag => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      refine ⟨⟨FCtx.stableP (safeVars_memPairV 7 (by norm_num)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) m m' hm.1.1 hag,
        hm.1.2.stable hag (fun x hx => (safeVars_memPairV 7 (by norm_num) x hx).2.1) (by addrf) (by addrf) (by decide)⟩,
        ?_, ?_⟩
      · rw [hag.var (G_ 31) (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2.1
      · rw [hag.var (G_ 31) (lt_hp hhp (by decide)) (by decide) (by decide)]; exact le_trans hm.2.2 hag.2))
    (fun x hx => (safeVars_memPairV 7 (by norm_num) x hx).1) (fun m hm => hm.1.1.ctx)
  refine (TestSpec.after hc ht ?_ ?_).mono (V' := keepV) (B' := keepB n) (fun x hx => hx) (by unfold keepB; omega)
    (fun m hm => hm)
  · intro m m₁ _ _ hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  · intro m m₁ _ _ hp
    dsimp only
    rw [hp.2.2.2.1, hp.2.2.2.2, hp.1.2.2]


theorem le_flowBound (n : ℕ) : 2 * n + 3 ≤ flowBound n := by
  unfold flowBound; exact Nat.le_mul_of_pos_left _ (by omega)

/-- `NEWU := augment UARR PATH` (given `STEPS = steps PATH`). -/
def augmentM : Cmd :=
  .seq (.seq (filterM 6 UARR keepTest) (mov (G_ 27) (OUT_ 6)))
    (.seq (.seq (filterM 6 STEPS (memPairM 7 ARCS (X_ 6))) (mov (G_ 28) (OUT_ 6)))
      (.seq (appendM 6 (G_ 27) (G_ 28)) (mov NEWU (OUT_ 6))))

def augmentV : List ℕ :=
  (Lvars 6 ++ FLAG :: keepV ++ [G_ 27]) ++ ((Lvars 6 ++ FLAG :: memPairV 7 ++ [G_ 28]) ++ (Lvars 6 ++ [NEWU]))

theorem augmentV_safe : SafeVars augmentV :=
  SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 6 (by norm_num)) (SafeVars.cons safeVars_FLAG keepV_safe))
      (safeVars_of_decide _ (by decide)))
    (SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 6 (by norm_num))
        (SafeVars.cons safeVars_FLAG (safeVars_memPairV 7 (by norm_num)))) (safeVars_of_decide _ (by decide)))
      (SafeVars.append (safeVars_Lvars 6 (by norm_num)) (safeVars_of_decide _ (by decide))))

def augmentB (n : ℕ) : ℕ :=
  (flowBound n * (keepB n + 14) + 9 + 1) +
    (((2 * n + 3) * (arcBound n * 23 + 10 + 14) + 9 + 1) + (2 * flowBound n * 12 + 15 + 1))

theorem augmentM_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hn : Sized n g)
    (hU : U.length ≤ flowBound n) (p : List ℕ) (hp : p.length ≤ 2 * n + 3) :
    RSpec augmentM augmentV (augmentB n) (fun m => FCtx k g U m ∧ PArrIs m STEPS (Network.steps p))
      (fun _ m' => FCtx k g U m' ∧ PArrIs m' NEWU ((g.networkL g.base.canonIds).augment U p)) := by
  have hsteps : (Network.steps p).length ≤ 2 * n + 3 := by
    rw [steps_eq_range, List.length_map, List.length_range]; omega
  let Pre : Mem → Prop := fun m => FCtx k g U m ∧ PArrIs m STEPS (Network.steps p)
  have hPre : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V →
      NETN ∉ V → ARCS ∉ V → UARR ∉ V → STEPS ∉ V → StableP Pre V := fun hV h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    (FCtx.stableP hV h1 h2 h3 h4 h5 h6 h7 h8).and
      (PArrIs.stableP (P := STEPS) (fun x hx => (hV x hx).2.1) (by addrf) (by addrf) h9)
  have hs1 : SafeVars (Lvars 6 ++ FLAG :: keepV) :=
    SafeVars.append (safeVars_Lvars 6 (by norm_num)) (SafeVars.cons safeVars_FLAG keepV_safe)
  have hs1' : SafeVars (Lvars 6 ++ FLAG :: keepV ++ [G_ 27]) := SafeVars.append hs1 (safeVars_of_decide _ (by decide))
  have hs1X : SafeVars (LvarsX 6 ++ FLAG :: keepV) :=
    SafeVars.append (safeVars_LvarsX 6 (by norm_num)) (SafeVars.cons safeVars_FLAG keepV_safe)
  -- `G_ 27 := U.filter (swap ∉ steps p)`
  have s1 := (filterM_parr_spec 6 UARR (G_ 27) (flowBound n) U (fun a => decide ((a.2, a.1) ∉ Network.steps p))
    (keepTest_spec k g U n p hp) (by norm_num) (fun x hx => ⟨(keepV_safe x hx).1, (keepV_safe x hx).2.1⟩)
    (by constructor <;> addrf) (by decide) (by decide) (by decide) (by decide) (by decide) (by constructor <;> addr3)
    (fun m hm => hm.1.ctx) (fun m hm => hm.1.2) hU
    (hPre hs1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      obtain ⟨hq1, hq2⟩ := hm.1.2.1.2.2 _ hx
      have hV := fun x hx => (hs1X x hx).2.1
      show (!decide ((m' (m' (X_ 6) + 1), m' (m' (X_ 6))) ∈ Network.steps p)) =
        !decide ((m (m (X_ 6) + 1), m (m (X_ 6))) ∈ Network.steps p)
      rw [hag.var (X_ 6) (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV _ (by omega) (by omega),
        hag.heap hV _ hq1 (by omega)])
    (fun m x hm hx => by
      obtain ⟨hq1, hq2⟩ := hm.1.2.1.2.2 _ hx
      show (!decide (((m.write (X_ 6) x) ((m.write (X_ 6) x) (X_ 6) + 1), (m.write (X_ 6) x) ((m.write (X_ 6) x) (X_ 6))) ∈
        Network.steps p)) = decide (((m x, m (x + 1)).2, (m x, m (x + 1)).1) ∉ Network.steps p)
      rw [Mem.write_same, Mem.write_ne _ _ (by addrf), Mem.write_ne _ _ (by addrf), decide_not])).carry
    (hPre hs1' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  -- `G_ 28 := (steps p).filter (∈ arcs)`
  let P2 : Mem → Prop := fun m => Pre m ∧ PArrIs m (G_ 27) (U.filter (fun a => decide ((a.2, a.1) ∉ Network.steps p)))
  have hP2 : ∀ {V : List ℕ}, SafeVars V → IDS ∉ V → RNGN ∉ V → REPS ∉ V → NETS ∉ V → NETT ∉ V →
      NETN ∉ V → ARCS ∉ V → UARR ∉ V → STEPS ∉ V → G_ 27 ∉ V → StableP P2 V :=
    fun hV h1 h2 h3 h4 h5 h6 h7 h8 h9 h27 =>
    (hPre hV h1 h2 h3 h4 h5 h6 h7 h8 h9).and
      (PArrIs.stableP (P := G_ 27) (fun x hx => (hV x hx).2.1) (by addr3) (by addr3) h27)
  have hs2 : SafeVars (Lvars 6 ++ FLAG :: memPairV 7) :=
    SafeVars.append (safeVars_Lvars 6 (by norm_num)) (SafeVars.cons safeVars_FLAG (safeVars_memPairV 7 (by norm_num)))
  have hs2' : SafeVars (Lvars 6 ++ FLAG :: memPairV 7 ++ [G_ 28]) := SafeVars.append hs2 (safeVars_of_decide _ (by decide))
  have hs2X : SafeVars (LvarsX 6 ++ FLAG :: memPairV 7) :=
    SafeVars.append (safeVars_LvarsX 6 (by norm_num)) (SafeVars.cons safeVars_FLAG (safeVars_memPairV 7 (by norm_num)))
  have harcs : ∀ m, P2 m → PArrIs m ARCS (g.networkL g.base.canonIds).arcs := fun m hm => hm.1.1.1.2
  have s2 := (filterM_parr_spec 6 STEPS (G_ 28) (2 * n + 3) (Network.steps p)
    (fun e => decide (e ∈ (g.networkL g.base.canonIds).arcs))
    (memPairM_spec 7 ARCS (X_ 6) (arcBound n) (by norm_num) (by constructor <;> addrn) (by constructor <;> addr3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m => P2 m ∧ m (X_ 6) ∈ arrAt m (m STEPS)) (fun m hm => hm.1.1.1.ctx)
      (fun m hm => ⟨(harcs m hm.1).1, by rw [(harcs m hm.1).len]; exact arcs_length_le hn,
        (hm.1.1.2.1.2.2 _ hm.2).1, (hm.1.1.2.1.2.2 _ hm.2).2⟩)
      (fun m m' hm hag => by
        have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
        refine ⟨hP2 (safeVars_memPairV 7 (by norm_num)) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) m m' hm.1 hag, ?_⟩
        have hS := hm.1.1.2.1
        rw [hag.var (X_ 6) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var STEPS (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.arrAt (fun x hx => (safeVars_memPairV 7 (by norm_num) x hx).2.1) _ hS.1 hS.2.1]
        exact hm.2))
    (by norm_num) (fun x hx => ⟨(safeVars_memPairV 7 (by norm_num) x hx).1, (safeVars_memPairV 7 (by norm_num) x hx).2.1⟩)
    (by constructor <;> addrf) (by decide) (by decide) (by decide) (by decide) (by decide) (by constructor <;> addr3)
    (fun m hm => hm.1.1.ctx) (fun m hm => hm.1.2) hsteps
    (hP2 hs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨hq1, hq2⟩ := hm.1.2.1.2.2 _ hx
      have hV := fun x hx => (hs2X x hx).2.1
      have hA := harcs m hm
      show decide ((m' (m' (X_ 6)), m' (m' (X_ 6) + 1)) ∈ pairsAt m' (m' ARCS)) =
        decide ((m (m (X_ 6)), m (m (X_ 6) + 1)) ∈ pairsAt m (m ARCS))
      rw [hag.var (X_ 6) (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV (m (X_ 6)) hq1 (by omega),
        hag.heap hV (m (X_ 6) + 1) (by omega) (by omega), hag.var ARCS (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.pairsAt hV _ hA.1.1 hA.1.2.1 hA.1.2.2])
    (fun m x hm hx => by
      obtain ⟨hq1, hq2⟩ := hm.1.2.1.2.2 _ hx
      have hA := harcs m hm
      show decide (((m.write (X_ 6) x) ((m.write (X_ 6) x) (X_ 6)), (m.write (X_ 6) x) ((m.write (X_ 6) x) (X_ 6) + 1)) ∈
        pairsAt (m.write (X_ 6) x) ((m.write (X_ 6) x) ARCS)) = decide ((m x, m (x + 1)) ∈ (g.networkL g.base.canonIds).arcs)
      rw [Mem.write_same, Mem.write_ne _ _ (by addrf), Mem.write_ne _ _ (by addrf), Mem.write_ne _ _ (by addrn),
        pairsAt_write_lo _ _ _ _ _ (by addr3) hA.1.1 hA.1.2.2, hA.2])).carry
    (hP2 hs2' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
  -- `NEWU := G_ 27 ++ G_ 28`
  let P3 : Mem → Prop := fun m => P2 m ∧
    PArrIs m (G_ 28) ((Network.steps p).filter (fun e => decide (e ∈ (g.networkL g.base.canonIds).arcs)))
  have hs3 : SafeVars (Lvars 6 ++ [NEWU]) := SafeVars.append (safeVars_Lvars 6 (by norm_num)) (safeVars_of_decide _ (by decide))
  have s3 := (appendM_parr_spec 6 (G_ 27) (G_ 28) NEWU (flowBound n) _ _ (by norm_num) (by constructor <;> addr3)
    (by constructor <;> addr3) (by decide) (by decide) (by constructor <;> addrf) P3 (fun m hm => hm.1.1.1.ctx)
    (fun m hm => hm.1.2) (fun m hm => hm.2)
    ⟨le_trans (List.length_filter_le _ _) hU, le_trans (List.length_filter_le _ _) (le_trans hsteps (le_flowBound n))⟩).carry
    (hP2 hs3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) |>.and (PArrIs.stableP (P := G_ 28) (fun x hx => (hs3 x hx).2.1) (by addr3) (by addr3) (by decide)))
  have hall := s1.seqP (s2.seqP s3)
  unfold augmentM augmentV augmentB
  refine hall.mono' (fun x hx => hx) le_rfl (fun m hm => hm) (fun m m' hm hag hp => ?_)
  exact ⟨hp.1.1.1.1, hp.2⟩


/-! ### The Ford–Fulkerson loop -/

/-- One round of the fuelled loop on the state `(stopped, U)`. -/
def ffStep (N : Network ℕ) (st : Bool × List (ℕ × ℕ)) : Bool × List (ℕ × ℕ) :=
  if st.1 then st else if N.t ∈ N.seen st.2 then (false, N.augment st.2 (N.augPath st.2)) else (true, st.2)

theorem ffStep_iterate_true (N : Network ℕ) (U : List (ℕ × ℕ)) : ∀ f, (ffStep N)^[f] (true, U) = (true, U)
  | 0 => rfl
  | f + 1 => by rw [Function.iterate_succ_apply, show ffStep N (true, U) = (true, U) by simp [ffStep]]; exact ffStep_iterate_true N U f

theorem ffAux_eq (N : Network ℕ) : ∀ (f : ℕ) (U : List (ℕ × ℕ)), N.ffAux f U = ((ffStep N)^[f] (false, U)).2
  | 0, U => rfl
  | f + 1, U => by
      rw [Network.ffAux, Function.iterate_succ_apply]
      by_cases ht : N.t ∈ N.seen U
      · rw [if_pos ht, show ffStep N (false, U) = (false, N.augment U (N.augPath U)) by simp [ffStep, ht]]
        exact ffAux_eq N f _
      · rw [if_neg ht, show ffStep N (false, U) = (true, U) by simp [ffStep, ht], ffStep_iterate_true]

theorem maxflow_eq (N : Network ℕ) : N.maxflow = ((ffStep N)^[N.arcs.length + 1] (false, [])).2 := ffAux_eq N _ _

theorem augPath_length_le (N : Network ℕ) (U : List (ℕ × ℕ)) : (N.augPath U).length ≤ N.nodes.length + 1 := by
  rw [augPath_eq]
  have := foldl_exStep_length N U (N.layers U).reverse (0, N.t, [])
  have hl : (N.layers U).reverse.length = N.nodes.length + 1 := by
    rw [List.length_reverse, layers_eq, List.length_map, List.length_range]
  rw [hl] at this
  simpa using this

theorem augment_length_le (N : Network ℕ) (U : List (ℕ × ℕ)) (p : List ℕ) :
    (N.augment U p).length ≤ U.length + (p.length - 1) := by
  unfold Network.augment
  rw [List.length_append]
  have h1 := List.length_filter_le (fun a => decide ((a.2, a.1) ∉ Network.steps p)) U
  have h2 := List.length_filter_le (fun e => decide (e ∈ N.arcs)) (Network.steps p)
  have h3 : (Network.steps p).length = p.length - 1 := by rw [steps_eq_range, List.length_map, List.length_range]
  omega

theorem ffStep_length (N : Network ℕ) (st : Bool × List (ℕ × ℕ)) :
    (ffStep N st).2.length ≤ st.2.length + N.nodes.length := by
  unfold ffStep
  split
  · omega
  · split
    · have := augment_length_le N st.2 (N.augPath st.2)
      have := augPath_length_le N st.2
      simp only; omega
    · simp

theorem ffStep_iterate_length (N : Network ℕ) : ∀ j,
    ((ffStep N)^[j] (false, [])).2.length ≤ j * N.nodes.length
  | 0 => by simp
  | j + 1 => by
      rw [Function.iterate_succ_apply']
      have := ffStep_length N ((ffStep N)^[j] (false, []))
      have := ffStep_iterate_length N j
      rw [Nat.succ_mul]; omega

/-- One round of the machine loop: if not stopped, compute the layers; if `t` is reached,
augment along the path, else stop. -/
def ffBody : Cmd :=
  .ite (.eq (G_ 35) ZERO)
    (.seq layersM (.seq seenTest (.ite (.eq FLAG ONE)
      (.seq augPathM (.seq stepsM (.seq augmentM (mov UARR NEWU))))
      (setc (G_ 35) 1))))
    nop

def ffBodyV : List ℕ := layersV ++ (seenV ++ ((augPathV ++ (stepsV ++ (augmentV ++ [UARR]))) ++ [G_ 35]))

theorem ffBodyV_safe : SafeVars ffBodyV :=
  SafeVars.append layersV_safe (SafeVars.append seenV_safe (SafeVars.append (SafeVars.append augPathV_safe
    (SafeVars.append stepsV_safe (SafeVars.append augmentV_safe (safeVars_of_decide _ (by decide)))))
    (safeVars_of_decide _ (by decide))))

def ffBodyB (n : ℕ) : ℕ :=
  layersB n + (seenBound n * (3 + 11) + 10) + augPathB n + stepsB n + augmentB n + 1 + 10

theorem ffBody_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) (st : Bool × List (ℕ × ℕ))
    (hU : st.2.length ≤ flowBound n) :
    RSpec ffBody ffBodyV (ffBodyB n) (fun m => FCtx k g st.2 m ∧ m (G_ 35) = bitv st.1)
      (fun _ m' => FCtx k g (ffStep (g.networkL g.base.canonIds) st).2 m' ∧
        m' (G_ 35) = bitv (ffStep (g.networkL g.base.canonIds) st).1) := by
  obtain ⟨stop, U⟩ := st
  intro m0 hm0
  obtain ⟨hF0, hS0⟩ := hm0
  simp only at hF0 hS0 hU
  have hctx0 := hF0.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hzero0 : m0 ZERO = 0 := hctx0.2.1
  have hone0 : m0 ONE = 1 := hctx0.1
  cases stop with
  | true =>
    have hc0 : (Cond.eq (G_ 35) ZERO).eval m0 = false := by simp [Cond.eval, hS0, hzero0]
    refine ⟨m0, _, Cmd.Exec.ite_false hc0 (Exec.nop m0), by unfold ffBodyB; omega, Agree.refl m0 ffBodyV, ?_⟩
    rw [show ffStep (g.networkL g.base.canonIds) (true, U) = (true, U) by simp [ffStep]]
    exact ⟨hF0, hS0⟩
  | false =>
    have hc0 : (Cond.eq (G_ 35) ZERO).eval m0 = true := by simp [Cond.eval, hS0, hzero0]
    -- the layers
    obtain ⟨m1, k1, e1, hk1, ag1, hF1, hseen1, hlays1⟩ := layersM_spec k g U n hn hU m0 hF0
    have hhp1 : 200 ≤ m1 HP := hF1.ctx.2.2
    have hS1 : m1 (G_ 35) = 0 := by rw [ag1.var (G_ 35) (lt_hp hhp0 (by decide)) (by decide) (by decide)]; exact hS0
    -- the reachability test
    obtain ⟨m2, k2, e2, hk2, ag2, hfl2⟩ := seenTest_spec k g U n hn m1 ⟨hF1, hseen1⟩
    have hVs : ∀ x, x ∈ seenV → x < IN := fun x hx => (seenV_safe x hx).2.1
    have hF2 : FCtx k g U m2 :=
      FCtx.stableP seenV_safe (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) m1 m2 hF1 ag2
    have hlays2 := hlays1.stable ag2 hVs (by decide)
    have hS2 : m2 (G_ 35) = 0 := by rw [ag2.var (G_ 35) (lt_hp hhp1 (by decide)) (by decide) (by decide)]; exact hS1
    have hone2 : m2 ONE = 1 := hF2.ctx.1
    have hhp2 : 200 ≤ m2 HP := hF2.ctx.2.2
    dsimp only at hfl2
    by_cases ht : (g.networkL g.base.canonIds).t ∈ (g.networkL g.base.canonIds).seen U
    · have hc1 : (Cond.eq FLAG ONE).eval m2 = true := by
        simp only [Cond.eval, hfl2, hone2, ht, decide_true, bitv]; rfl
      -- the augmenting path, its steps, the augmentation
      obtain ⟨m3, k3, e3, hk3, ag3, hF3, hP3⟩ := augPathM_spec k g U n hn hU m2 ⟨hF2, hlays2⟩
      have hp : ((g.networkL g.base.canonIds).augPath U).length ≤ 2 * n + 3 := by
        have := augPath_length_le (g.networkL g.base.canonIds) U
        have := netNodes_length_le hn
        omega
      obtain ⟨m4, k4, e4, hk4, ag4, hF4, hS4⟩ := stepsM_spec k g U n _ hp m3 ⟨hF3, hP3⟩
      obtain ⟨m5, k5, e5, hk5, ag5, hF5, hN5⟩ := augmentM_spec k g U n hn hU _ hp m4 ⟨hF4, hS4⟩
      obtain ⟨m6, k6, e6, hk6, ag6, h6a, h6b⟩ := movM_spec NEWU UARR (by constructor <;> addrf) Ctx m5 hF5.ctx
      have hVu : ∀ x, x ∈ [UARR] → x < IN := fun x hx => by simp at hx; subst hx; addrf
      have hhp5 : 200 ≤ m5 HP := hF5.ctx.2.2
      have hN6 : NetCtx k g m6 :=
        NetCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) m5 m6 hF5.1 ag6
      have hU6 : PArrIs m6 UARR ((g.networkL g.base.canonIds).augment U ((g.networkL g.base.canonIds).augPath U)) :=
        hN5.mov ag6 hVu h6a
      have ag := ag1.trans (ag2.trans ((ag3.trans (ag4.trans (ag5.trans ag6))).trans (Agree.refl m6 [G_ 35])))
      refine ⟨m6, _, Cmd.Exec.ite_true hc0 (Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc1
        (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 e6)))))), by unfold ffBodyB; omega, ag, ?_⟩
      rw [show ffStep (g.networkL g.base.canonIds) (false, U) =
        (false, (g.networkL g.base.canonIds).augment U ((g.networkL g.base.canonIds).augPath U)) by simp [ffStep, ht]]
      refine ⟨⟨hN6, hU6⟩, ?_⟩
      have ag36 := ag3.trans (ag4.trans (ag5.trans ag6))
      rw [ag36.var (G_ 35) (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact hS2
    · have hc1 : (Cond.eq FLAG ONE).eval m2 = false := by
        simp only [Cond.eval, hfl2, hone2, ht, decide_false, bitv]; rfl
      obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write (G_ 35) 1 := ⟨_, rfl⟩
      have e3 : Cmd.Exec (setc (G_ 35) 1) m2 m3 1 := by rw [hm3]; exact Exec.setc _ _ _
      have ag3 : Agree m2 m3 [G_ 35] := by rw [hm3]; exact Agree.write _ _ _ (by addr3)
      have hF3 : FCtx k g U m3 :=
        FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) m2 m3 hF2 ag3
      refine ⟨m3, _, Cmd.Exec.ite_true hc0 (Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_false hc1 e3))),
        by unfold ffBodyB; omega, (ag1.trans (ag2.trans ag3)).mono (fun x hx => ?_), ?_⟩
      · rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ h
        · rcases List.mem_append.1 h with h | h
          · exact List.mem_append_right _ (List.mem_append_left _ h)
          · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ h))
      · rw [show ffStep (g.networkL g.base.canonIds) (false, U) = (true, U) by simp [ffStep, ht]]
        exact ⟨hF3, by rw [hm3, Mem.write_same]; rfl⟩


/-- The fuelled loop: `UARR := []`, `|arcs| + 1` rounds. -/
def ffM : Cmd :=
  .seq (emptyArrM UARR) (.seq (setc (G_ 35) 0) (.seq (load (CNT_ 9) ARCS) (.seq (add (CNT_ 9) (CNT_ 9) ONE)
    (.seq (setc (I_ 9) 0) (forLoop (I_ 9) (CNT_ 9) ffBody)))))

def ffV : List ℕ := [UARR] ++ ([G_ 35] ++ ([CNT_ 9] ++ ([CNT_ 9] ++ ([I_ 9] ++ (ffBodyV ++ [I_ 9])))))

theorem ffV_safe : SafeVars ffV :=
  SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
    (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append (safeVars_of_decide _ (by decide))
      (SafeVars.append (safeVars_of_decide _ (by decide)) (SafeVars.append ffBodyV_safe (safeVars_of_decide _ (by decide)))))))

def ffB (n : ℕ) : ℕ := 3 + 1 + 1 + 1 + 1 + ((arcBound n + 1) * (ffBodyB n + 3) + 2)

/-- The invariant of the fuelled loop after `j` rounds (relative to the state `m5` before the loop). -/
def FfInv (k : ℕ) (g : GInstance) (m5 : Mem) (j : ℕ) (m : Mem) : Prop :=
  Agree m5 m (ffBodyV ++ [I_ 9]) ∧
    FCtx k g ((ffStep (g.networkL g.base.canonIds))^[j] (false, [])).2 m ∧
    m (G_ 35) = bitv ((ffStep (g.networkL g.base.canonIds))^[j] (false, [])).1 ∧
    m (I_ 9) = j ∧ m (CNT_ 9) = (g.networkL g.base.canonIds).arcs.length + 1

theorem iterate_length_le {n : ℕ} {g : GInstance} (hn : Sized n g) (j : ℕ)
    (hj : j ≤ (g.networkL g.base.canonIds).arcs.length + 1) :
    ((ffStep (g.networkL g.base.canonIds))^[j] (false, [])).2.length ≤ flowBound n := by
  have := ffStep_iterate_length (g.networkL g.base.canonIds) j
  have hNL := netNodes_length_le hn
  have hA := arcs_length_le hn
  have : j * (g.networkL g.base.canonIds).nodes.length ≤ (arcBound n + 1) * (2 * n + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold flowBound; omega

theorem ffM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec ffM ffV (ffB n) (NetCtx k g) (fun _ m' => FCtx k g (g.networkL g.base.canonIds).maxflow m') := by
  intro m0 hm0
  have hctx0 := hm0.1.1.1.1.ctx
  have hhp0 : 200 ≤ m0 HP := hctx0.2.2
  have hA := arcs_length_le hn
  -- `UARR := []`
  obtain ⟨m1, k1, e1, hk1, ag1, h1a, h1b, h1c⟩ := emptyArrM_spec UARR (by constructor <;> addrf) Ctx (fun m hm => hm) m0 hctx0
  have hN1 : NetCtx k g m1 :=
    NetCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m0 m1 hm0 ag1
  have hU1 : PArrIs m1 UARR [] := by
    refine ⟨⟨by rw [h1a]; exact hhp0, by rw [h1a, h1b, h1c], fun q hq => ?_⟩, by rw [h1a, pairsAt, arrAt_nil h1b]; rfl⟩
    rw [h1a, arrAt_nil h1b] at hq; simp at hq
  have hF1 : FCtx k g [] m1 := ⟨hN1, hU1⟩
  -- `G_ 35 := 0`, `CNT_ 9 := |arcs| + 1`, `I_ 9 := 0`
  obtain ⟨m2, k2, e2, hk2, ag2, h2a, h2b⟩ := setcM_spec (G_ 35) 0 (by constructor <;> addr3) Ctx m1 hF1.ctx
  have hV35 : ∀ x, x ∈ [G_ 35] → x < IN := fun x hx => by simp at hx; subst hx; addr3
  have hF2 : FCtx k g [] m2 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m1 m2 hF1 ag2
  obtain ⟨m3, k3, e3, hk3, ag3, h3a, h3b⟩ := loadM_spec ARCS (CNT_ 9) (by constructor <;> addr3) Ctx m2 hF2.ctx
  have hV9 : ∀ x, x ∈ [CNT_ 9] → x < IN := fun x hx => by simp at hx; subst hx; addr3
  have hF3 : FCtx k g [] m3 :=
    FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) m2 m3 hF2 ag3
  have hhp2 : 200 ≤ m2 HP := hF2.ctx.2.2
  have h3c : m3 (CNT_ 9) = (g.networkL g.base.canonIds).arcs.length := by rw [h3a, hF2.1.2.len]
  have h3s : m3 (G_ 35) = 0 := by rw [ag3.var (G_ 35) (lt_hp hhp2 (by decide)) (by decide) (by decide)]; exact h2a
  have hone3 : m3 ONE = 1 := hF3.ctx.1
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write (CNT_ 9) ((g.networkL g.base.canonIds).arcs.length + 1) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (add (CNT_ 9) (CNT_ 9) ONE) m3 m4 1 := by
    have := Exec.add (CNT_ 9) (CNT_ 9) ONE m3; rwa [h3c, hone3, ← hm4] at this
  have ag4 : Agree m3 m4 [CNT_ 9] := by rw [hm4]; exact Agree.write _ _ _ (by addr3)
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write (I_ 9) 0 := ⟨_, rfl⟩
  have e5 : Cmd.Exec (setc (I_ 9) 0) m4 m5 1 := by rw [hm5]; exact Exec.setc _ _ _
  have ag5 : Agree m4 m5 [I_ 9] := by rw [hm5]; exact Agree.write _ _ _ (by addr3)
  have ag45 : Agree m3 m5 ([CNT_ 9] ++ [I_ 9]) := ag4.trans ag5
  have hF5 : FCtx k g [] m5 :=
    FCtx.stableP (SafeVars.append (safeVars_of_decide _ (by decide)) (safeVars_of_decide _ (by decide))) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) m3 m5 hF3 ag45
  have h5c : m5 (CNT_ 9) = (g.networkL g.base.canonIds).arcs.length + 1 := by
    rw [hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_same]
  have h5i : m5 (I_ 9) = 0 := by rw [hm5, Mem.write_same]
  have h5s : m5 (G_ 35) = 0 := by rw [hm5, Mem.write_ne _ _ (by addr3), hm4, Mem.write_ne _ _ (by addr3)]; exact h3s
  -- the loop
  have hVb : ∀ x, x ∈ ffBodyV → x < IN := fun x hx => (ffBodyV_safe x hx).2.1
  have main := loopR_spec 9 (by norm_num) ffBody ffBodyV (ffBodyB n) ((g.networkL g.base.canonIds).arcs.length + 1)
    (FfInv k g m5) hVb (by decide) (by decide)
    (fun j m hm => ⟨hm.2.2.2.1, hm.2.2.2.2, hm.2.1.ctx.1, hm.2.1.ctx.2.2⟩) ?_ 0 m5 (Nat.zero_le _)
    ⟨Agree.refl _ _, by simpa using hF5, by simpa using h5s, h5i, h5c⟩
  · obtain ⟨m', kk, e, inv', hk⟩ := main
    obtain ⟨ag', hF', _, _, _⟩ := inv'
    refine ⟨m', _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5 e)))), ?_,
      ag1.trans (ag2.trans (ag3.trans (ag45.trans ag'))), ?_⟩
    · have : ((g.networkL g.base.canonIds).arcs.length + 1 - 0) * (ffBodyB n + 3) ≤ (arcBound n + 1) * (ffBodyB n + 3) :=
        Nat.mul_le_mul_right _ (by omega)
      unfold ffB; omega
    · rw [maxflow_eq]; exact hF'
  · -- the body
    intro j m hj hm
    obtain ⟨hag, hF, hS, hi, hc⟩ := hm
    have hhp : 200 ≤ m HP := hF.ctx.2.2
    obtain ⟨m', kk, e, hk, agB, hF', hS'⟩ := ffBody_spec k g n hn _ (iterate_length_le hn j (by omega)) m ⟨hF, hS⟩
    have agW : Agree m' (m'.write (I_ 9) (j + 1)) [I_ 9] := Agree.write _ _ _ (by addr3)
    have hhp' : 200 ≤ m' HP := hF'.ctx.2.2
    refine ⟨m', kk, e, hk, agB, ?_, ?_, ?_, by rw [Mem.write_same], ?_⟩
    · refine ((hag.trans agB).mono (fun x hx => ?_)).write_mem (I_ 9) (j + 1) (by decide) (by addr3)
      rcases List.mem_append.1 hx with h | h
      · exact h
      · exact List.mem_append_left _ h
    · rw [Function.iterate_succ_apply']
      exact FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) m' _ hF' agW
    · rw [Function.iterate_succ_apply', Mem.write_ne _ _ (by addr3)]; exact hS'
    · rw [Mem.write_ne _ _ (by addr3), agB.var (CNT_ 9) (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hc

/-! ### Counting the flow -/

/-- `VAL := |UARR.filter (·.1 = s)|`. -/
def countM : Cmd :=
  .seq (.seq (filterM 6 UARR (.seq (load (G_ 36) (X_ 6)) (eqTest (G_ 36) NETS))) (mov (G_ 37) (OUT_ 6)))
    (load VAL (G_ 37))

def countV : List ℕ := (Lvars 6 ++ FLAG :: ([G_ 36] ++ [FLAG]) ++ [G_ 37]) ++ [VAL]

theorem countV_safe : SafeVars countV :=
  SafeVars.append (SafeVars.append (SafeVars.append (safeVars_Lvars 6 (by norm_num))
    (SafeVars.cons safeVars_FLAG (safeVars_of_decide _ (by decide)))) (safeVars_of_decide _ (by decide)))
    (safeVars_of_decide _ (by decide))

def countB (n : ℕ) : ℕ := (flowBound n * (1 + 3 + 14) + 9 + 1) + 1

theorem countM_spec (k : ℕ) (g : GInstance) (U : List (ℕ × ℕ)) (n : ℕ) (hU : U.length ≤ flowBound n) :
    RSpec countM countV (countB n) (FCtx k g U)
      (fun _ m' => NetCtx k g m' ∧ m' VAL = (U.filter (fun a => a.1 == g.netS)).length) := by
  have hs : SafeVars (Lvars 6 ++ FLAG :: ([G_ 36] ++ [FLAG])) :=
    SafeVars.append (safeVars_Lvars 6 (by norm_num)) (SafeVars.cons safeVars_FLAG (safeVars_of_decide _ (by decide)))
  have hsX : SafeVars (LvarsX 6 ++ FLAG :: ([G_ 36] ++ [FLAG])) :=
    SafeVars.append (safeVars_LvarsX 6 (by norm_num)) (SafeVars.cons safeVars_FLAG (safeVars_of_decide _ (by decide)))
  have ht := TestSpec.after (loadM_spec (X_ 6) (G_ 36) (by constructor <;> addr3)
      (fun m => FCtx k g U m ∧ m (X_ 6) ∈ arrAt m (m UARR)))
    (eqTest_spec (G_ 36) NETS (fun m => FCtx k g U m)) (fun m m₁ hm hag _ =>
      FCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) m m₁ hm.1 hag)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      show decide (m₁ (G_ 36) = m₁ NETS) = decide (m (m (X_ 6)) = m NETS)
      rw [hp.1, hag.var NETS (lt_hp hhp (by decide)) (by decide) (by decide)])
  have s1 := filterM_parr_spec 6 UARR (G_ 37) (flowBound n) U (fun a => a.1 == g.netS) ht (by norm_num)
    (fun x hx => ⟨(safeVars_of_decide _ (by decide) x hx).1, (safeVars_of_decide _ (by decide) x hx).2.1⟩)
    (by constructor <;> addrf) (by decide) (by decide) (by decide) (by decide) (by decide) (by constructor <;> addr3)
    (fun m hm => hm.ctx) (fun m hm => hm.2) hU
    (FCtx.stableP hs (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun m m' hm hx hag => by
      have hhp : 200 ≤ m HP := hm.ctx.2.2
      obtain ⟨hq1, hq2⟩ := hm.2.1.2.2 _ hx
      have hV := fun x hx => (hsX x hx).2.1
      show decide (m' (m' (X_ 6)) = m' NETS) = decide (m (m (X_ 6)) = m NETS)
      rw [hag.var (X_ 6) (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV (m (X_ 6)) hq1 (by omega),
        hag.var NETS (lt_hp hhp (by decide)) (by decide) (by decide)])
    (fun m x hm hx => by
      obtain ⟨hq1, hq2⟩ := hm.2.1.2.2 _ hx
      show decide ((m.write (X_ 6) x) ((m.write (X_ 6) x) (X_ 6)) = (m.write (X_ 6) x) NETS) = ((m x, m (x + 1)).1 == g.netS)
      rw [Mem.write_same, Mem.write_ne _ _ (by addrf), Mem.write_ne _ _ (by addrn), hm.1.1.2.1, Bool.beq_eq_decide_eq])
  intro m hm
  obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hP₁⟩ := s1 m hm
  have hN₁ : NetCtx k g m₁ :=
    NetCtx.stableP (SafeVars.append hs (safeVars_of_decide _ (by decide))) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) m m₁ hm.1 ag₁
  obtain ⟨m₂, k₂, e₂, hk₂, ag₂, h2a, h2b⟩ := loadM_spec (G_ 37) VAL (by constructor <;> addr3) Ctx m₁ hN₁.1.1.1.1.ctx
  refine ⟨m₂, _, Cmd.Exec.seq e₁ e₂, by unfold countB; omega, ag₁.trans ag₂, ?_, ?_⟩
  · exact NetCtx.stableP (safeVars_of_decide _ (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m₁ m₂ hN₁ ag₂
  · rw [h2a, hP₁.len]

/-- The flow value `ρ`: the fuelled loop, then the count. -/
def rhoM : Cmd := .seq ffM countM

def rhoV : List ℕ := ffV ++ countV

theorem rhoV_safe : SafeVars rhoV := SafeVars.append ffV_safe countV_safe

def rhoB (n : ℕ) : ℕ := ffB n + countB n

theorem rhoM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    RSpec rhoM rhoV (rhoB n) (NetCtx k g) (fun _ m' => NetCtx k g m' ∧ m' VAL = g.rhoFlowL g.base.canonIds) :=
  (ffM_spec k g n hn).seqP (countM_spec k g _ n (by
    rw [maxflow_eq]; exact iterate_length_le hn _ le_rfl))

end DisequalityDispersion.Machine
