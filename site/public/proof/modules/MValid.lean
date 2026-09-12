import MParseRec
import MLib3

/-! # Validation on the machine

After parsing, the fields of the instance are copied into global variables (`loadInstM`,
giving the context `InstCtx`), and `GInstance.isValid` is evaluated by a sequence of tests. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### The instance context -/

/-- The parsed instance `(k, g)` laid out in memory: the globals point to its parts. -/
structure InstCtx (k : ℕ) (g : GInstance) (m : Mem) : Prop where
  ctx : Ctx m
  kv : m KV = k
  srcs : RepListOf RepNat m IN (m HP) (m SRCS) g.base.sources
  syms : RepListOf RepPair m IN (m HP) (m SYMS) g.base.symbols
  nodes : RepListOf RepNode m IN (m HP) (m NODES) g.base.nodes
  x : m XV = g.base.x
  y : m YV = g.base.y
  t : m TV = g.base.t
  tests : RepListOf RepPair m IN (m HP) (m TESTS) g.base.tests
  outs : RepListOf RepNat m IN (m HP) (m OUTS) g.outs
  nn : m NN = g.base.nodes.length
  kk : m KK = g.base.sources.length
  mm : m MM = g.base.symbols.length

/-- The global variables of the instance context. -/
def instVars : List ℕ := [KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM]

/-- Variables a phase may write without disturbing the instance context. -/
def SafeVars (V : List ℕ) : Prop := ∀ x, x ∈ V → 5 ≤ x ∧ x < IN ∧ x ∉ instVars

theorem SafeVars.append {V₁ V₂ : List ℕ} (h₁ : SafeVars V₁) (h₂ : SafeVars V₂) : SafeVars (V₁ ++ V₂) := by
  intro x hx; rw [List.mem_append] at hx; rcases hx with h | h
  · exact h₁ x h
  · exact h₂ x h

theorem SafeVars.cons {x : ℕ} {V : List ℕ} (hx : 5 ≤ x ∧ x < IN ∧ x ∉ instVars) (h : SafeVars V) :
    SafeVars (x :: V) := by
  intro y hy; simp only [List.mem_cons] at hy; rcases hy with rfl | hy
  · exact hx
  · exact h y hy

theorem safeVars_of_decide (V : List ℕ)
    (h : V.all (fun x => decide (5 ≤ x ∧ x < IN ∧ x ∉ instVars)) = true) : SafeVars V := by
  intro x hx
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h x hx)

theorem safeVars_Lvars (L : ℕ) (hL : L ≤ 9) : SafeVars (Lvars L) := by
  intro x hx
  have := Lvars_range L hL x hx
  refine ⟨by omega, this.2, ?_⟩
  intro h
  simp only [instVars, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [Lvars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at hx <;>
    simp [I_, CNT_, PTR_, CONT_, X_, OUT_, KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM] at hx <;> omega

theorem safeVars_LvarsX (L : ℕ) (hL : L ≤ 9) : SafeVars (LvarsX L) :=
  fun x hx => safeVars_Lvars L hL x (by
    simp only [LvarsX, List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [Lvars, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)

theorem safeVars_memPairV (L : ℕ) (hL : L + 1 ≤ 9) : SafeVars (memPairV L) := by
  intro x hx
  simp only [memPairV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | rfl | rfl | rfl | rfl
  · exact safeVars_Lvars L (by omega) x h
  · refine ⟨by addr3, by addr3, by decide⟩
  · refine ⟨by addr3, by addr3, ?_⟩
    simp [instVars, X_, KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM]; omega
  · refine ⟨by addr3, by addr3, ?_⟩
    simp [instVars, PTR_, KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM]; omega
  · refine ⟨by addr3, by addr3, by decide⟩

theorem safeVars_rangeV (L : ℕ) (hL : L + 1 ≤ 9) : SafeVars (rangeV L) := by
  refine SafeVars.append (safeVars_Lvars (L + 1) hL) (SafeVars.cons ⟨by addr3, by addr3, ?_⟩ (safeVars_Lvars L (by omega)))
  simp [instVars, RNG, KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM]; omega

theorem safeVars_FLAG : 5 ≤ FLAG ∧ FLAG < IN ∧ FLAG ∉ instVars := ⟨by addr3, by addr3, by decide⟩

theorem safeVars_G (i : ℕ) (hi : i < 60) : 5 ≤ G_ i ∧ G_ i < IN ∧ G_ i ∉ instVars := by
  refine ⟨by addr3, by addr3, ?_⟩
  simp [instVars, G_, KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM]; omega

theorem InstCtx.of_agree {k : ℕ} {g : GInstance} {m m' : Mem} (h : InstCtx k g m) {V : List ℕ}
    (ha : Agree m m' V) (hV : SafeVars V) : InstCtx k g m' := by
  have hVlt : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2.1
  have hv : ∀ x, x ∈ instVars → m' x = m x := by
    intro x hx
    have hlt : x < IN ∧ x ≠ HP := by
      simp only [instVars, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        constructor <;> addr3
    have := h.ctx.2.2
    exact ha.var x (by omega) hlt.2 (fun h' => (hV x h').2.2 hx)
  have hframe : ∀ x, IN ≤ x → x < m HP → m' x = m x := fun x h1 h2 => ha.heap hVlt x h1 h2
  have gn := goodRep_listOf goodRep_nat
  have gp := goodRep_listOf goodRep_pair
  have gd := goodRep_listOf goodRep_node
  refine ⟨h.ctx.of_agree ha (fun x hx => (hV x hx).1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv KV (by simp [instVars]), h.kv]
  · rw [hv SRCS (by simp [instVars])]
    exact gn.mono m' IN (m HP) IN (m' HP) _ _ (gn.frame m m' IN (m HP) _ _ h.srcs hframe) le_rfl ha.2
  · rw [hv SYMS (by simp [instVars])]
    exact gp.mono m' IN (m HP) IN (m' HP) _ _ (gp.frame m m' IN (m HP) _ _ h.syms hframe) le_rfl ha.2
  · rw [hv NODES (by simp [instVars])]
    exact gd.mono m' IN (m HP) IN (m' HP) _ _ (gd.frame m m' IN (m HP) _ _ h.nodes hframe) le_rfl ha.2
  · rw [hv XV (by simp [instVars]), h.x]
  · rw [hv YV (by simp [instVars]), h.y]
  · rw [hv TV (by simp [instVars]), h.t]
  · rw [hv TESTS (by simp [instVars])]
    exact gp.mono m' IN (m HP) IN (m' HP) _ _ (gp.frame m m' IN (m HP) _ _ h.tests hframe) le_rfl ha.2
  · rw [hv OUTS (by simp [instVars])]
    exact gn.mono m' IN (m HP) IN (m' HP) _ _ (gn.frame m m' IN (m HP) _ _ h.outs hframe) le_rfl ha.2
  · rw [hv NN (by simp [instVars]), h.nn]
  · rw [hv KK (by simp [instVars]), h.kk]
  · rw [hv MM (by simp [instVars]), h.mm]

theorem InstCtx.stableP {k : ℕ} {g : GInstance} {V : List ℕ} (hV : SafeVars V) :
    StableP (InstCtx k g) V := fun _ _ h ha => h.of_agree ha hV


/-! ### Loading the parsed instance into the globals -/

/-- `D := M[M[Q] + off]`. -/
def fieldM (Q D off : ℕ) : Cmd := .seq (setc D off) (.seq (add D D Q) (load D D))

theorem fieldM_exec (Q D off : ℕ) (m : Mem) (hDQ : D ≠ Q) (hheap : m Q + off ≠ D) :
    Cmd.Exec (fieldM Q D off) m (m.write D (m (m Q + off))) 3 := by
  have e1 := Exec.setc D off m
  have e2 := Exec.add D D Q (m.write D off)
  rw [Mem.write_same, Mem.write_ne _ _ (Ne.symm hDQ), Mem.write_write, Nat.add_comm off] at e2
  have e3 := Exec.load D D (m.write D (m Q + off))
  rw [Mem.write_same, Mem.write_ne _ _ hheap, Mem.write_write] at e3
  exact Cmd.Exec.seq e1 (Cmd.Exec.seq e2 e3)

/-- Copy the parsed `(k, g)` (record at `VAL`) into the globals. -/
def loadInstM : Cmd :=
  .seq (fieldM VAL KV 0) (.seq (fieldM VAL (G_ 0) 1) (.seq (fieldM (G_ 0) BASE 0)
    (.seq (fieldM (G_ 0) OUTS 1) (.seq (fieldM BASE SRCS 0) (.seq (fieldM BASE SYMS 1)
      (.seq (fieldM BASE NODES 2) (.seq (fieldM BASE XV 3) (.seq (fieldM BASE YV 4)
        (.seq (fieldM BASE TV 5) (.seq (fieldM BASE TESTS 6) (.seq (fieldM NODES NN 0)
          (.seq (fieldM SRCS KK 0) (fieldM SYMS MM 0)))))))))))))

/-- The variables written by `loadInstM`. -/
def loadVars : List ℕ := [KV, G_ 0, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV, TESTS, NN, KK, MM]

theorem ne_of_ge_200 {a c : ℕ} (h : 200 ≤ a) (hc : c < 200) : a ≠ c := by omega

theorem loadInstM_spec (k : ℕ) (g : GInstance) (m : Mem) (hctx : Ctx m)
    (hrep : RepKG m IN (m HP) (m VAL) (k, g)) :
    ∃ m', Cmd.Exec loadInstM m m' 42 ∧ Agree m m' loadVars ∧ InstCtx k g m' := by
  obtain ⟨hone, hzero, hhp⟩ := hctx
  obtain ⟨hv1, hv2, hkv, hg1, hg2, hbase, houts⟩ := hrep
  obtain ⟨hb1, hb2, hsrcs, hsyms, hnodes, hx, hy, ht, htests⟩ := hbase
  obtain ⟨v, hv⟩ : ∃ v, v = m VAL := ⟨_, rfl⟩
  obtain ⟨gp, hgp⟩ : ∃ gp, gp = m (v + 1) := ⟨_, rfl⟩
  obtain ⟨bp, hbp⟩ : ∃ bp, bp = m gp := ⟨_, rfl⟩
  rw [← hv] at hv1 hv2 hkv hg1 hg2 houts hb1 hb2 hsrcs hsyms hnodes hx hy ht htests
  rw [← hgp] at hg1 hg2 houts hb1 hb2 hsrcs hsyms hnodes hx hy ht htests
  rw [← hbp] at hb1 hb2 hsrcs hsyms hnodes hx hy ht htests
  have hv1' : 200 ≤ v := hv1
  have hg1' : 200 ≤ gp := hg1
  have hb1' : 200 ≤ bp := hb1
  have hnIN' : 200 ≤ m (bp + 2) := hnodes.1
  have hsIN' : 200 ≤ m bp := hsrcs.1
  have hyIN' : 200 ≤ m (bp + 1) := hsyms.1
  have hvVAL : 200 ≤ m VAL := by rw [← hv]; exact hv1'
  have hv1p : 200 ≤ v + 1 := by omega
  have hgp1 : 200 ≤ gp + 1 := by omega
  have hbpk : ∀ i, 200 ≤ bp + i := fun i => by omega
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write KV k := ⟨_, rfl⟩
  have e1 : Cmd.Exec (fieldM VAL KV 0) m m1 3 := by
    have := fieldM_exec VAL KV 0 m (by decide) (by rw [Nat.add_zero]; exact ne_of_ge_200 hvVAL (by decide))
    rwa [Nat.add_zero, ← hv, hkv, ← hm1] at this
  have q1 : ∀ x, x ≠ KV → m1 x = m x := fun x h1 => by rw [hm1, Mem.write_ne _ _ h1]
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write (G_ 0) gp := ⟨_, rfl⟩
  have e2 : Cmd.Exec (fieldM VAL (G_ 0) 1) m1 m2 3 := by
    have := fieldM_exec VAL (G_ 0) 1 m1 (by decide) (by rw [q1 VAL (by decide), ← hv]; exact ne_of_ge_200 hv1p (by decide))
    rwa [q1 VAL (by decide), ← hv, q1 (v + 1) (ne_of_ge_200 hv1p (by decide)), ← hgp, ← hm2] at this
  have q2 : ∀ x, x ≠ KV → x ≠ G_ 0 → m2 x = m x := fun x h1 h2 => by rw [hm2, Mem.write_ne _ _ h2, q1 x h1]
  have m2G : m2 (G_ 0) = gp := by rw [hm2, Mem.write_same]
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write BASE bp := ⟨_, rfl⟩
  have e3 : Cmd.Exec (fieldM (G_ 0) BASE 0) m2 m3 3 := by
    have := fieldM_exec (G_ 0) BASE 0 m2 (by decide) (by rw [m2G, Nat.add_zero]; exact ne_of_ge_200 hg1' (by decide))
    rwa [m2G, Nat.add_zero, q2 gp (ne_of_ge_200 hg1' (by decide)) (ne_of_ge_200 hg1' (by decide)), ← hbp, ← hm3] at this
  have q3 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → m3 x = m x := fun x h1 h2 h3 => by rw [hm3, Mem.write_ne _ _ h3, q2 x h1 h2]
  have m3G : m3 (G_ 0) = gp := by rw [hm3, Mem.write_ne _ _ (by decide), m2G]
  have m3B : m3 BASE = bp := by rw [hm3, Mem.write_same]
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write OUTS (m (gp + 1)) := ⟨_, rfl⟩
  have e4 : Cmd.Exec (fieldM (G_ 0) OUTS 1) m3 m4 3 := by
    have := fieldM_exec (G_ 0) OUTS 1 m3 (by decide) (by rw [m3G]; exact ne_of_ge_200 hgp1 (by decide))
    rwa [m3G, q3 (gp + 1) (ne_of_ge_200 hgp1 (by decide)) (ne_of_ge_200 hgp1 (by decide)) (ne_of_ge_200 hgp1 (by decide)), ← hm4] at this
  have q4 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → m4 x = m x := fun x h1 h2 h3 h4 => by rw [hm4, Mem.write_ne _ _ h4, q3 x h1 h2 h3]
  have m4B : m4 BASE = bp := by rw [hm4, Mem.write_ne _ _ (by decide), m3B]
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write SRCS (m bp) := ⟨_, rfl⟩
  have e5 : Cmd.Exec (fieldM BASE SRCS 0) m4 m5 3 := by
    have := fieldM_exec BASE SRCS 0 m4 (by decide) (by rw [m4B, Nat.add_zero]; exact ne_of_ge_200 (hbpk 0) (by decide))
    rwa [m4B, Nat.add_zero, q4 (bp) (ne_of_ge_200 (hbpk 0) (by decide)) (ne_of_ge_200 (hbpk 0) (by decide)) (ne_of_ge_200 (hbpk 0) (by decide)) (ne_of_ge_200 (hbpk 0) (by decide)), ← hm5] at this
  have q5 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → m5 x = m x := fun x h1 h2 h3 h4 h5 => by rw [hm5, Mem.write_ne _ _ h5, q4 x h1 h2 h3 h4]
  have m5B : m5 BASE = bp := by rw [hm5, Mem.write_ne _ _ (by decide), m4B]
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write SYMS (m (bp + 1)) := ⟨_, rfl⟩
  have e6 : Cmd.Exec (fieldM BASE SYMS 1) m5 m6 3 := by
    have := fieldM_exec BASE SYMS 1 m5 (by decide) (by rw [m5B]; exact ne_of_ge_200 (hbpk 1) (by decide))
    rwa [m5B, q5 (bp + 1) (ne_of_ge_200 (hbpk 1) (by decide)) (ne_of_ge_200 (hbpk 1) (by decide)) (ne_of_ge_200 (hbpk 1) (by decide)) (ne_of_ge_200 (hbpk 1) (by decide)) (ne_of_ge_200 (hbpk 1) (by decide)), ← hm6] at this
  have q6 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → m6 x = m x := fun x h1 h2 h3 h4 h5 h6 => by rw [hm6, Mem.write_ne _ _ h6, q5 x h1 h2 h3 h4 h5]
  have m6B : m6 BASE = bp := by rw [hm6, Mem.write_ne _ _ (by decide), m5B]
  obtain ⟨m7, hm7⟩ : ∃ m7, m7 = m6.write NODES (m (bp + 2)) := ⟨_, rfl⟩
  have e7 : Cmd.Exec (fieldM BASE NODES 2) m6 m7 3 := by
    have := fieldM_exec BASE NODES 2 m6 (by decide) (by rw [m6B]; exact ne_of_ge_200 (hbpk 2) (by decide))
    rwa [m6B, q6 (bp + 2) (ne_of_ge_200 (hbpk 2) (by decide)) (ne_of_ge_200 (hbpk 2) (by decide)) (ne_of_ge_200 (hbpk 2) (by decide)) (ne_of_ge_200 (hbpk 2) (by decide)) (ne_of_ge_200 (hbpk 2) (by decide)) (ne_of_ge_200 (hbpk 2) (by decide)), ← hm7] at this
  have q7 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → m7 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 => by rw [hm7, Mem.write_ne _ _ h7, q6 x h1 h2 h3 h4 h5 h6]
  have m7B : m7 BASE = bp := by rw [hm7, Mem.write_ne _ _ (by decide), m6B]
  obtain ⟨m8, hm8⟩ : ∃ m8, m8 = m7.write XV (m (bp + 3)) := ⟨_, rfl⟩
  have e8 : Cmd.Exec (fieldM BASE XV 3) m7 m8 3 := by
    have := fieldM_exec BASE XV 3 m7 (by decide) (by rw [m7B]; exact ne_of_ge_200 (hbpk 3) (by decide))
    rwa [m7B, q7 (bp + 3) (ne_of_ge_200 (hbpk 3) (by decide)) (ne_of_ge_200 (hbpk 3) (by decide)) (ne_of_ge_200 (hbpk 3) (by decide)) (ne_of_ge_200 (hbpk 3) (by decide)) (ne_of_ge_200 (hbpk 3) (by decide)) (ne_of_ge_200 (hbpk 3) (by decide)) (ne_of_ge_200 (hbpk 3) (by decide)), ← hm8] at this
  have q8 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → x ≠ XV → m8 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by rw [hm8, Mem.write_ne _ _ h8, q7 x h1 h2 h3 h4 h5 h6 h7]
  have m8B : m8 BASE = bp := by rw [hm8, Mem.write_ne _ _ (by decide), m7B]
  obtain ⟨m9, hm9⟩ : ∃ m9, m9 = m8.write YV (m (bp + 4)) := ⟨_, rfl⟩
  have e9 : Cmd.Exec (fieldM BASE YV 4) m8 m9 3 := by
    have := fieldM_exec BASE YV 4 m8 (by decide) (by rw [m8B]; exact ne_of_ge_200 (hbpk 4) (by decide))
    rwa [m8B, q8 (bp + 4) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)) (ne_of_ge_200 (hbpk 4) (by decide)), ← hm9] at this
  have q9 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → x ≠ XV → x ≠ YV → m9 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 => by rw [hm9, Mem.write_ne _ _ h9, q8 x h1 h2 h3 h4 h5 h6 h7 h8]
  have m9B : m9 BASE = bp := by rw [hm9, Mem.write_ne _ _ (by decide), m8B]
  obtain ⟨m10, hm10⟩ : ∃ m10, m10 = m9.write TV (m (bp + 5)) := ⟨_, rfl⟩
  have e10 : Cmd.Exec (fieldM BASE TV 5) m9 m10 3 := by
    have := fieldM_exec BASE TV 5 m9 (by decide) (by rw [m9B]; exact ne_of_ge_200 (hbpk 5) (by decide))
    rwa [m9B, q9 (bp + 5) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)) (ne_of_ge_200 (hbpk 5) (by decide)), ← hm10] at this
  have q10 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → x ≠ XV → x ≠ YV → x ≠ TV → m10 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by rw [hm10, Mem.write_ne _ _ h10, q9 x h1 h2 h3 h4 h5 h6 h7 h8 h9]
  have m10B : m10 BASE = bp := by rw [hm10, Mem.write_ne _ _ (by decide), m9B]
  obtain ⟨m11, hm11⟩ : ∃ m11, m11 = m10.write TESTS (m (bp + 6)) := ⟨_, rfl⟩
  have e11 : Cmd.Exec (fieldM BASE TESTS 6) m10 m11 3 := by
    have := fieldM_exec BASE TESTS 6 m10 (by decide) (by rw [m10B]; exact ne_of_ge_200 (hbpk 6) (by decide))
    rwa [m10B, q10 (bp + 6) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)) (ne_of_ge_200 (hbpk 6) (by decide)), ← hm11] at this
  have q11 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → x ≠ XV → x ≠ YV → x ≠ TV → x ≠ TESTS → m11 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 => by rw [hm11, Mem.write_ne _ _ h11, q10 x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  have m11B : m11 BASE = bp := by rw [hm11, Mem.write_ne _ _ (by decide), m10B]
  have m11N : m11 NODES = m (bp + 2) := by
    rw [hm11, Mem.write_ne _ _ (by decide), hm10, Mem.write_ne _ _ (by decide), hm9,
      Mem.write_ne _ _ (by decide), hm8, Mem.write_ne _ _ (by decide), hm7, Mem.write_same]
  have m11S : m11 SRCS = m bp := by
    rw [hm11, Mem.write_ne _ _ (by decide), hm10, Mem.write_ne _ _ (by decide), hm9,
      Mem.write_ne _ _ (by decide), hm8, Mem.write_ne _ _ (by decide), hm7, Mem.write_ne _ _ (by decide),
      hm6, Mem.write_ne _ _ (by decide), hm5, Mem.write_same]
  have m11Y : m11 SYMS = m (bp + 1) := by
    rw [hm11, Mem.write_ne _ _ (by decide), hm10, Mem.write_ne _ _ (by decide), hm9,
      Mem.write_ne _ _ (by decide), hm8, Mem.write_ne _ _ (by decide), hm7, Mem.write_ne _ _ (by decide),
      hm6, Mem.write_same]
  obtain ⟨m12, hm12⟩ : ∃ m12, m12 = m11.write NN (m (m (bp + 2))) := ⟨_, rfl⟩
  have e12 : Cmd.Exec (fieldM NODES NN 0) m11 m12 3 := by
    have := fieldM_exec NODES NN 0 m11 (by decide) (by rw [m11N, Nat.add_zero]; exact ne_of_ge_200 hnIN' (by decide))
    rwa [m11N, Nat.add_zero, q11 (m (bp + 2)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)) (ne_of_ge_200 hnIN' (by decide)), ← hm12] at this
  have q12 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → x ≠ XV → x ≠ YV → x ≠ TV → x ≠ TESTS → x ≠ NN → m12 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by rw [hm12, Mem.write_ne _ _ h12, q11 x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]
  have m12S : m12 SRCS = m bp := by rw [hm12, Mem.write_ne _ _ (by decide), m11S]
  have m12Y : m12 SYMS = m (bp + 1) := by rw [hm12, Mem.write_ne _ _ (by decide), m11Y]
  obtain ⟨m13, hm13⟩ : ∃ m13, m13 = m12.write KK (m (m bp)) := ⟨_, rfl⟩
  have e13 : Cmd.Exec (fieldM SRCS KK 0) m12 m13 3 := by
    have := fieldM_exec SRCS KK 0 m12 (by decide) (by rw [m12S, Nat.add_zero]; exact ne_of_ge_200 hsIN' (by decide))
    rwa [m12S, Nat.add_zero, q12 (m bp) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)) (ne_of_ge_200 hsIN' (by decide)), ← hm13] at this
  have q13 : ∀ x, x ≠ KV → x ≠ G_ 0 → x ≠ BASE → x ≠ OUTS → x ≠ SRCS → x ≠ SYMS → x ≠ NODES → x ≠ XV → x ≠ YV → x ≠ TV → x ≠ TESTS → x ≠ NN → x ≠ KK → m13 x = m x := fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 => by rw [hm13, Mem.write_ne _ _ h13, q12 x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]
  have m13Y : m13 SYMS = m (bp + 1) := by rw [hm13, Mem.write_ne _ _ (by decide), m12Y]
  obtain ⟨m14, hm14⟩ : ∃ m14, m14 = m13.write MM (m (m (bp + 1))) := ⟨_, rfl⟩
  have e14 : Cmd.Exec (fieldM SYMS MM 0) m13 m14 3 := by
    have := fieldM_exec SYMS MM 0 m13 (by decide) (by rw [m13Y, Nat.add_zero]; exact ne_of_ge_200 hyIN' (by decide))
    rwa [m13Y, Nat.add_zero, q13 (m (bp + 1)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)) (ne_of_ge_200 hyIN' (by decide)), ← hm14] at this
  have q14 : ∀ x, x ∉ loadVars → m14 x = m x := by
    intro x hx
    simp only [loadVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hx
    rw [hm14, Mem.write_ne _ _ h14, q13 x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13]
  have hval : ∀ x, x ∈ loadVars → m14 x = (if x = KV then k else if x = G_ 0 then gp else if x = BASE then bp
      else if x = OUTS then m (gp + 1) else if x = SRCS then m bp else if x = SYMS then m (bp + 1)
      else if x = NODES then m (bp + 2) else if x = XV then m (bp + 3) else if x = YV then m (bp + 4)
      else if x = TV then m (bp + 5) else if x = TESTS then m (bp + 6) else if x = NN then m (m (bp + 2))
      else if x = KK then m (m bp) else m (m (bp + 1))) := by
    intro x hx
    rw [hm14, hm13, hm12, hm11, hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hm1]
    simp only [loadVars, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide [Mem.write_apply, KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV, TESTS, NN, KK, MM]
  have hHP : m14 HP = m HP := q14 HP (by decide)
  have hheap : ∀ x, 200 ≤ x → m14 x = m x := fun x hx => q14 x (by
    simp only [loadVars, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ne_of_ge_200 hx (by decide))
  have hag : Agree m m14 loadVars := ⟨fun x _ hx => q14 x (fun h => hx (List.mem_cons_of_mem _ h)), by rw [hHP]⟩
  have hframe : ∀ x, IN ≤ x → x < m HP → m14 x = m x := fun x h1 _ => hheap x h1
  have gn := goodRep_listOf goodRep_nat
  have gp' := goodRep_listOf goodRep_pair
  have gd := goodRep_listOf goodRep_node
  refine ⟨m14, ?_, hag, ?_⟩
  · have := Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5
      (Cmd.Exec.seq e6 (Cmd.Exec.seq e7 (Cmd.Exec.seq e8 (Cmd.Exec.seq e9 (Cmd.Exec.seq e10
        (Cmd.Exec.seq e11 (Cmd.Exec.seq e12 (Cmd.Exec.seq e13 e14))))))))))))
    exact this
  refine ⟨⟨by rw [q14 ONE (by decide)]; exact hone, by rw [q14 ZERO (by decide)]; exact hzero,
    by rw [hHP]; exact hhp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hval KV (by simp [loadVars])]; simp
  · rw [hval SRCS (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS, SRCS]
    rw [hHP]; exact gn.frame m m14 IN (m HP) _ _ hsrcs hframe
  · rw [hval SYMS (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS]
    rw [hHP]; exact gp'.frame m m14 IN (m HP) _ _ hsyms hframe
  · rw [hval NODES (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES]
    rw [hHP]; exact gd.frame m m14 IN (m HP) _ _ hnodes hframe
  · rw [hval XV (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV]; exact hx
  · rw [hval YV (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV]; exact hy
  · rw [hval TV (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV]; exact ht
  · rw [hval TESTS (by simp [loadVars])]
    simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV, TESTS]
    rw [hHP]; exact gp'.frame m m14 IN (m HP) _ _ htests hframe
  · rw [hval OUTS (by simp [loadVars])]; simp +decide [KV, G_, BASE, OUTS]
    rw [hHP]; exact gn.frame m m14 IN (m HP) _ _ houts hframe
  · rw [hval NN (by simp [loadVars])]
    simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV, TESTS, NN]
    exact hnodes.2.2.1
  · rw [hval KK (by simp [loadVars])]
    simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV, TESTS, NN, KK]
    exact hsrcs.2.2.1
  · rw [hval MM (by simp [loadVars])]
    simp +decide [KV, G_, BASE, OUTS, SRCS, SYMS, NODES, XV, YV, TV, TESTS, NN, KK, MM]
    exact hsyms.2.2.1


/-! ### Size bounds -/

/-- All lists of the instance have length at most `n`. -/
structure Sized (n : ℕ) (g : GInstance) : Prop where
  srcs : g.base.sources.length ≤ n
  syms : g.base.symbols.length ≤ n
  nodes : g.base.nodes.length ≤ n
  tests : g.base.tests.length ≤ n
  outs : g.outs.length ≤ n
  args : ∀ nd, nd ∈ g.base.nodes → ∀ f args, nd = Node.app f args → args.length ≤ n

/-! ### Facts derived from the context -/

theorem InstCtx.arr_srcs {k : ℕ} {g : GInstance} {m : Mem} (h : InstCtx k g m) :
    IN ≤ m SRCS ∧ m SRCS + 1 + m (m SRCS) ≤ m HP ∧ arrAt m (m SRCS) = g.base.sources := by
  obtain ⟨h1, h2, h3, h4⟩ := h.srcs
  refine ⟨h1, by rw [h3]; exact h2, arrAt_of_cells h3 h4⟩

theorem InstCtx.arr_outs {k : ℕ} {g : GInstance} {m : Mem} (h : InstCtx k g m) :
    IN ≤ m OUTS ∧ m OUTS + 1 + m (m OUTS) ≤ m HP ∧ arrAt m (m OUTS) = g.outs := by
  obtain ⟨h1, h2, h3, h4⟩ := h.outs
  refine ⟨h1, by rw [h3]; exact h2, arrAt_of_cells h3 h4⟩

/-- The arrays of records: the pointer array and the record cells. -/
theorem InstCtx.arr_syms {k : ℕ} {g : GInstance} {m : Mem} (h : InstCtx k g m) :
    IN ≤ m SYMS ∧ m SYMS + 1 + m (m SYMS) ≤ m HP ∧ (arrAt m (m SYMS)).length = g.base.symbols.length ∧
    ∀ i, (hi : i < g.base.symbols.length) →
      IN ≤ m (m SYMS + 1 + i) ∧ m (m SYMS + 1 + i) + 2 ≤ m HP ∧
      m (m (m SYMS + 1 + i)) = g.base.symbols[i].1 ∧ m (m (m SYMS + 1 + i) + 1) = g.base.symbols[i].2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h.syms
  refine ⟨h1, by rw [h3]; exact h2, by rw [arrAt_length, h3], fun i hi => ?_⟩
  obtain ⟨g1, g2, g3, g4⟩ := h4 i hi
  exact ⟨g1, g2, g3, g4⟩

theorem InstCtx.arr_tests {k : ℕ} {g : GInstance} {m : Mem} (h : InstCtx k g m) :
    IN ≤ m TESTS ∧ m TESTS + 1 + m (m TESTS) ≤ m HP ∧ (arrAt m (m TESTS)).length = g.base.tests.length ∧
    ∀ i, (hi : i < g.base.tests.length) →
      IN ≤ m (m TESTS + 1 + i) ∧ m (m TESTS + 1 + i) + 2 ≤ m HP ∧
      m (m (m TESTS + 1 + i)) = g.base.tests[i].1 ∧ m (m (m TESTS + 1 + i) + 1) = g.base.tests[i].2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h.tests
  refine ⟨h1, by rw [h3]; exact h2, by rw [arrAt_length, h3], fun i hi => ?_⟩
  obtain ⟨g1, g2, g3, g4⟩ := h4 i hi
  exact ⟨g1, g2, g3, g4⟩

/-- The node records. -/
theorem InstCtx.arr_nodes {k : ℕ} {g : GInstance} {m : Mem} (h : InstCtx k g m) :
    IN ≤ m NODES ∧ m NODES + 1 + m (m NODES) ≤ m HP ∧ (arrAt m (m NODES)).length = g.base.nodes.length ∧
    ∀ i, (hi : i < g.base.nodes.length) →
      IN ≤ m (m NODES + 1 + i) ∧ RepNode m IN (m HP) (m (m NODES + 1 + i)) g.base.nodes[i] := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nodes
  refine ⟨h1, by rw [h3]; exact h2, by rw [arrAt_length, h3], fun i hi => ?_⟩
  exact ⟨(h4 i hi).1, h4 i hi⟩

/-! ### The elementary tests of validity -/

theorem decide_two_le (a : ℕ) : decide (2 ≤ a) = decide (1 < a) := by
  cases a with
  | zero => simp
  | succ a => cases a <;> simp

/-- `2 ≤ k` (as `1 < KK`). -/
theorem k2Test_spec (k : ℕ) (g : GInstance) :
    TestSpec (ltTest ONE KK) [FLAG] 3 (InstCtx k g) (fun _ => decide (2 ≤ g.base.k)) :=
  (ltTest_spec ONE KK _).congr (fun m hm => by
    rw [hm.ctx.1, hm.kk, decide_two_le]; rfl)

/-- `x < k`. -/
theorem xkTest_spec (k : ℕ) (g : GInstance) :
    TestSpec (ltTest XV KK) [FLAG] 3 (InstCtx k g) (fun _ => decide (g.base.x < g.base.k)) :=
  (ltTest_spec XV KK _).congr (fun m hm => by rw [hm.x, hm.kk]; rfl)

/-- `y < k`. -/
theorem ykTest_spec (k : ℕ) (g : GInstance) :
    TestSpec (ltTest YV KK) [FLAG] 3 (InstCtx k g) (fun _ => decide (g.base.y < g.base.k)) :=
  (ltTest_spec YV KK _).congr (fun m hm => by rw [hm.y, hm.kk]; rfl)

/-- `x ≠ y`. -/
theorem xyTest_spec (k : ℕ) (g : GInstance) :
    TestSpec (notM (eqTest XV YV)) (FLAG :: [FLAG]) 4 (InstCtx k g) (fun _ => decide (g.base.x ≠ g.base.y)) :=
  (notM_spec (eqTest_spec XV YV _) (by intro x hx; simp at hx; subst hx; addr3) (fun m hm => hm.ctx)).congr
    (fun m hm => by rw [hm.x, hm.y, decide_not])

/-- `t < |nodes|`. -/
theorem tnTest_spec (k : ℕ) (g : GInstance) :
    TestSpec (ltTest TV NN) [FLAG] 3 (InstCtx k g) (fun _ => decide (g.base.t < g.base.nodes.length)) :=
  (ltTest_spec TV NN _).congr (fun m hm => by rw [hm.t, hm.nn])


/-! ### Duplicate detection -/

/-- `decide l.Nodup` as a double scan over indices. -/
theorem nodup_eq_scan (l : List ℕ) :
    decide l.Nodup = !((List.range l.length).any (fun i => (List.range l.length).any (fun j =>
      decide (j < i) && decide (l.getD i 0 = l.getD j 0)))) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.not_eq_true', Bool.eq_false_iff]
  rw [List.Nodup, List.pairwise_iff_getElem]
  constructor
  · intro h hany
    rw [List.any_eq_true] at hany
    obtain ⟨i, hi, hany⟩ := hany
    rw [List.any_eq_true] at hany
    obtain ⟨j, hj, hij⟩ := hany
    rw [List.mem_range] at hi hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hij
    rw [List.getD_eq_getElem l 0 hi, List.getD_eq_getElem l 0 hj] at hij
    exact h j i hj hi hij.1 hij.2.symm
  · intro h i j hi hj hij heq
    apply h
    rw [List.any_eq_true]
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    rw [List.any_eq_true]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [List.getD_eq_getElem l 0 hi, List.getD_eq_getElem l 0 hj]
    exact ⟨hij, heq.symm⟩

/-- `j < i ∧ sources[i] = sources[j]` with `i = X_ 0`, `j = X_ 1`. -/
def dupSrcTest : Cmd :=
  andM (ltTest (X_ 1) (X_ 0))
    (.seq (elemM SRCS (X_ 0) (G_ 1)) (.seq (elemM SRCS (X_ 1) (G_ 2)) (eqTest (G_ 1) (G_ 2))))

/-- `sources.Nodup`. -/
def nodupSrcM : Cmd := notM (anyRangeM 0 KK (anyRangeM 1 KK dupSrcTest))

theorem dupSrcTest_spec (k : ℕ) (g : GInstance) :
    TestSpec dupSrcTest ([FLAG] ++ ([G_ 1] ++ ([G_ 2] ++ [FLAG]))) 15
      (fun m => (InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK)
      (fun m => decide (m (X_ 1) < m (X_ 0)) &&
        decide (g.base.sources.getD (m (X_ 0)) 0 = g.base.sources.getD (m (X_ 1)) 0)) := by
  have hctx : ∀ m, (InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK → Ctx m :=
    fun m hm => hm.1.1.ctx
  -- the element reads
  have hsrc : ∀ m, (InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK →
      m (m SRCS + 1 + m (X_ 0)) = g.base.sources.getD (m (X_ 0)) 0 ∧
      m (m SRCS + 1 + m (X_ 1)) = g.base.sources.getD (m (X_ 1)) 0 := by
    intro m ⟨⟨hm, h0⟩, h1⟩
    obtain ⟨_, _, harr⟩ := hm.arr_srcs
    rw [hm.kk] at h0 h1
    constructor
    · rw [List.getD_eq_getElem _ _ h0, ← arrAt_getElem m (m SRCS) _ (by rw [harr]; exact h0)]
      exact (List.getElem_of_eq harr _)
    · rw [List.getD_eq_getElem _ _ h1, ← arrAt_getElem m (m SRCS) _ (by rw [harr]; exact h1)]
      exact (List.getElem_of_eq harr _)
  -- stability of the precondition under the writes of the reads
  have hstab : ∀ m m₁, ((InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK) → Agree m m₁ [G_ 1] ∨ Agree m m₁ [G_ 2] →
      (InstCtx k g m₁ ∧ m₁ (X_ 0) < m₁ KK) ∧ m₁ (X_ 1) < m₁ KK := by
    intro m m₁ ⟨⟨hm, h0⟩, h1⟩ hag
    have hhp := hm.ctx.2.2
    rcases hag with hag | hag
    · refine ⟨⟨hm.of_agree hag (fun x hx => by simp at hx; subst hx; exact safeVars_G 1 (by norm_num)), ?_⟩, ?_⟩
      · rw [hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_]), hag.var KK (by addr3) (by addr3) (by simp [G_, KK])]; exact h0
      · rw [hag.var (X_ 1) (by addr3) (by addr3) (by simp [G_, X_]), hag.var KK (by addr3) (by addr3) (by simp [G_, KK])]; exact h1
    · refine ⟨⟨hm.of_agree hag (fun x hx => by simp at hx; subst hx; exact safeVars_G 2 (by norm_num)), ?_⟩, ?_⟩
      · rw [hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_]), hag.var KK (by addr3) (by addr3) (by simp [G_, KK])]; exact h0
      · rw [hag.var (X_ 1) (by addr3) (by addr3) (by simp [G_, X_]), hag.var KK (by addr3) (by addr3) (by simp [G_, KK])]; exact h1
  have e1 := elemM_spec SRCS (X_ 0) (G_ 1) (by constructor <;> addr3) (by addr3) (by addr3)
    (fun m => (InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK) hctx (fun m hm => hm.1.1.arr_srcs.1)
  have e2 := elemM_spec SRCS (X_ 1) (G_ 2) (by constructor <;> addr3) (by addr3) (by addr3)
    (fun m => ((InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK) ∧ m (G_ 1) = g.base.sources.getD (m (X_ 0)) 0)
    (fun m hm => hm.1.1.1.ctx) (fun m hm => hm.1.1.1.arr_srcs.1)
  -- second read then compare
  have t2 := TestSpec.after e2 (eqTest_spec (G_ 1) (G_ 2)
      (fun m => (((InstCtx k g m ∧ m (X_ 0) < m KK) ∧ m (X_ 1) < m KK) ∧ m (G_ 1) = g.base.sources.getD (m (X_ 0)) 0) ∧
        m (G_ 2) = g.base.sources.getD (m (X_ 1)) 0))
    (Q := fun m => decide (g.base.sources.getD (m (X_ 0)) 0 = g.base.sources.getD (m (X_ 1)) 0))
    (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
  · have t1 := TestSpec.after e1 t2 (Q := fun m => decide (g.base.sources.getD (m (X_ 0)) 0 = g.base.sources.getD (m (X_ 1)) 0))
      (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
    · have ha := andM_spec (ltTest_spec (X_ 1) (X_ 0) _) t1 (by intro x hx; simp at hx; subst hx; addr3) hctx
        ?_ ?_
      · unfold dupSrcTest
        exact ha.mono (fun x hx => hx) (by omega) (fun m hm => hm)
      · intro m m' hm hag
        have hm' : InstCtx k g m' := hm.1.1.of_agree hag (fun x hx => by simp at hx; subst hx; exact safeVars_FLAG)
        have hhp := hm.1.1.ctx.2.2
        refine ⟨⟨hm', ?_⟩, ?_⟩
        · rw [hag.var (X_ 0) (by addr3) (by addr3) (by simp [FLAG, X_]), hag.var KK (by addr3) (by addr3) (by simp [FLAG, KK])]; exact hm.1.2
        · rw [hag.var (X_ 1) (by addr3) (by addr3) (by simp [FLAG, X_]), hag.var KK (by addr3) (by addr3) (by simp [FLAG, KK])]; exact hm.2
      · intro m m' hm hag
        have hhp := hm.1.1.ctx.2.2
        simp only [hag.var (X_ 0) (by addr3) (by addr3) (by simp [FLAG, X_]),
          hag.var (X_ 1) (by addr3) (by addr3) (by simp [FLAG, X_])]
    · -- the context after the first read
      have hpre := hstab m m₁ hm (Or.inl hag)
      have hhp := hm.1.1.ctx.2.2
      exact ⟨hpre, by rw [hp.1, (hsrc m hm).1, hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_])]⟩
    · have hhp := hm.1.1.ctx.2.2
      simp only [hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_]),
        hag.var (X_ 1) (by addr3) (by addr3) (by simp [G_, X_])]
  · -- the context after the second read
    obtain ⟨hpre, hG⟩ := hm
    have hpre' := hstab m m₁ hpre (Or.inr hag)
    have hhp := hpre.1.1.ctx.2.2
    refine ⟨⟨hpre', ?_⟩, ?_⟩
    · rw [hag.var (G_ 1) (by addr3) (by addr3) (by simp [G_]), hG,
        hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_])]
    · rw [hp.1, (hsrc m hpre).2, hag.var (X_ 1) (by addr3) (by addr3) (by simp [G_, X_])]
  · obtain ⟨hpre, hG⟩ := hm
    have hhp := hpre.1.1.ctx.2.2
    simp only [hag.var (G_ 1) (by addr3) (by addr3) (by simp [G_]), hG, hp.1, (hsrc m hpre).2]


/-- The variables of `dupSrcTest`. -/
def dupV : List ℕ := [FLAG] ++ ([G_ 1] ++ ([G_ 2] ++ [FLAG]))

theorem dupV_safe : SafeVars dupV := safeVars_of_decide _ (by decide)

/-- Stability of `InstCtx k g m ∧ m X < m N` (`N` a global) under safe variables not
containing `X`. -/
theorem instX_stable (k : ℕ) (g : GInstance) (X N : ℕ) (hX : X < IN) (hXH : X ≠ HP)
    (hN : N ∈ instVars) {V : List ℕ} (hV : SafeVars V) (hXV : X ∉ V) :
    StableP (fun m => InstCtx k g m ∧ m X < m N) V := by
  intro m m' ⟨hm, hx⟩ hag
  have hhp := hm.ctx.2.2
  have hNlt : N < IN ∧ N ≠ HP := by
    simp only [instVars, List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> addr3
  refine ⟨hm.of_agree hag hV, ?_⟩
  rw [hag.var X (by omega) hXH hXV, hag.var N (by omega) hNlt.2 (fun h => (hV N h).2.2 hN)]
  exact hx

theorem nodupSrcM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec nodupSrcM
      (FLAG :: (rangeV 0 ++ FLAG :: (rangeV 1 ++ FLAG :: dupV)))
      (n * ((n * (15 + 11) + n * 6 + 20) + 11) + n * 6 + 20 + 1) (InstCtx k g)
      (fun _ => decide g.base.sources.Nodup) := by
  have hkk : ∀ m, InstCtx k g m → m KK ≤ n := fun m hm => by rw [hm.kk]; exact hn.srcs
  -- the inner scan (level 1): some j < i with equal entries
  have inner := anyRangeM_spec 1 KK n (by norm_num) (dupSrcTest_spec k g)
    (fun x hx => ⟨(dupV_safe x hx).1, (dupV_safe x hx).2.1⟩)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m hm => hm.1.ctx) (fun m hm => hkk m hm.1)
    (instX_stable k g (X_ 0) KK (by addr3) (by addr3) (by decide) (SafeVars.append (safeVars_rangeV 1 (by norm_num))
      (SafeVars.cons safeVars_FLAG dupV_safe)) (by decide))
    (by
      intro m m' hm hag
      have hhp := hm.1.1.ctx.2.2
      dsimp only
      simp only [hag.var (X_ 0) (by addr3) (by addr3) (by decide), hag.var (X_ 1) (by addr3) (by addr3) (by decide)])
  -- the outer scan (level 0)
  have hsafe1 : SafeVars (rangeV 1 ++ FLAG :: dupV) :=
    SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupV_safe)
  have outer := anyRangeM_spec 0 KK n (by norm_num) inner
    (fun x hx => ⟨(hsafe1 x hx).1, (hsafe1 x hx).2.1⟩)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m hm => hm.ctx) hkk
    (InstCtx.stableP (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupV_safe)))))
    (by
      intro m m' hm hag
      have hhp := hm.1.ctx.2.2
      have hK : m' KK = m KK := hag.var KK (by addr3) (by addr3) (by decide)
      have hX0 : m' (X_ 0) = m (X_ 0) := hag.var (X_ 0) (by addr3) (by addr3) (by decide)
      dsimp only
      rw [hK]
      apply any_congr_mem
      intro j hj
      simp only [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide), hX0])
  have hnot := notM_spec outer (by
    intro x hx
    exact (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupV_safe))) x hx).1)
    (fun m hm => hm.ctx)
  unfold nodupSrcM
  refine hnot.congr (fun m hm => ?_)
  rw [nodup_eq_scan]
  congr 1
  rw [hm.kk]
  apply any_congr_mem
  intro i hi
  simp only [Mem.write_same, Mem.write_ne _ _ (show KK ≠ X_ 0 by decide), hm.kk]
  apply any_congr_mem
  intro j hj
  simp only [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide)]


/-! ### Duplicate symbols (by their first component) -/

/-- `j < i ∧ symbols[i].1 = symbols[j].1` with `i = X_ 0`, `j = X_ 1`. -/
def dupSymTest : Cmd :=
  andM (ltTest (X_ 1) (X_ 0))
    (.seq (elemM SYMS (X_ 0) (G_ 1)) (.seq (load (G_ 1) (G_ 1))
      (.seq (elemM SYMS (X_ 1) (G_ 2)) (.seq (load (G_ 2) (G_ 2)) (eqTest (G_ 1) (G_ 2))))))

/-- `(symbols.map Prod.fst).Nodup`. -/
def nodupSymM : Cmd := notM (anyRangeM 0 MM (anyRangeM 1 MM dupSymTest))

theorem InstCtx.sym_fst {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) (i : ℕ)
    (hi : i < g.base.symbols.length) :
    m (m (m SYMS + 1 + i)) = (g.base.symbols.map Prod.fst).getD i 0 := by
  obtain ⟨_, _, _, h4⟩ := hm.arr_syms
  rw [(h4 i hi).2.2.1, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map]

theorem dupSymTest_spec (k : ℕ) (g : GInstance) :
    TestSpec dupSymTest ([FLAG] ++ ([G_ 1] ++ ([G_ 1] ++ ([G_ 2] ++ ([G_ 2] ++ [FLAG]))))) 17
      (fun m => (InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM)
      (fun m => decide (m (X_ 1) < m (X_ 0)) &&
        decide ((g.base.symbols.map Prod.fst).getD (m (X_ 0)) 0 = (g.base.symbols.map Prod.fst).getD (m (X_ 1)) 0)) := by
  have hctx : ∀ m, (InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM → Ctx m :=
    fun m hm => hm.1.1.ctx
  -- stability of the precondition under the writes to `G_ 1`, `G_ 2`
  have hstab : ∀ m m₁, ((InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) → (Agree m m₁ [G_ 1] ∨ Agree m m₁ [G_ 2]) →
      (InstCtx k g m₁ ∧ m₁ (X_ 0) < m₁ MM) ∧ m₁ (X_ 1) < m₁ MM := by
    intro m m₁ ⟨⟨hm, h0⟩, h1⟩ hag
    have hhp := hm.ctx.2.2
    rcases hag with hag | hag
    · refine ⟨⟨hm.of_agree hag (fun x hx => by simp at hx; subst hx; exact safeVars_G 1 (by norm_num)), ?_⟩, ?_⟩
      · rw [hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_]), hag.var MM (by addr3) (by addr3) (by simp [G_, MM])]; exact h0
      · rw [hag.var (X_ 1) (by addr3) (by addr3) (by simp [G_, X_]), hag.var MM (by addr3) (by addr3) (by simp [G_, MM])]; exact h1
    · refine ⟨⟨hm.of_agree hag (fun x hx => by simp at hx; subst hx; exact safeVars_G 2 (by norm_num)), ?_⟩, ?_⟩
      · rw [hag.var (X_ 0) (by addr3) (by addr3) (by simp [G_, X_]), hag.var MM (by addr3) (by addr3) (by simp [G_, MM])]; exact h0
      · rw [hag.var (X_ 1) (by addr3) (by addr3) (by simp [G_, X_]), hag.var MM (by addr3) (by addr3) (by simp [G_, MM])]; exact h1
  -- record pointers and their first components
  have hptr : ∀ m, (InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM →
      (IN ≤ m (m SYMS + 1 + m (X_ 0)) ∧ m (m (m SYMS + 1 + m (X_ 0))) = (g.base.symbols.map Prod.fst).getD (m (X_ 0)) 0) ∧
      (IN ≤ m (m SYMS + 1 + m (X_ 1)) ∧ m (m (m SYMS + 1 + m (X_ 1))) = (g.base.symbols.map Prod.fst).getD (m (X_ 1)) 0) := by
    intro m ⟨⟨hm, h0⟩, h1⟩
    rw [hm.mm] at h0 h1
    obtain ⟨_, _, _, h4⟩ := hm.arr_syms
    exact ⟨⟨(h4 _ h0).1, hm.sym_fst _ h0⟩, ⟨(h4 _ h1).1, hm.sym_fst _ h1⟩⟩
  -- the reads
  have e1 := elemM_spec SYMS (X_ 0) (G_ 1) (by constructor <;> addr3) (by addr3) (by addr3)
    (fun m => (InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) hctx (fun m hm => hm.1.1.arr_syms.1)
  have e1' := loadM_spec (G_ 1) (G_ 1) (by constructor <;> addr3)
    (fun m => ((InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) ∧ m (G_ 1) = m (m SYMS + 1 + m (X_ 0)))
  have e2 := elemM_spec SYMS (X_ 1) (G_ 2) (by constructor <;> addr3) (by addr3) (by addr3)
    (fun m => ((InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) ∧ m (G_ 1) = (g.base.symbols.map Prod.fst).getD (m (X_ 0)) 0)
    (fun m hm => hm.1.1.1.ctx) (fun m hm => hm.1.1.1.arr_syms.1)
  have e2' := loadM_spec (G_ 2) (G_ 2) (by constructor <;> addr3)
    (fun m => (((InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) ∧ m (G_ 1) = (g.base.symbols.map Prod.fst).getD (m (X_ 0)) 0) ∧
      m (G_ 2) = m (m SYMS + 1 + m (X_ 1)))
  let Q : Mem → Bool := fun m => decide ((g.base.symbols.map Prod.fst).getD (m (X_ 0)) 0 = (g.base.symbols.map Prod.fst).getD (m (X_ 1)) 0)
  have hX : ∀ (m m₁ : Mem) (D : ℕ), D = G_ 1 ∨ D = G_ 2 → Agree m m₁ [D] → Ctx m →
      m₁ (X_ 0) = m (X_ 0) ∧ m₁ (X_ 1) = m (X_ 1) ∧ m₁ SYMS = m SYMS := by
    intro m m₁ D hD hag hc
    have hhp := hc.2.2
    rcases hD with rfl | rfl <;>
      exact ⟨hag.var _ (by addr3) (by addr3) (by simp [G_, X_]), hag.var _ (by addr3) (by addr3) (by simp [G_, X_]),
        hag.var _ (by addr3) (by addr3) (by simp [G_, SYMS])⟩
  have hcell : ∀ m m₁ D, (D = G_ 1 ∨ D = G_ 2) → Agree m m₁ [D] →
      ((InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) →
      m₁ (m SYMS + 1 + m (X_ 0)) = m (m SYMS + 1 + m (X_ 0)) ∧
      m₁ (m SYMS + 1 + m (X_ 1)) = m (m SYMS + 1 + m (X_ 1)) ∧
      m₁ (m (m SYMS + 1 + m (X_ 1))) = m (m (m SYMS + 1 + m (X_ 1))) := by
    intro m m₁ D hD hag hpre
    obtain ⟨⟨hm, h0⟩, h1⟩ := hpre
    obtain ⟨hs1, hs2, hs3, hs4⟩ := hm.arr_syms
    rw [hm.mm] at h0 h1
    rw [arrAt_length] at hs3
    have hV : ∀ x, x ∈ [D] → x < IN := by
      intro x hx; simp at hx; subst hx; rcases hD with rfl | rfl <;> addr3
    refine ⟨hag.heap hV _ (by omega) (by omega), hag.heap hV _ (by omega) (by omega), ?_⟩
    obtain ⟨q1, q2, _, _⟩ := hs4 _ h1
    exact hag.heap hV _ q1 (by omega)
  -- assemble the second half: read, deref, read, deref, compare
  have t4 := TestSpec.after e2' (eqTest_spec (G_ 1) (G_ 2)
      (fun m => (((InstCtx k g m ∧ m (X_ 0) < m MM) ∧ m (X_ 1) < m MM) ∧ m (G_ 1) = (g.base.symbols.map Prod.fst).getD (m (X_ 0)) 0) ∧
        m (G_ 2) = (g.base.symbols.map Prod.fst).getD (m (X_ 1)) 0))
    (Q := Q) (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
  · have t3 := TestSpec.after e2 t4 (Q := Q) (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
    · have t2 := TestSpec.after e1' t3 (Q := Q) (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
      · have t1 := TestSpec.after e1 t2 (Q := Q) (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
        · have ha := andM_spec (ltTest_spec (X_ 1) (X_ 0) _) t1 (by intro x hx; simp at hx; subst hx; addr3) hctx
            ?_ ?_
          · unfold dupSymTest
            exact ha.mono (fun x hx => hx) (by omega) (fun m hm => hm)
          · intro m m' hm hag
            have hm' : InstCtx k g m' := hm.1.1.of_agree hag (fun x hx => by simp at hx; subst hx; exact safeVars_FLAG)
            have hhp := hm.1.1.ctx.2.2
            refine ⟨⟨hm', ?_⟩, ?_⟩
            · rw [hag.var (X_ 0) (by addr3) (by addr3) (by simp [FLAG, X_]), hag.var MM (by addr3) (by addr3) (by simp [FLAG, MM])]; exact hm.1.2
            · rw [hag.var (X_ 1) (by addr3) (by addr3) (by simp [FLAG, X_]), hag.var MM (by addr3) (by addr3) (by simp [FLAG, MM])]; exact hm.2
          · intro m m' hm hag
            have hhp := hm.1.1.ctx.2.2
            simp only [Q, hag.var (X_ 0) (by addr3) (by addr3) (by simp [FLAG, X_]),
              hag.var (X_ 1) (by addr3) (by addr3) (by simp [FLAG, X_])]
        · obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 1) (Or.inl rfl) hag (hctx m hm)
          exact ⟨hstab m m₁ hm (Or.inl hag), by
            rw [hp.1, hx0, hs]; exact (hcell m m₁ (G_ 1) (Or.inl rfl) hag hm).1.symm⟩
        · obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 1) (Or.inl rfl) hag (hctx m hm)
          simp only [Q, hx0, hx1]
      · obtain ⟨hpre, hG⟩ := hm
        obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 1) (Or.inl rfl) hag (hctx m hpre)
        refine ⟨hstab m m₁ hpre (Or.inl hag), ?_⟩
        rw [hp.1, hG, (hptr m hpre).1.2, hx0]
      · obtain ⟨hpre, hG⟩ := hm
        obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 1) (Or.inl rfl) hag (hctx m hpre)
        simp only [Q, hx0, hx1]
    · obtain ⟨hpre, hG⟩ := hm
      obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 2) (Or.inr rfl) hag (hctx m hpre)
      have hhp := (hctx m hpre).2.2
      refine ⟨⟨hstab m m₁ hpre (Or.inr hag), ?_⟩, ?_⟩
      · rw [hag.var (G_ 1) (by addr3) (by addr3) (by simp [G_]), hG, hx0]
      · rw [hp.1, hx1, hs]
        exact (hcell m m₁ (G_ 2) (Or.inr rfl) hag hpre).2.1.symm
    · obtain ⟨hpre, hG⟩ := hm
      obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 2) (Or.inr rfl) hag (hctx m hpre)
      simp only [Q, hx0, hx1]
  · obtain ⟨⟨hpre, hG1⟩, hG2⟩ := hm
    obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 2) (Or.inr rfl) hag (hctx m hpre)
    have hhp := (hctx m hpre).2.2
    refine ⟨⟨hstab m m₁ hpre (Or.inr hag), ?_⟩, ?_⟩
    · rw [hag.var (G_ 1) (by addr3) (by addr3) (by simp [G_]), hG1, hx0]
    · rw [hp.1, hG2, (hptr m hpre).2.2, hx1]
  · obtain ⟨⟨hpre, hG1⟩, hG2⟩ := hm
    obtain ⟨hx0, hx1, hs⟩ := hX m m₁ (G_ 2) (Or.inr rfl) hag (hctx m hpre)
    have hhp := (hctx m hpre).2.2
    simp only [Q, hag.var (G_ 1) (by addr3) (by addr3) (by simp [G_]), hG1, hp.1, hG2, (hptr m hpre).2.2, hx0, hx1]

/-- The variables of `dupSymTest`. -/
def dupSymV : List ℕ := [FLAG] ++ ([G_ 1] ++ ([G_ 1] ++ ([G_ 2] ++ ([G_ 2] ++ [FLAG]))))

theorem dupSymV_safe : SafeVars dupSymV := safeVars_of_decide _ (by decide)

theorem nodupSymM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec nodupSymM
      (FLAG :: (rangeV 0 ++ FLAG :: (rangeV 1 ++ FLAG :: dupSymV)))
      (n * ((n * (17 + 11) + n * 6 + 20) + 11) + n * 6 + 20 + 1) (InstCtx k g)
      (fun _ => decide (g.base.symbols.map Prod.fst).Nodup) := by
  have hmm : ∀ m, InstCtx k g m → m MM ≤ n := fun m hm => by rw [hm.mm]; exact hn.syms
  -- the inner scan (level 1): some j < i with equal entries
  have inner := anyRangeM_spec 1 MM n (by norm_num) (dupSymTest_spec k g)
    (fun x hx => ⟨(dupSymV_safe x hx).1, (dupSymV_safe x hx).2.1⟩)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m hm => hm.1.ctx) (fun m hm => hmm m hm.1)
    (instX_stable k g (X_ 0) MM (by addr3) (by addr3) (by decide) (SafeVars.append (safeVars_rangeV 1 (by norm_num))
      (SafeVars.cons safeVars_FLAG dupSymV_safe)) (by decide))
    (by
      intro m m' hm hag
      have hhp := hm.1.1.ctx.2.2
      dsimp only
      simp only [hag.var (X_ 0) (by addr3) (by addr3) (by decide), hag.var (X_ 1) (by addr3) (by addr3) (by decide)])
  -- the outer scan (level 0)
  have hsafe1 : SafeVars (rangeV 1 ++ FLAG :: dupSymV) :=
    SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupSymV_safe)
  have outer := anyRangeM_spec 0 MM n (by norm_num) inner
    (fun x hx => ⟨(hsafe1 x hx).1, (hsafe1 x hx).2.1⟩)
    (by constructor <;> addr3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (fun m hm => hm.ctx) hmm
    (InstCtx.stableP (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupSymV_safe)))))
    (by
      intro m m' hm hag
      have hhp := hm.1.ctx.2.2
      have hK : m' MM = m MM := hag.var MM (by addr3) (by addr3) (by decide)
      have hX0 : m' (X_ 0) = m (X_ 0) := hag.var (X_ 0) (by addr3) (by addr3) (by decide)
      dsimp only
      rw [hK]
      apply any_congr_mem
      intro j hj
      simp only [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide), hX0])
  have hnot := notM_spec outer (by
    intro x hx
    exact (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupSymV_safe))) x hx).1)
    (fun m hm => hm.ctx)
  unfold nodupSymM
  refine hnot.congr (fun m hm => ?_)
  rw [nodup_eq_scan, List.length_map]
  congr 1
  rw [hm.mm]
  apply any_congr_mem
  intro i hi
  simp only [Mem.write_same, Mem.write_ne _ _ (show MM ≠ X_ 0 by decide), hm.mm]
  apply any_congr_mem
  intro j hj
  simp only [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide)]




/-! ### The tests on `tests` and `outs` -/

theorem InstCtx.pairs_tests {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) :
    pairsAt m (m TESTS) = g.base.tests := by
  obtain ⟨h1, h2, h3, h4⟩ := hm.arr_tests
  unfold pairsAt
  apply List.ext_getElem (by rw [List.length_map]; exact h3)
  intro i hi hi'
  rw [List.getElem_map, arrAt_getElem]
  obtain ⟨_, _, g3, g4⟩ := h4 i hi'
  rw [g3, g4]

theorem InstCtx.tests_wf {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) :
    IN ≤ m TESTS ∧ m TESTS + 1 + m (m TESTS) ≤ m HP ∧ RecsIn m (m TESTS) IN (m HP) := by
  obtain ⟨h1, h2, h3, h4⟩ := hm.arr_tests
  refine ⟨h1, h2, fun q hq => ?_⟩
  rw [List.mem_iff_getElem] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  rw [arrAt_getElem]
  rw [h3] at hi
  exact ⟨(h4 i hi).1, (h4 i hi).2.1⟩

/-- Membership of a pointer in the tests array gives its record. -/
theorem InstCtx.test_rec {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) (q : ℕ)
    (hq : q ∈ arrAt m (m TESTS)) : IN ≤ q ∧ q + 2 ≤ m HP ∧ (m q, m (q + 1)) ∈ g.base.tests := by
  obtain ⟨_, _, hrec⟩ := hm.tests_wf
  refine ⟨(hrec q hq).1, (hrec q hq).2, ?_⟩
  rw [← hm.pairs_tests]
  unfold pairsAt
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- `i < |nodes| ∧ j < |nodes|` for the test record at `X_ 0`. -/
def testBoundsTest : Cmd :=
  .seq (load (G_ 1) (X_ 0)) (.seq (field1M (X_ 0) (G_ 2)) (andM (ltTest (G_ 1) NN) (ltTest (G_ 2) NN)))

/-- `tests.all (fun ij => ij.1 < |nodes| ∧ ij.2 < |nodes|)`. -/
def testsBoundsM : Cmd := allM 0 TESTS testBoundsTest

theorem testBoundsTest_spec (k : ℕ) (g : GInstance) :
    TestSpec testBoundsTest ([G_ 1] ++ ([G_ 2] ++ ([FLAG] ++ [FLAG]))) 12
      (fun m => InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS))
      (fun m => decide (m (m (X_ 0)) < g.base.nodes.length) && decide (m (m (X_ 0) + 1) < g.base.nodes.length)) := by
  have hq : ∀ m, InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS) → IN ≤ m (X_ 0) ∧ m (X_ 0) + 2 ≤ m HP :=
    fun m hm => ⟨(hm.1.test_rec _ hm.2).1, (hm.1.test_rec _ hm.2).2.1⟩
  -- stability of the precondition and of the relevant cells under one safe write
  have hstab : ∀ m m₁ D, (D = G_ 1 ∨ D = G_ 2 ∨ D = FLAG) → Agree m m₁ [D] →
      InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS) →
      (InstCtx k g m₁ ∧ m₁ (X_ 0) ∈ arrAt m₁ (m₁ TESTS)) ∧ m₁ (X_ 0) = m (X_ 0) ∧ m₁ (m (X_ 0)) = m (m (X_ 0)) ∧
        m₁ (m (X_ 0) + 1) = m (m (X_ 0) + 1) ∧ m₁ NN = m NN := by
    intro m m₁ D hD hag ⟨hm, hx⟩
    have hhp := hm.ctx.2.2
    have hsafe : SafeVars [D] := by
      intro x hx; simp at hx; subst hx; rcases hD with rfl | rfl | rfl
      · exact safeVars_G 1 (by norm_num)
      · exact safeVars_G 2 (by norm_num)
      · exact safeVars_FLAG
    have hV : ∀ x, x ∈ [D] → x < IN := fun x hx => (hsafe x hx).2.1
    have hX : m₁ (X_ 0) = m (X_ 0) := hag.var (X_ 0) (by addr3) (by addr3) (by
      intro h; simp at h; rcases hD with rfl | rfl | rfl <;> simp [G_, X_, FLAG] at h)
    have hT : m₁ TESTS = m TESTS := hag.var TESTS (by addr3) (by addr3) (fun h => (hsafe TESTS h).2.2 (by decide))
    obtain ⟨hq1, hq2⟩ := hq m ⟨hm, hx⟩
    obtain ⟨ht1, ht2, _⟩ := hm.tests_wf
    refine ⟨⟨hm.of_agree hag hsafe, ?_⟩, hX, hag.heap hV _ hq1 (by omega), hag.heap hV _ (by omega) (by omega),
      hag.var NN (by addr3) (by addr3) (fun h => (hsafe NN h).2.2 (by decide))⟩
    rw [hX, hT, hag.arrAt hV _ ht1 ht2]; exact hx
  have e1 := loadM_spec (X_ 0) (G_ 1) (by constructor <;> addr3)
    (fun m => InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS))
  have e2 := field1M_spec (X_ 0) (G_ 2) (by constructor <;> addr3) (by addr3)
    (fun m => (InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)) ∧ m (G_ 1) = m (m (X_ 0)))
    (fun m hm => hm.1.1.ctx) (fun m hm => (hq m hm.1).1)
  let Pre2 : Mem → Prop := fun m => ((InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)) ∧ m (G_ 1) = m (m (X_ 0))) ∧
    m (G_ 2) = m (m (X_ 0) + 1)
  have ta := andM_spec (ltTest_spec (G_ 1) NN Pre2) (ltTest_spec (G_ 2) NN Pre2)
    (by intro x hx; simp at hx; subst hx; addr3) (fun m hm => hm.1.1.1.ctx)
    (by
      intro m m' hm hag
      obtain ⟨⟨hpre, hG1⟩, hG2⟩ := hm
      obtain ⟨hpre', hX, hc0, hc1, _⟩ := hstab m m' FLAG (Or.inr (Or.inr rfl)) hag hpre
      have hhp := hpre.1.ctx.2.2
      refine ⟨⟨hpre', ?_⟩, ?_⟩
      · rw [hag.var (G_ 1) (by addr3) (by addr3) (by decide), hG1, hX, hc0]
      · rw [hag.var (G_ 2) (by addr3) (by addr3) (by decide), hG2, hX, hc1])
    (by
      intro m m' hm hag
      have hhp := hm.1.1.1.ctx.2.2
      dsimp only
      rw [hag.var (G_ 2) (by addr3) (by addr3) (by decide), hag.var NN (by addr3) (by addr3) (by decide)])
  have t2 := TestSpec.after e2 ta (Q := fun m => decide (m (m (X_ 0)) < g.base.nodes.length) &&
      decide (m (m (X_ 0) + 1) < g.base.nodes.length))
    (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
  · have t1 := TestSpec.after e1 t2 (Q := fun m => decide (m (m (X_ 0)) < g.base.nodes.length) &&
        decide (m (m (X_ 0) + 1) < g.base.nodes.length))
      (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
    · unfold testBoundsTest
      exact t1.mono (fun x hx => hx) (by omega) (fun m hm => hm)
    · obtain ⟨hpre', hX, hc0, hc1, _⟩ := hstab m m₁ (G_ 1) (Or.inl rfl) hag hm
      exact ⟨hpre', by rw [hp.1, hX, hc0]⟩
    · obtain ⟨hpre', hX, hc0, hc1, _⟩ := hstab m m₁ (G_ 1) (Or.inl rfl) hag hm
      simp only [hX, hc0, hc1]
  · obtain ⟨hpre, hG1⟩ := hm
    obtain ⟨hpre', hX, hc0, hc1, _⟩ := hstab m m₁ (G_ 2) (Or.inr (Or.inl rfl)) hag hpre
    have hhp := hpre.1.ctx.2.2
    refine ⟨⟨hpre', ?_⟩, by rw [hp.1, hX, hc1]⟩
    rw [hag.var (G_ 1) (by addr3) (by addr3) (by decide), hG1, hX, hc0]
  · obtain ⟨hpre, hG1⟩ := hm
    obtain ⟨hpre', hX, hc0, hc1, hN⟩ := hstab m m₁ (G_ 2) (Or.inr (Or.inl rfl)) hag hpre
    have hhp := hpre.1.ctx.2.2
    dsimp only
    rw [hag.var (G_ 1) (by addr3) (by addr3) (by decide), hG1, hp.1, hN, hpre.1.nn]

/-- The variables of `testBoundsTest`. -/
def tbV : List ℕ := [G_ 1] ++ ([G_ 2] ++ ([FLAG] ++ [FLAG]))

theorem tbV_safe : SafeVars tbV := safeVars_of_decide _ (by decide)

theorem all_congr_mem {l : List ℕ} {p q : ℕ → Bool} (h : ∀ x, x ∈ l → p x = q x) :
    l.all p = l.all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro hp x hx; rw [← h x hx]; exact hp x hx
  · intro hq x hx; rw [h x hx]; exact hq x hx

theorem testsBoundsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec testsBoundsM (FLAG :: (Lvars 0 ++ FLAG :: (FLAG :: tbV))) (n * (12 + 12) + 11) (InstCtx k g)
      (fun _ => g.base.tests.all (fun ij => decide (ij.1 < g.base.nodes.length) && decide (ij.2 < g.base.nodes.length))) := by
  have hall := allM_spec 0 TESTS n (testBoundsTest_spec k g) (by norm_num)
    (fun x hx => ⟨(tbV_safe x hx).1, (tbV_safe x hx).2.1⟩) (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (fun m hm => hm.ctx)
    (fun m hm => ⟨hm.tests_wf.1, hm.tests_wf.2.1, by
      have := hm.arr_tests.2.2.1; rw [arrAt_length] at this; rw [this]; exact hn.tests⟩)
    (InstCtx.stableP (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG tbV_safe)))
    (by
      intro m m' hm hx hag
      have hhp := hm.ctx.2.2
      have hV : ∀ x, x ∈ LvarsX 0 ++ FLAG :: tbV → x < IN := fun x hx =>
        (SafeVars.append (safeVars_LvarsX 0 (by norm_num)) (SafeVars.cons safeVars_FLAG tbV_safe) x hx).2.1
      obtain ⟨hq1, hq2, _⟩ := hm.test_rec _ hx
      dsimp only
      rw [hag.var (X_ 0) (by addr3) (by addr3) (by decide), hag.heap hV _ hq1 (by omega),
        hag.heap hV _ (by omega) (by omega)])
  unfold testsBoundsM
  refine hall.congr (fun m hm => ?_)
  dsimp only
  rw [← hm.pairs_tests]
  unfold pairsAt
  rw [List.all_map]
  apply all_congr_mem
  intro q hq
  simp only [Function.comp, Mem.write_same]
  obtain ⟨_, _, hrec⟩ := hm.tests_wf
  obtain ⟨hq1, hq2⟩ := hrec q hq
  rw [Mem.write_ne _ _ (show q ≠ X_ 0 by addr3), Mem.write_ne _ _ (show q + 1 ≠ X_ 0 by addr3)]


/-! ### `outs.all (· < |nodes|)` -/

/-- `outs.all (fun j => j < |nodes|)`. -/
def outsBoundsM : Cmd := allM 0 OUTS (ltTest (X_ 0) NN)

theorem outsBoundsM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec outsBoundsM (FLAG :: (Lvars 0 ++ FLAG :: (FLAG :: [FLAG]))) (n * (3 + 12) + 11) (InstCtx k g)
      (fun _ => g.outs.all (fun j => decide (j < g.base.nodes.length))) := by
  have hall := allM_spec 0 OUTS n (ltTest_spec (X_ 0) NN (fun m => InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m OUTS)))
    (by norm_num) (by intro x hx; simp at hx; subst hx; constructor <;> addr3) (by constructor <;> addr3)
    (by decide) (by decide) (by decide) (by decide) (fun m hm => hm.ctx)
    (fun m hm => ⟨hm.arr_outs.1, hm.arr_outs.2.1, by
      have := congrArg List.length hm.arr_outs.2.2; rw [arrAt_length] at this; rw [this]; exact hn.outs⟩)
    (InstCtx.stableP (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
      (SafeVars.cons safeVars_FLAG (fun x hx => by simp at hx)))))
    (by
      intro m m' hm hx hag
      have hhp := hm.ctx.2.2
      dsimp only
      rw [hag.var (X_ 0) (by addr3) (by addr3) (by decide), hag.var NN (by addr3) (by addr3) (by decide)])
  unfold outsBoundsM
  refine hall.congr (fun m hm => ?_)
  dsimp only
  rw [hm.arr_outs.2.2]
  simp only [Mem.write_same, Mem.write_ne _ _ (show NN ≠ X_ 0 by decide), hm.nn]

/-! ### Conditionals whose branches know the outcome of the test -/

theorem TestSpec.ite' {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {P₁ P₂ : Mem → Bool} (a b : ℕ) (h₁ : TestSpec t₁ V₁ B₁ (fun m => Pre m ∧ m a = m b) P₁)
    (h₂ : TestSpec t₂ V₂ B₂ (fun m => Pre m ∧ m a ≠ m b) P₂) :
    TestSpec (.ite (.eq a b) t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 2) Pre
      (fun m => if m a = m b then P₁ m else P₂ m) := by
  intro m hm
  dsimp only
  by_cases h : m a = m b
  · have hc : (Cond.eq a b).eval m = true := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₁ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_true hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_left _ hx),
      by rw [hfl, if_pos h]⟩
  · have hc : (Cond.eq a b).eval m = false := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₂ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_false hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_right _ hx),
      by rw [hfl, if_neg h]⟩

theorem TestSpec.iteLt' {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {Pre : Mem → Prop}
    {P₁ P₂ : Mem → Bool} (a b : ℕ) (h₁ : TestSpec t₁ V₁ B₁ (fun m => Pre m ∧ m a < m b) P₁)
    (h₂ : TestSpec t₂ V₂ B₂ (fun m => Pre m ∧ ¬ m a < m b) P₂) :
    TestSpec (.ite (.lt a b) t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 2) Pre
      (fun m => if m a < m b then P₁ m else P₂ m) := by
  intro m hm
  dsimp only
  by_cases h : m a < m b
  · have hc : (Cond.lt a b).eval m = true := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₁ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_true hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_left _ hx),
      by rw [hfl, if_pos h]⟩
  · have hc : (Cond.lt a b).eval m = false := by simp [Cond.eval, h]
    obtain ⟨m₁, k₁, e₁, hk₁, ag₁, hfl⟩ := h₂ m ⟨hm, h⟩
    exact ⟨m₁, _, Cmd.Exec.ite_false hc e₁, by omega, ag₁.mono (fun x hx => List.mem_append_right _ hx),
      by rw [hfl, if_neg h]⟩

/-! ### Node records -/

/-- The node record of index `i < |nodes|`. -/
theorem InstCtx.node_rec {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) (i : ℕ)
    (hi : i < g.base.nodes.length) :
    IN ≤ m NODES + 1 + i ∧ m NODES + 1 + i < m HP ∧ IN ≤ m (m NODES + 1 + i) ∧
      RepNode m IN (m HP) (m (m NODES + 1 + i)) g.base.nodes[i] := by
  obtain ⟨h1, h2, h3, h4⟩ := hm.arr_nodes
  rw [arrAt_length] at h3
  refine ⟨by omega, by omega, (h4 i hi).1, (h4 i hi).2⟩

theorem InstCtx.nn_eq {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) :
    m (m NODES) = g.base.nodes.length := by
  have := hm.arr_nodes.2.2.1; rwa [arrAt_length] at this

/-- The literal test `nd = .src x` in terms of the record cells. -/
theorem repNode_src_iff {m : Mem} {lo hi p : ℕ} {nd : Node} (h : RepNode m lo hi p nd) (x : ℕ) :
    decide (nd = .src x) = (if m p = 0 then decide (m (p + 1) = x) else false) := by
  cases nd with
  | src i =>
    obtain ⟨_, _, h2, h3⟩ := h
    rw [if_pos h2, h3]; simp
  | app f args =>
    obtain ⟨_, _, h2, _⟩ := h
    rw [if_neg (by omega)]; simp

/-- With an index in `I`: is node `M[I]` literally `.src M[XY]`?  Scratch `P` (node pointer) and `T`. -/
def isSrcTest (I XY P T : ℕ) : Cmd :=
  .ite (.lt I NN)
    (.seq (elemM NODES I P) (.seq (load T P)
      (.ite (.eq T ZERO) (.seq (field1M P T) (eqTest T XY)) (setc FLAG 0))))
    (setc FLAG 0)

theorem ne_inst {v x : ℕ} (hv : v ∉ instVars) (hx : x ∈ instVars) : v ≠ x := fun h => hv (h ▸ hx)
theorem ne_inst' {v x : ℕ} (hv : v ∉ instVars) (hx : x ∈ instVars) : x ≠ v := fun h => hv (h ▸ hx)
theorem ne_lo {v c : ℕ} (hv : 5 ≤ v) (hc : c < 5) : c ≠ v := by omega
theorem ne_lo' {v c : ℕ} (hv : 5 ≤ v) (hc : c < 5) : v ≠ c := by omega

theorem lt_hp {m : Mem} {x : ℕ} (hhp : 200 ≤ m HP) (hx : x < 200) : x < m HP := lt_of_lt_of_le hx hhp

theorem repNode_size {m : Mem} {lo hi p : ℕ} {nd : Node} (h : RepNode m lo hi p nd) : p + 2 ≤ hi := by
  cases nd with
  | src i => exact h.2.1
  | app f args => have := h.2.1; omega

theorem isSrcTest_spec (k : ℕ) (g : GInstance) (I XY P T : ℕ)
    (hP : 5 ≤ P ∧ P < IN ∧ P ∉ instVars) (hT : 5 ≤ T ∧ T < IN ∧ T ∉ instVars) (hPT : P ≠ T)
    (hI : 5 ≤ I ∧ I < IN ∧ I ≠ P ∧ I ≠ T ∧ I ≠ FLAG) (hXY : 5 ≤ XY ∧ XY < IN ∧ XY ≠ P ∧ XY ≠ T ∧ XY ≠ FLAG)
    (hPF : P ≠ FLAG) (hTF : T ≠ FLAG) :
    TestSpec (isSrcTest I XY P T) [P, T, FLAG] 15 (InstCtx k g)
      (fun m => decide (g.base.nodes.getD (m I) (.app 0 []) = .src (m XY))) := by
  have hsP : SafeVars [P] := fun x hx => by simp at hx; subst hx; exact hP
  have hsT : SafeVars [T] := fun x hx => by simp at hx; subst hx; exact hT
  have hVP : ∀ x, x ∈ [P] → x < IN := fun x hx => by simp at hx; subst hx; exact hP.2.1
  have hVT : ∀ x, x ∈ [T] → x < IN := fun x hx => by simp at hx; subst hx; exact hT.2.1
  have hIH : I ≠ HP := ne_lo' hI.1 (by decide)
  have hXH : XY ≠ HP := ne_lo' hXY.1 (by decide)
  have hI200 : I < 200 := hI.2.1
  have hXY200 : XY < 200 := hXY.2.1
  have hP200 : P < 200 := hP.2.1
  have hNT : NN ∉ [T] := by simp; exact ne_inst' hT.2.2 (by decide)
  have hNP : NN ∉ [P] := by simp; exact ne_inst' hP.2.2 (by decide)
  have hDT : NODES ∉ [T] := by simp; exact ne_inst' hT.2.2 (by decide)
  have hDP : NODES ∉ [P] := by simp; exact ne_inst' hP.2.2 (by decide)
  have hZT : ZERO ∉ [T] := by simp; exact ne_lo hT.1 (by decide)
  have hIT : I ∉ [T] := by simp; exact hI.2.2.2.1
  have hIP : I ∉ [P] := by simp; exact hI.2.2.1
  have hXT : XY ∉ [T] := by simp; exact hXY.2.2.2.1
  have hXP : XY ∉ [P] := by simp; exact hXY.2.2.1
  have hPT' : P ∉ [T] := by simp; exact hPT
  -- the then-branch after the node pointer and the tag are loaded
  let Pre2 : Mem → Prop := fun m => ((InstCtx k g m ∧ m I < m NN) ∧ m P = m (m NODES + 1 + m I)) ∧
    m T = m (m P)
  have hidx : ∀ m, InstCtx k g m → m I < m NN → m I < g.base.nodes.length := by
    intro m hm h; rw [← hm.nn]; exact h
  have hnode : ∀ m, InstCtx k g m → m I < m NN →
      IN ≤ m NODES + 1 + m I ∧ m NODES + 1 + m I < m HP ∧ IN ≤ m (m NODES + 1 + m I) ∧
        m (m NODES + 1 + m I) + 2 ≤ m HP := by
    intro m hm h
    obtain ⟨h1, h2, h3, h4⟩ := hm.node_rec (m I) (hidx m hm h)
    exact ⟨h1, h2, h3, repNode_size h4⟩
  have hrec : ∀ m, Pre2 m → IN ≤ m P := by
    intro m hm
    obtain ⟨⟨⟨hc, hlt⟩, hp⟩, _⟩ := hm
    rw [hp]; exact (hnode m hc hlt).2.2.1
  have e3 := field1M_spec P T ⟨hT.1, hT.2.1⟩ (Ne.symm hPT) (fun m => Pre2 m ∧ m T = m ZERO)
    (fun m hm => hm.1.1.1.1.ctx) (fun m hm => hrec m hm.1)
  have t3 := TestSpec.after e3 (eqTest_spec T XY (fun m => True))
    (Q := fun m => decide (m (m P + 1) = m XY)) (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      dsimp only
      rw [hp.1, hag.var XY (lt_hp hhp hXY200) hXH hXT])
  have t2 := TestSpec.ite' T ZERO t3 (falseTest_spec (fun m => Pre2 m ∧ m T ≠ m ZERO))
  have e1 := loadM_spec P T ⟨hT.1, hT.2.1⟩ (fun m => (InstCtx k g m ∧ m I < m NN) ∧ m P = m (m NODES + 1 + m I))
  have t1 := TestSpec.after e1 t2 (Q := fun m => if m (m P) = 0 then decide (m (m P + 1) = m XY) else false)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hnode m hm.1.1 hm.1.2
      have hI' : m₁ I = m I := hag.var I (lt_hp hhp hI200) hIH hIT
      have hP' : m₁ P = m P := hag.var P (lt_hp hhp hP200) (ne_lo' hP.1 (by decide)) hPT'
      have hpIN : IN ≤ m P := by rw [hm.2]; exact hq3
      have hpHP : m P + 2 ≤ m HP := by rw [hm.2]; exact hq4
      refine ⟨⟨⟨hm.1.1.of_agree hag hsT, ?_⟩, ?_⟩, ?_⟩
      · rw [hI', hag.var NN (lt_hp hhp (by decide)) (by decide) hNT]; exact hm.1.2
      · rw [hI', hag.var NODES (lt_hp hhp (by decide)) (by decide) hDT, hP', hag.heap hVT (m NODES + 1 + m I) hq1 hq2]
        exact hm.2
      · rw [hp.1, hP', hag.heap hVT (m P) hpIN (by omega)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      have hz := hm.1.1.ctx.2.1
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hnode m hm.1.1 hm.1.2
      have hP' : m₁ P = m P := hag.var P (lt_hp hhp hP200) (ne_lo' hP.1 (by decide)) hPT'
      have hpIN : IN ≤ m P := by rw [hm.2]; exact hq3
      have hpHP : m P + 2 ≤ m HP := by rw [hm.2]; exact hq4
      dsimp only
      rw [hp.1, hag.var ZERO (lt_hp hhp (by decide)) (by decide) hZT, hz, hP',
        hag.heap hVT (m P + 1) (by omega) (by omega),
        hag.var XY (lt_hp hhp hXY200) hXH hXT])
  have e0 := elemM_spec NODES I P ⟨hP.1, hP.2.1⟩ (ne_inst hP.2.2 (by decide)) (Ne.symm hI.2.2.1)
    (fun m => InstCtx k g m ∧ m I < m NN) (fun m hm => hm.1.ctx) (fun m hm => hm.1.arr_nodes.1)
  have t0 := TestSpec.after e0 t1
    (Q := fun m => if m (m (m NODES + 1 + m I)) = 0 then decide (m (m (m NODES + 1 + m I) + 1) = m XY) else false)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hnode m hm.1 hm.2
      have hI' : m₁ I = m I := hag.var I (lt_hp hhp hI200) hIH hIP
      refine ⟨⟨hm.1.of_agree hag hsP, ?_⟩, ?_⟩
      · rw [hI', hag.var NN (lt_hp hhp (by decide)) (by decide) hNP]; exact hm.2
      · rw [hp.1, hI', hag.var NODES (lt_hp hhp (by decide)) (by decide) hDP, hag.heap hVP (m NODES + 1 + m I) hq1 hq2])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hnode m hm.1 hm.2
      have hcell : m₁ (m NODES + 1 + m I) = m (m NODES + 1 + m I) := hag.heap hVP _ hq1 hq2
      dsimp only
      rw [hp.1, hag.heap hVP (m (m NODES + 1 + m I)) hq3 (by omega),
        hag.heap hVP (m (m NODES + 1 + m I) + 1) (by omega) (by omega),
        hag.var XY (lt_hp hhp hXY200) hXH hXP])
  have tt := TestSpec.iteLt' I NN t0 (falseTest_spec (fun m => InstCtx k g m ∧ ¬ m I < m NN))
  unfold isSrcTest
  refine (tt.mono (V' := [P, T, FLAG]) (fun x hx => by simp at hx ⊢; tauto) (by omega) (fun m hm => hm)).congr
    (fun m hm => ?_)
  dsimp only
  by_cases hlt : m I < m NN
  · rw [if_pos hlt]
    have hi : m I < g.base.nodes.length := hidx m hm hlt
    obtain ⟨_, _, _, hq4⟩ := hm.node_rec (m I) hi
    rw [List.getD_eq_getElem _ _ hi, repNode_src_iff hq4]
  · rw [if_neg hlt, List.getD_eq_default _ _ (by rw [← hm.nn]; omega)]
    simp


/-! ### `guardOk` -/

/-- Stability of the test-record precondition under safe writes not touching `X_ 0`. -/
theorem testPre_stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hX : X_ 0 ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)) :
    (InstCtx k g m₁ ∧ m₁ (X_ 0) ∈ arrAt m₁ (m₁ TESTS)) ∧ m₁ (X_ 0) = m (X_ 0) ∧
      m₁ (m (X_ 0)) = m (m (X_ 0)) ∧ m₁ (m (X_ 0) + 1) = m (m (X_ 0) + 1) := by
  obtain ⟨hm, hx⟩ := h
  have hhp : 200 ≤ m HP := hm.ctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2.1
  have hX' : m₁ (X_ 0) = m (X_ 0) := hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) hX
  have hT : m₁ TESTS = m TESTS := hag.var TESTS (lt_hp hhp (by decide)) (by decide)
    (fun h => (hV TESTS h).2.2 (by decide))
  obtain ⟨hq1, hq2, _⟩ := hm.test_rec _ hx
  obtain ⟨ht1, ht2, _⟩ := hm.tests_wf
  refine ⟨⟨hm.of_agree hag hV, ?_⟩, hX', hag.heap hV' _ hq1 (by omega), hag.heap hV' _ (by omega) (by omega)⟩
  rw [hX', hT, hag.arrAt hV' _ ht1 ht2]; exact hx

/-- The guard test for the test record at `X_ 0`: `nodes[i] = .src x ∧ nodes[j] = .src y`. -/
def guardTest : Cmd :=
  .seq (load (G_ 1) (X_ 0)) (.seq (field1M (X_ 0) (G_ 2))
    (andM (isSrcTest (G_ 1) XV (G_ 3) (G_ 4)) (isSrcTest (G_ 2) YV (G_ 3) (G_ 4))))

/-- `tests.any guardTest`. -/
def guardOkM : Cmd := anyM 0 TESTS guardTest

def gtV : List ℕ := [G_ 1] ++ ([G_ 2] ++ ([G_ 3, G_ 4, FLAG] ++ [G_ 3, G_ 4, FLAG]))

theorem gtV_safe : SafeVars gtV := safeVars_of_decide _ (by decide)

theorem guardTest_spec (k : ℕ) (g : GInstance) :
    TestSpec guardTest gtV 36 (fun m => InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS))
      (fun m => decide (g.base.nodes.getD (m (m (X_ 0))) (.app 0 []) = .src g.base.x) &&
        decide (g.base.nodes.getD (m (m (X_ 0) + 1)) (.app 0 []) = .src g.base.y)) := by
  have hq : ∀ m, InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS) → IN ≤ m (X_ 0) ∧ m (X_ 0) + 2 ≤ m HP :=
    fun m hm => ⟨(hm.1.test_rec _ hm.2).1, (hm.1.test_rec _ hm.2).2.1⟩
  have e1 := loadM_spec (X_ 0) (G_ 1) (by constructor <;> addr3)
    (fun m => InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS))
  have e2 := field1M_spec (X_ 0) (G_ 2) (by constructor <;> addr3) (by addr3)
    (fun m => (InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)) ∧ m (G_ 1) = m (m (X_ 0)))
    (fun m hm => hm.1.1.ctx) (fun m hm => (hq m hm.1).1)
  let Pre2 : Mem → Prop := fun m => ((InstCtx k g m ∧ m (X_ 0) ∈ arrAt m (m TESTS)) ∧ m (G_ 1) = m (m (X_ 0))) ∧
    m (G_ 2) = m (m (X_ 0) + 1)
  have s1 := (isSrcTest_spec k g (G_ 1) XV (G_ 3) (G_ 4) (safeVars_G 3 (by norm_num)) (safeVars_G 4 (by norm_num))
    (by decide) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by decide) (by decide)).mono (V' := [G_ 3, G_ 4, FLAG]) (fun x hx => hx) le_rfl
    (fun m (hm : Pre2 m) => hm.1.1.1)
  have s2 := (isSrcTest_spec k g (G_ 2) YV (G_ 3) (G_ 4) (safeVars_G 3 (by norm_num)) (safeVars_G 4 (by norm_num))
    (by decide) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide) (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by decide) (by decide)).mono (V' := [G_ 3, G_ 4, FLAG]) (fun x hx => hx) le_rfl
    (fun m (hm : Pre2 m) => hm.1.1.1)
  have hs34 : SafeVars [G_ 3, G_ 4, FLAG] := safeVars_of_decide _ (by decide)
  have ta := andM_spec s1 s2 (fun x hx => (hs34 x hx).1) (fun m hm => hm.1.1.1.ctx)
    (by
      intro m m' hm hag
      obtain ⟨⟨hpre, hG1⟩, hG2⟩ := hm
      obtain ⟨hpre', hX, hc0, hc1⟩ := testPre_stable k g hs34 (by decide) hag hpre
      have hhp : 200 ≤ m HP := hpre.1.ctx.2.2
      refine ⟨⟨hpre', ?_⟩, ?_⟩
      · rw [hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide), hG1, hX, hc0]
      · rw [hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) (by decide), hG2, hX, hc1])
    (by
      intro m m' hm hag
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      dsimp only
      rw [hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var YV (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t2 := TestSpec.after e2 ta (Q := fun m => decide (g.base.nodes.getD (m (m (X_ 0))) (.app 0 []) = .src g.base.x) &&
        decide (g.base.nodes.getD (m (m (X_ 0) + 1)) (.app 0 []) = .src g.base.y))
    (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
  · have t1 := TestSpec.after e1 t2 (Q := fun m => decide (g.base.nodes.getD (m (m (X_ 0))) (.app 0 []) = .src g.base.x) &&
        decide (g.base.nodes.getD (m (m (X_ 0) + 1)) (.app 0 []) = .src g.base.y))
      (fun m m₁ hm hag hp => ?_) (fun m m₁ hm hag hp => ?_)
    · unfold guardTest
      exact t1.mono (fun x hx => hx) (by omega) (fun m hm => hm)
    · obtain ⟨hpre', hX, hc0, hc1⟩ := testPre_stable k g (safeVars_of_decide [G_ 1] (by decide)) (by decide) hag hm
      exact ⟨hpre', by rw [hp.1, hX, hc0]⟩
    · obtain ⟨hpre', hX, hc0, hc1⟩ := testPre_stable k g (safeVars_of_decide [G_ 1] (by decide)) (by decide) hag hm
      simp only [hX, hc0, hc1]
  · obtain ⟨hpre, hG1⟩ := hm
    obtain ⟨hpre', hX, hc0, hc1⟩ := testPre_stable k g (safeVars_of_decide [G_ 2] (by decide)) (by decide) hag hpre
    have hhp : 200 ≤ m HP := hpre.1.ctx.2.2
    refine ⟨⟨hpre', ?_⟩, by rw [hp.1, hX, hc1]⟩
    rw [hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide), hG1, hX, hc0]
  · obtain ⟨hpre, hG1⟩ := hm
    obtain ⟨hpre', hX, hc0, hc1⟩ := testPre_stable k g (safeVars_of_decide [G_ 2] (by decide)) (by decide) hag hpre
    have hhp : 200 ≤ m HP := hpre.1.ctx.2.2
    dsimp only
    rw [hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide), hG1, hp.1,
      hag.var XV (lt_hp hhp (by decide)) (by decide) (by decide), hag.var YV (lt_hp hhp (by decide)) (by decide) (by decide),
      hpre.1.x, hpre.1.y]

theorem guardOkM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec guardOkM (Lvars 0 ++ FLAG :: gtV) (n * (36 + 11) + 10) (InstCtx k g) (fun _ => g.base.guardOk) := by
  have hany := anyM_spec 0 TESTS n (guardTest_spec k g) (by norm_num)
    (fun x hx => ⟨(gtV_safe x hx).1, (gtV_safe x hx).2.1⟩) (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (fun m hm => hm.ctx)
    (fun m hm => ⟨hm.tests_wf.1, hm.tests_wf.2.1, by
      have := hm.arr_tests.2.2.1; rw [arrAt_length] at this; rw [this]; exact hn.tests⟩)
    (InstCtx.stableP (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG gtV_safe)))
    (by
      intro m m' hm hx hag
      have hhp : 200 ≤ m HP := hm.ctx.2.2
      have hV : ∀ x, x ∈ LvarsX 0 ++ FLAG :: gtV → x < IN := fun x hx =>
        (SafeVars.append (safeVars_LvarsX 0 (by norm_num)) (SafeVars.cons safeVars_FLAG gtV_safe) x hx).2.1
      obtain ⟨hq1, hq2, _⟩ := hm.test_rec _ hx
      dsimp only
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV _ hq1 (by omega),
        hag.heap hV _ (by omega) (by omega)])
  unfold guardOkM
  refine hany.congr (fun m hm => ?_)
  dsimp only
  unfold Instance.guardOk
  rw [← hm.pairs_tests]
  unfold pairsAt
  rw [List.any_map]
  apply any_congr_mem
  intro q hq
  simp only [Function.comp, Mem.write_same]
  obtain ⟨_, _, hrec⟩ := hm.tests_wf
  obtain ⟨hq1, hq2⟩ := hrec q hq
  rw [Mem.write_ne _ _ (show q ≠ X_ 0 by addr3), Mem.write_ne _ _ (show q + 1 ≠ X_ 0 by addr3)]


/-! ### `nodesOk` -/

/-- The two shapes of a represented node. -/
theorem repNode_cases {m : Mem} {lo hi p : ℕ} {nd : Node} (h : RepNode m lo hi p nd) :
    (m p = 0 ∧ ∃ i, nd = .src i ∧ m (p + 1) = i) ∨
    (m p = 1 ∧ ∃ f args, nd = .app f args ∧ m (p + 1) = f ∧ RepArr m lo hi (m (p + 2)) args) := by
  cases nd with
  | src i => exact Or.inl ⟨h.2.2.1, i, rfl, h.2.2.2⟩
  | app f args => exact Or.inr ⟨h.2.2.1, f, args, rfl, h.2.2.2.1, h.2.2.2.2⟩

theorem repArr_arrAt {m : Mem} {lo hi v : ℕ} {l : List ℕ} (h : RepArr m lo hi v l) : arrAt m v = l :=
  arrAt_of_cells h.2.2.1 h.2.2.2

/-- `nodeOk` in terms of the record cells. -/
theorem nodeOk_eq (γ : Instance) (j : ℕ) {m : Mem} {lo hi p : ℕ} {nd : Node} (h : RepNode m lo hi p nd) :
    γ.nodeOk j nd = (if m p = 0 then decide (m (p + 1) < γ.k) else
      (decide (m (p + 1) < γ.m) && decide (m (m (p + 2)) = γ.arityOf (m (p + 1)))) &&
        (arrAt m (m (p + 2))).all (fun a => decide (a < j))) := by
  rcases repNode_cases h with ⟨h0, i, rfl, h1⟩ | ⟨h0, f, args, rfl, h1, h2⟩
  · rw [if_pos h0, h1]; rfl
  · rw [if_neg (by omega), h1, repArr_arrAt h2, h2.2.2.1]; rfl

/-- The node record at index `X_ 0`. -/
theorem InstCtx.node_at {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) (hj : m (X_ 0) < m NN) :
    IN ≤ m NODES + 1 + m (X_ 0) ∧ m NODES + 1 + m (X_ 0) < m HP ∧ IN ≤ m (m NODES + 1 + m (X_ 0)) ∧
      m (m NODES + 1 + m (X_ 0)) + 2 ≤ m HP ∧
      RepNode m IN (m HP) (m (m NODES + 1 + m (X_ 0))) (g.base.nodes.getD (m (X_ 0)) (.src 0)) := by
  have hi : m (X_ 0) < g.base.nodes.length := by rw [← hm.nn]; exact hj
  obtain ⟨h1, h2, h3, h4⟩ := hm.node_rec (m (X_ 0)) hi
  rw [List.getD_eq_getElem _ _ hi]
  exact ⟨h1, h2, h3, repNode_size h4, h4⟩

/-- `args.length = arityOf f` with `G_ 3 = f`, `G_ 4 = args pointer`; scratch `G_ 5`, `G_ 6`, `G_ 7`. -/
def arityTest : Cmd :=
  .ite (.lt (G_ 3) MM)
    (.seq (elemM SYMS (G_ 3) (G_ 5)) (.seq (field1M (G_ 5) (G_ 6))
      (.seq (load (G_ 7) (G_ 4)) (eqTest (G_ 7) (G_ 6)))))
    (.seq (load (G_ 7) (G_ 4)) (eqTest (G_ 7) ZERO))

/-- `args.all (· < j)` with `G_ 4 = args pointer`, `X_ 0 = j`. -/
def argsTest : Cmd := allM 1 (G_ 4) (ltTest (X_ 1) (X_ 0))

/-- `nodeOk j nodes[j]` for `X_ 0 = j`. -/
def nodeTest : Cmd :=
  .seq (elemM NODES (X_ 0) (G_ 1)) (.seq (load (G_ 2) (G_ 1))
    (.ite (.eq (G_ 2) ZERO)
      (.seq (field1M (G_ 1) (G_ 3)) (ltTest (G_ 3) KK))
      (.seq (field1M (G_ 1) (G_ 3)) (.seq (field2M (G_ 1) (G_ 4))
        (andM (andM (ltTest (G_ 3) MM) arityTest) argsTest)))))

/-- `(range |nodes|).all nodeTest`. -/
def nodesOkM : Cmd := allRangeM 0 NN nodeTest

theorem InstCtx.sym_rec {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) (f : ℕ) (hf : f < m MM) :
    IN ≤ m SYMS + 1 + f ∧ m SYMS + 1 + f < m HP ∧ IN ≤ m (m SYMS + 1 + f) ∧ m (m SYMS + 1 + f) + 2 ≤ m HP ∧
      m (m (m SYMS + 1 + f) + 1) = g.base.arityOf f := by
  have hf' : f < g.base.symbols.length := by rw [← hm.mm]; exact hf
  obtain ⟨h1, h2, h3, h4⟩ := hm.arr_syms
  rw [arrAt_length] at h3
  obtain ⟨g1, g2, _, g4⟩ := h4 f hf'
  refine ⟨by addr3, by omega, g1, g2, ?_⟩
  rw [g4]; unfold Instance.arityOf; rw [List.getD_eq_getElem _ _ hf']

/-- The precondition of `arityTest`: `G_ 4` points into the heap. -/
def ArityPre (k : ℕ) (g : GInstance) (m : Mem) : Prop := InstCtx k g m ∧ IN ≤ m (G_ 4) ∧ m (G_ 4) < m HP

theorem arityTest_spec (k : ℕ) (g : GInstance) :
    TestSpec arityTest [G_ 5, G_ 6, G_ 7, FLAG] 15 (ArityPre k g)
      (fun m => decide (m (m (G_ 4)) = g.base.arityOf (m (G_ 3)))) := by
  have hs5 : SafeVars [G_ 5] := safeVars_of_decide _ (by decide)
  have hs6 : SafeVars [G_ 6] := safeVars_of_decide _ (by decide)
  have hs7 : SafeVars [G_ 7] := safeVars_of_decide _ (by decide)
  have hV5 : ∀ x, x ∈ [G_ 5] → x < IN := fun x hx => (hs5 x hx).2.1
  have hV6 : ∀ x, x ∈ [G_ 6] → x < IN := fun x hx => (hs6 x hx).2.1
  -- stability of `ArityPre` and of the cell `M[G_ 4]`
  have hstab : ∀ {V : List ℕ}, SafeVars V → G_ 4 ∉ V → ∀ m m₁, Agree m m₁ V → ArityPre k g m →
      ArityPre k g m₁ ∧ m₁ (G_ 4) = m (G_ 4) ∧ m₁ (m (G_ 4)) = m (m (G_ 4)) := by
    intro V hV hG m m₁ hag hm
    have hhp : 200 ≤ m HP := hm.1.ctx.2.2
    have hG' : m₁ (G_ 4) = m (G_ 4) := hag.var (G_ 4) (lt_hp hhp (by decide)) (by decide) hG
    refine ⟨⟨hm.1.of_agree hag hV, by rw [hG']; exact hm.2.1, by rw [hG']; exact lt_of_lt_of_le hm.2.2 hag.2⟩,
      hG', hag.heap (fun x hx => (hV x hx).2.1) _ hm.2.1 hm.2.2⟩
  -- then-branch
  let Pre1 : Mem → Prop := fun m => ArityPre k g m ∧ m (G_ 3) < m MM
  have e0 := elemM_spec SYMS (G_ 3) (G_ 5) (by constructor <;> addr3) (by decide) (by decide) Pre1
    (fun m hm => hm.1.1.ctx) (fun m hm => hm.1.1.arr_syms.1)
  let Pre2 : Mem → Prop := fun m => Pre1 m ∧ m (G_ 5) = m (m SYMS + 1 + m (G_ 3))
  have e1 := field1M_spec (G_ 5) (G_ 6) (by constructor <;> addr3) (by decide) Pre2 (fun m hm => hm.1.1.1.ctx)
    (fun m hm => by rw [hm.2]; exact (hm.1.1.1.sym_rec _ hm.1.2).2.2.1)
  let Pre3 : Mem → Prop := fun m => Pre2 m ∧ m (G_ 6) = m (m (G_ 5) + 1)
  have e2 := loadM_spec (G_ 4) (G_ 7) (by constructor <;> addr3) Pre3
  have t3 := TestSpec.after e2 (eqTest_spec (G_ 7) (G_ 6) (fun _ => True))
    (Q := fun m => decide (m (m (G_ 4)) = m (G_ 6))) (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      dsimp only
      rw [hp.1, hag.var (G_ 6) (lt_hp hhp (by decide)) (by decide) (by decide)])
  have t2 := TestSpec.after e1 t3 (Q := fun m => decide (m (m (G_ 4)) = m (m (G_ 5) + 1)))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      obtain ⟨hq1, hq2, hq3, hq4, _⟩ := hm.1.1.1.sym_rec _ hm.1.2
      obtain ⟨hA, _, _⟩ := hstab hs6 (by decide) m m₁ hag hm.1.1
      refine ⟨⟨⟨hA, ?_⟩, ?_⟩, ?_⟩
      · rw [hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var MM (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.1.2
      · rw [hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var SYMS (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV6 _ hq1 hq2]
        exact hm.2
      · rw [hp.1, hag.var (G_ 5) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.heap hV6 (m (G_ 5) + 1) (by rw [hm.2]; omega) (by rw [hm.2]; omega)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
      obtain ⟨_, _, hq3, hq4, _⟩ := hm.1.1.1.sym_rec _ hm.1.2
      obtain ⟨_, hG, hc⟩ := hstab hs6 (by decide) m m₁ hag hm.1.1
      dsimp only
      rw [hG, hc, hp.1])
  have t1 := TestSpec.after e0 t2 (Q := fun m => decide (m (m (G_ 4)) = m (m (m SYMS + 1 + m (G_ 3)) + 1)))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨hq1, hq2, _⟩ := hm.1.1.sym_rec _ hm.2
      obtain ⟨hA, _, _⟩ := hstab hs5 (by decide) m m₁ hag hm.1
      refine ⟨⟨hA, ?_⟩, ?_⟩
      · rw [hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var MM (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2
      · rw [hp.1, hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide),
          hag.var SYMS (lt_hp hhp (by decide)) (by decide) (by decide), hag.heap hV5 _ hq1 hq2])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨hq1, hq2, hq3, hq4, _⟩ := hm.1.1.sym_rec _ hm.2
      obtain ⟨_, hG, hc⟩ := hstab hs5 (by decide) m m₁ hag hm.1
      dsimp only
      rw [hG, hc, hp.1, hag.heap hV5 (m (m SYMS + 1 + m (G_ 3)) + 1) (by omega) (by omega)])
  -- else-branch
  have e4 := loadM_spec (G_ 4) (G_ 7) (by constructor <;> addr3) (fun m => ArityPre k g m ∧ ¬ m (G_ 3) < m MM)
  have t4 := TestSpec.after e4 (eqTest_spec (G_ 7) ZERO (fun _ => True))
    (Q := fun m => decide (m (m (G_ 4)) = 0)) (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      dsimp only
      rw [hp.1, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide), hm.1.1.ctx.2.1])
  have tt := TestSpec.iteLt' (G_ 3) MM t1 t4
  unfold arityTest
  refine (tt.mono (V' := [G_ 5, G_ 6, G_ 7, FLAG]) (fun x hx => by simp at hx ⊢; tauto) (by omega)
    (fun m hm => hm)).congr (fun m hm => ?_)
  dsimp only
  by_cases hlt : m (G_ 3) < m MM
  · rw [if_pos hlt, (hm.1.sym_rec _ hlt).2.2.2.2]
  · rw [if_neg hlt]
    unfold Instance.arityOf
    rw [List.getD_eq_default _ _ (by rw [← hm.1.mm]; omega)]

/-- The precondition of `argsTest`: `G_ 4` points to an array of at most `n` elements. -/
def ArgsPre (k : ℕ) (g : GInstance) (n : ℕ) (m : Mem) : Prop :=
  InstCtx k g m ∧ IN ≤ m (G_ 4) ∧ m (G_ 4) + 1 + m (m (G_ 4)) ≤ m HP ∧ m (m (G_ 4)) ≤ n

theorem argsTest_spec (k : ℕ) (g : GInstance) (n : ℕ) :
    TestSpec argsTest (FLAG :: (Lvars 1 ++ FLAG :: (FLAG :: [FLAG]))) (n * (3 + 12) + 11) (ArgsPre k g n)
      (fun m => (arrAt m (m (G_ 4))).all (fun a => decide (a < m (X_ 0)))) := by
  have hall := allM_spec 1 (G_ 4) n (ltTest_spec (X_ 1) (X_ 0) (fun m => ArgsPre k g n m ∧ m (X_ 1) ∈ arrAt m (m (G_ 4))))
    (by norm_num) (by intro x hx; simp at hx; subst hx; constructor <;> addr3) (by constructor <;> addr3)
    (by decide) (by decide) (by decide) (by decide) (fun m hm => hm.1.ctx)
    (fun m hm => ⟨hm.2.1, hm.2.2.1, hm.2.2.2⟩)
    (by
      intro m m' hm hag
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      have hV : SafeVars (Lvars 1 ++ FLAG :: [FLAG]) :=
        SafeVars.append (safeVars_Lvars 1 (by norm_num)) (SafeVars.cons safeVars_FLAG (SafeVars.cons safeVars_FLAG
          (fun x hx => by simp at hx)))
      have hG : m' (G_ 4) = m (G_ 4) := hag.var (G_ 4) (lt_hp hhp (by decide)) (by decide) (by decide)
      have h22 := hm.2.2.1
      have hc : m' (m (G_ 4)) = m (m (G_ 4)) := hag.heap (fun x hx => (hV x hx).2.1) _ hm.2.1 (by omega)
      refine ⟨hm.1.of_agree hag hV, ?_, ?_, ?_⟩
      · rw [hG]; exact hm.2.1
      · rw [hG, hc]; exact le_trans hm.2.2.1 hag.2
      · rw [hG, hc]; exact hm.2.2.2)
    (by
      intro m m' hm hx hag
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      dsimp only
      rw [hag.var (X_ 1) (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
  unfold argsTest
  refine hall.congr (fun m hm => ?_)
  dsimp only
  apply all_congr_mem
  intro a ha
  rw [Mem.write_same, Mem.write_ne _ _ (show X_ 0 ≠ X_ 1 by decide)]


/-- Stability of the node precondition under safe writes not touching `X_ 0`. -/
theorem nodePre_stable (k : ℕ) (g : GInstance) {V : List ℕ} (hV : SafeVars V) (hX : X_ 0 ∉ V)
    {m m₁ : Mem} (hag : Agree m m₁ V) (h : InstCtx k g m ∧ m (X_ 0) < m NN) :
    (InstCtx k g m₁ ∧ m₁ (X_ 0) < m₁ NN) ∧ m₁ (X_ 0) = m (X_ 0) ∧ m₁ NODES = m NODES ∧
      (∀ x, IN ≤ x → x < m HP → m₁ x = m x) := by
  obtain ⟨hm, hj⟩ := h
  have hhp : 200 ≤ m HP := hm.ctx.2.2
  have hV' : ∀ x, x ∈ V → x < IN := fun x hx => (hV x hx).2.1
  have hX' : m₁ (X_ 0) = m (X_ 0) := hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) hX
  refine ⟨⟨hm.of_agree hag hV, ?_⟩, hX', hag.var NODES (lt_hp hhp (by decide)) (by decide)
    (fun h => (hV NODES h).2.2 (by decide)), fun x h1 h2 => hag.heap hV' x h1 h2⟩
  rw [hX', hag.var NN (lt_hp hhp (by decide)) (by decide) (fun h => (hV NN h).2.2 (by decide))]; exact hj

/-- An application node at `X_ 0`, recognised by its tag. -/
theorem InstCtx.app_at {k : ℕ} {g : GInstance} {m : Mem} (hm : InstCtx k g m) (hj : m (X_ 0) < m NN)
    (htag : m (m (m NODES + 1 + m (X_ 0))) ≠ 0) :
    ∃ f args, g.base.nodes.getD (m (X_ 0)) (.src 0) = .app f args ∧
      m (m (m NODES + 1 + m (X_ 0)) + 1) = f ∧
      RepArr m IN (m HP) (m (m (m NODES + 1 + m (X_ 0)) + 2)) args ∧ m (m NODES + 1 + m (X_ 0)) + 3 ≤ m HP := by
  obtain ⟨_, _, _, _, hrep⟩ := hm.node_at hj
  rcases repNode_cases hrep with ⟨h0, _⟩ | ⟨_, f, args, he, h1, h2⟩
  · exact absurd h0 htag
  · exact ⟨f, args, he, h1, h2, by rw [he] at hrep; exact hrep.2.1⟩

theorem Sized.args_getD {n : ℕ} {g : GInstance} (hn : Sized n g) (j : ℕ) (hj : j < g.base.nodes.length)
    (f : ℕ) (args : List ℕ) (h : g.base.nodes.getD j (.src 0) = .app f args) : args.length ≤ n := by
  rw [List.getD_eq_getElem _ _ hj] at h
  exact hn.args _ (List.getElem_mem hj) f args h

def ntV : List ℕ := [G_ 1, G_ 2, G_ 3, G_ 4, G_ 5, G_ 6, G_ 7, FLAG] ++ Lvars 1

theorem ntV_safe : SafeVars ntV := SafeVars.append (safeVars_of_decide _ (by decide)) (safeVars_Lvars 1 (by norm_num))

theorem repArr_bounds {m : Mem} {lo hi v : ℕ} {l : List ℕ} (h : RepArr m lo hi v l) :
    lo ≤ v ∧ v + 1 + m v ≤ hi := ⟨h.1, by rw [h.2.2.1]; exact h.2.1⟩

theorem nodeTest_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec nodeTest ntV (n * 15 + 51) (fun m => InstCtx k g m ∧ m (X_ 0) < m NN)
      (fun m => g.base.nodeOk (m (X_ 0)) (g.base.nodes.getD (m (X_ 0)) (.src 0))) := by
  have hsG : ∀ i, i < 60 → SafeVars [G_ i] := fun i hi x hx => by simp at hx; subst hx; exact safeVars_G i hi
  have hsF : SafeVars [FLAG] := fun x hx => by simp at hx; subst hx; exact safeVars_FLAG
  -- the precondition after the node pointer and the tag are loaded
  let Pre0 : Mem → Prop := fun m => InstCtx k g m ∧ m (X_ 0) < m NN
  let Pre1 : Mem → Prop := fun m => Pre0 m ∧ m (G_ 1) = m (m NODES + 1 + m (X_ 0))
  let Pre2 : Mem → Prop := fun m => Pre1 m ∧ m (G_ 2) = m (m (G_ 1))
  have hnode : ∀ m, Pre1 m → IN ≤ m (G_ 1) ∧ m (G_ 1) + 2 ≤ m HP := by
    intro m hm
    obtain ⟨_, _, h3, h4, _⟩ := hm.1.1.node_at hm.1.2
    rw [hm.2]; exact ⟨h3, h4⟩
  -- generic stability of `Pre2 ∧ tag condition` under safe writes avoiding `X_ 0, G_ 1, G_ 2`
  have hstab2 : ∀ {V : List ℕ}, SafeVars V → X_ 0 ∉ V → G_ 1 ∉ V → G_ 2 ∉ V → ∀ m m₁, Agree m m₁ V →
      Pre2 m → Pre2 m₁ ∧ m₁ (X_ 0) = m (X_ 0) ∧ m₁ (G_ 1) = m (G_ 1) ∧ m₁ (G_ 2) = m (G_ 2) ∧
        (∀ x, IN ≤ x → x < m HP → m₁ x = m x) := by
    intro V hV hX h1 h2 m m₁ hag hm
    have hhp : 200 ≤ m HP := hm.1.1.1.ctx.2.2
    obtain ⟨hp0, hX', hN', hheap⟩ := nodePre_stable k g hV hX hag hm.1.1
    obtain ⟨hq1, hq2, hq3, hq4, _⟩ := hm.1.1.1.node_at hm.1.1.2
    have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) h1
    have hG2 : m₁ (G_ 2) = m (G_ 2) := hag.var (G_ 2) (lt_hp hhp (by decide)) (by decide) h2
    refine ⟨⟨⟨hp0, ?_⟩, ?_⟩, hX', hG1, hG2, hheap⟩
    · rw [hG1, hX', hN', hheap _ hq1 hq2]; exact hm.1.2
    · obtain ⟨hn1, hn2⟩ := hnode m hm.1
      rw [hG2, hG1, hheap (m (G_ 1)) hn1 (by omega)]; exact hm.2
  -- source branch
  have es := field1M_spec (G_ 1) (G_ 3) (by constructor <;> addr3) (by decide)
    (fun m => Pre2 m ∧ m (G_ 2) = m ZERO) (fun m hm => hm.1.1.1.1.ctx) (fun m hm => (hnode m hm.1.1).1)
  have ts := TestSpec.after es (ltTest_spec (G_ 3) KK (fun _ => True))
    (Q := fun m => decide (m (m (G_ 1) + 1) < m KK)) (fun _ _ _ _ _ => trivial)
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      dsimp only
      rw [hp.1, hag.var KK (lt_hp hhp (by decide)) (by decide) (by decide)])
  -- application branch
  let PreA : Mem → Prop := fun m => Pre2 m ∧ m (G_ 2) ≠ m ZERO
  let PreB : Mem → Prop := fun m => PreA m ∧ m (G_ 3) = m (m (G_ 1) + 1)
  let PreC : Mem → Prop := fun m => PreB m ∧ m (G_ 4) = m (m (G_ 1) + 2)
  have happ : ∀ m, PreA m → ∃ f args, g.base.nodes.getD (m (X_ 0)) (.src 0) = .app f args ∧
      m (m (G_ 1) + 1) = f ∧ RepArr m IN (m HP) (m (m (G_ 1) + 2)) args ∧ m (G_ 1) + 3 ≤ m HP := by
    intro m hm
    have hz := hm.1.1.1.1.ctx.2.1
    have h2 : m (G_ 2) ≠ m ZERO := hm.2
    rw [hz] at h2
    have htag : m (m (m NODES + 1 + m (X_ 0))) ≠ 0 := by
      rw [← hm.1.1.2, ← hm.1.2]; exact h2
    obtain ⟨f, args, he, h1, h2, h3⟩ := hm.1.1.1.1.app_at hm.1.1.1.2 htag
    rw [← hm.1.1.2] at h1 h2 h3
    exact ⟨f, args, he, h1, h2, h3⟩
  have hC : ∀ m, PreC m → ArityPre k g m ∧ ArgsPre k g n m := by
    intro m hm
    obtain ⟨f, args, he, h1, h2, h3⟩ := happ m hm.1.1
    have hj : m (X_ 0) < g.base.nodes.length := by rw [← hm.1.1.1.1.1.1.nn]; exact hm.1.1.1.1.1.2
    have hlen := hn.args_getD _ hj f args he
    obtain ⟨g1, g2⟩ := repArr_bounds h2
    have g3 := h2.2.2.1
    rw [← hm.2] at g1 g2 g3
    refine ⟨⟨hm.1.1.1.1.1.1, g1, by omega⟩, hm.1.1.1.1.1.1, g1, g2, by rw [g3]; exact hlen⟩
  have ea := field1M_spec (G_ 1) (G_ 3) (by constructor <;> addr3) (by decide) PreA
    (fun m hm => hm.1.1.1.1.ctx) (fun m hm => (hnode m hm.1.1).1)
  have eb := field2M_spec (G_ 1) (G_ 4) (by constructor <;> addr3) (by decide) PreB
    (fun m hm => hm.1.1.1.1.1.ctx) (fun m hm => (hnode m hm.1.1.1).1)
  have tl := ltTest_spec (G_ 3) MM PreC
  have tar := (arityTest_spec k g).mono (fun x hx => hx) le_rfl (fun m hm => (hC m hm).1)
  have targs := (argsTest_spec k g n).mono (fun x hx => hx) le_rfl (fun m hm => (hC m hm).2)
  -- stability of `PreC` under safe writes avoiding `X_ 0, G_ 1, G_ 2, G_ 3, G_ 4`
  have hstabC : ∀ {V : List ℕ}, SafeVars V → X_ 0 ∉ V → G_ 1 ∉ V → G_ 2 ∉ V → G_ 3 ∉ V → G_ 4 ∉ V →
      ∀ m m₁, Agree m m₁ V → PreC m → PreC m₁ ∧ m₁ (X_ 0) = m (X_ 0) ∧ m₁ (G_ 3) = m (G_ 3) ∧
        m₁ (G_ 4) = m (G_ 4) ∧ (∀ x, IN ≤ x → x < m HP → m₁ x = m x) := by
    intro V hV hX h1 h2 h3 h4 m m₁ hag hm
    have hhp : 200 ≤ m HP := hm.1.1.1.1.1.1.ctx.2.2
    obtain ⟨hp2, hX', hG1, hG2, hheap⟩ := hstab2 hV hX h1 h2 m m₁ hag hm.1.1.1
    obtain ⟨hq1, hq2⟩ := hnode m hm.1.1.1.1
    obtain ⟨_, _, _, _, _, hq3⟩ := happ m hm.1.1
    have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) h3
    have hG4 : m₁ (G_ 4) = m (G_ 4) := hag.var (G_ 4) (lt_hp hhp (by decide)) (by decide) h4
    refine ⟨⟨⟨⟨hp2, ?_⟩, ?_⟩, ?_⟩, hX', hG3, hG4, hheap⟩
    · rw [hG2, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (fun h => by have := (hV ZERO h).1; addr3)]
      exact hm.1.1.2
    · rw [hG3, hG1, hheap _ (by omega) (by omega)]; exact hm.1.2
    · rw [hG4, hG1, hheap _ (by omega) (by omega)]; exact hm.2
  have tand1 := andM_spec tl tar (fun x hx => by simp at hx; subst hx; addr3) (fun m hm => hm.1.1.1.1.1.1.ctx)
    (fun m m₁ hm hag => (hstabC hsF (by decide) (by decide) (by decide) (by decide) (by decide) m m₁ hag hm).1)
    (fun m m₁ hm hag => by
      obtain ⟨_, _, hG3, hG4, hheap⟩ := hstabC hsF (by decide) (by decide) (by decide) (by decide) (by decide)
        m m₁ hag hm
      obtain ⟨⟨_, g1, g2⟩, _⟩ := hC m hm
      show decide (m₁ (m₁ (G_ 4)) = g.base.arityOf (m₁ (G_ 3))) = decide (m (m (G_ 4)) = g.base.arityOf (m (G_ 3)))
      rw [hG3, hG4, hheap _ g1 g2])
  have hs4 : SafeVars ([FLAG] ++ [G_ 5, G_ 6, G_ 7, FLAG]) := safeVars_of_decide _ (by decide)
  have tand2 := andM_spec tand1 targs (fun x hx => (hs4 x hx).1) (fun m hm => hm.1.1.1.1.1.1.ctx)
    (fun m m₁ hm hag => (hstabC hs4 (by decide) (by decide) (by decide) (by decide) (by decide) m m₁ hag hm).1)
    (fun m m₁ hm hag => by
      obtain ⟨_, hX', hG3, hG4, hheap⟩ := hstabC hs4 (by decide) (by decide) (by decide) (by decide) (by decide)
        m m₁ hag hm
      obtain ⟨_, _, g1, g2, _⟩ := hC m hm
      show (arrAt m₁ (m₁ (G_ 4))).all (fun a => decide (a < m₁ (X_ 0))) =
        (arrAt m (m (G_ 4))).all (fun a => decide (a < m (X_ 0)))
      rw [hG4, hX', hag.arrAt (fun x hx => (hs4 x hx).2.1) _ g1 g2])
  have tB := TestSpec.after eb tand2
    (Q := fun m => (decide (m (G_ 3) < m MM) && decide (m (m (m (G_ 1) + 2)) = g.base.arityOf (m (G_ 3)))) &&
      (arrAt m (m (m (G_ 1) + 2))).all (fun a => decide (a < m (X_ 0))))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      obtain ⟨hp2, hX', hG1, hG2, hheap⟩ := hstab2 (hsG 4 (by norm_num)) (by decide) (by decide) (by decide)
        m m₁ hag hm.1.1
      obtain ⟨hq1, hq2⟩ := hnode m hm.1.1.1
      obtain ⟨_, _, _, _, _, hq3⟩ := happ m hm.1
      have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine ⟨⟨⟨hp2, ?_⟩, ?_⟩, ?_⟩
      · rw [hG2, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.1.2
      · rw [hG3, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)]; exact hm.2
      · rw [hp.1, hG1, hheap (m (G_ 1) + 2) (by omega) (by omega)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.1.ctx.2.2
      obtain ⟨hp2, hX', hG1, hG2, hheap⟩ := hstab2 (hsG 4 (by norm_num)) (by decide) (by decide) (by decide)
        m m₁ hag hm.1.1
      obtain ⟨hq1, hq2⟩ := hnode m hm.1.1.1
      obtain ⟨_, _, _, _, h2, hq3⟩ := happ m hm.1
      obtain ⟨g1, g2⟩ := repArr_bounds h2
      have hG3 : m₁ (G_ 3) = m (G_ 3) := hag.var (G_ 3) (lt_hp hhp (by decide)) (by decide) (by decide)
      dsimp only
      rw [hp.1, hG3, hX', hag.var MM (lt_hp hhp (by decide)) (by decide) (by decide),
        hheap (m (m (G_ 1) + 2)) g1 (by omega),
        hag.arrAt (fun x hx => ((hsG 4 (by norm_num)) x hx).2.1) _ g1 g2])
  have tA := TestSpec.after ea tB
    (Q := fun m => (decide (m (m (G_ 1) + 1) < m MM) &&
        decide (m (m (m (G_ 1) + 2)) = g.base.arityOf (m (m (G_ 1) + 1)))) &&
      (arrAt m (m (m (G_ 1) + 2))).all (fun a => decide (a < m (X_ 0))))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      obtain ⟨hp2, hX', hG1, hG2, hheap⟩ := hstab2 (hsG 3 (by norm_num)) (by decide) (by decide) (by decide)
        m m₁ hag hm.1
      obtain ⟨hq1, hq2⟩ := hnode m hm.1.1
      refine ⟨⟨hp2, ?_⟩, ?_⟩
      · rw [hG2, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide)]; exact hm.2
      · rw [hp.1, hG1, hheap (m (G_ 1) + 1) (by omega) (by omega)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.1.1.ctx.2.2
      obtain ⟨hp2, hX', hG1, hG2, hheap⟩ := hstab2 (hsG 3 (by norm_num)) (by decide) (by decide) (by decide)
        m m₁ hag hm.1
      obtain ⟨hq1, hq2⟩ := hnode m hm.1.1
      obtain ⟨_, _, _, _, h2, hq3⟩ := happ m hm
      obtain ⟨g1, g2⟩ := repArr_bounds h2
      dsimp only
      rw [hp.1, hG1, hX', hag.var MM (lt_hp hhp (by decide)) (by decide) (by decide),
        hheap (m (G_ 1) + 2) (by omega) (by omega),
        hheap (m (m (G_ 1) + 2)) g1 (by omega), hag.arrAt (fun x hx => ((hsG 3 (by norm_num)) x hx).2.1) _ g1 g2])
  -- the conditional on the tag
  have tite := TestSpec.ite' (G_ 2) ZERO ts tA
  have e1 := loadM_spec (G_ 1) (G_ 2) (by constructor <;> addr3) Pre1
  have t1 := TestSpec.after e1 tite
    (Q := fun m => if m (m (G_ 1)) = 0 then decide (m (m (G_ 1) + 1) < m KK) else
      (decide (m (m (G_ 1) + 1) < m MM) &&
        decide (m (m (m (G_ 1) + 2)) = g.base.arityOf (m (m (G_ 1) + 1)))) &&
      (arrAt m (m (m (G_ 1) + 2))).all (fun a => decide (a < m (X_ 0))))
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨hp0, hX', hN', hheap⟩ := nodePre_stable k g (hsG 2 (by norm_num)) (by decide) hag hm.1
      obtain ⟨hq1, hq2, hq3, hq4, _⟩ := hm.1.1.node_at hm.1.2
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      refine ⟨⟨hp0, ?_⟩, ?_⟩
      · rw [hG1, hX', hN', hheap _ hq1 hq2]; exact hm.2
      · rw [hp.1, hG1, hheap (m (G_ 1)) (by rw [hm.2]; exact hq3) (by rw [hm.2]; omega)])
    (fun m m₁ hm hag hp => by
      have hhp : 200 ≤ m HP := hm.1.1.ctx.2.2
      obtain ⟨hp0, hX', hN', hheap⟩ := nodePre_stable k g (hsG 2 (by norm_num)) (by decide) hag hm.1
      obtain ⟨hq1, hq2, hq3, hq4, hrep⟩ := hm.1.1.node_at hm.1.2
      have hG1 : m₁ (G_ 1) = m (G_ 1) := hag.var (G_ 1) (lt_hp hhp (by decide)) (by decide) (by decide)
      have hz := hm.1.1.ctx.2.1
      have hpIN : IN ≤ m (G_ 1) := by rw [hm.2]; exact hq3
      have hp2 : m (G_ 1) + 2 ≤ m HP := by rw [hm.2]; exact hq4
      dsimp only
      rw [hp.1, hag.var ZERO (lt_hp hhp (by decide)) (by decide) (by decide), hz, hG1, hX',
        hag.var KK (lt_hp hhp (by decide)) (by decide) (by decide),
        hag.var MM (lt_hp hhp (by decide)) (by decide) (by decide),
        hheap (m (G_ 1) + 1) (by omega) (by omega)]
      by_cases htag : m (m (G_ 1)) = 0
      · rw [if_pos htag, if_pos htag]
      · rw [if_neg htag, if_neg htag]
        have htag' : m (m (m NODES + 1 + m (X_ 0))) ≠ 0 := by rw [← hm.2]; exact htag
        obtain ⟨_, _, _, _, h2, hq5⟩ := hm.1.1.app_at hm.1.2 htag'
        rw [← hm.2] at h2 hq5
        obtain ⟨g1, g2⟩ := repArr_bounds h2
        rw [hheap (m (G_ 1) + 2) (by omega) (by omega), hheap (m (m (G_ 1) + 2)) g1 (by omega),
          hag.arrAt (fun x hx => ((hsG 2 (by norm_num)) x hx).2.1) _ g1 g2])
  have e0 := elemM_spec NODES (X_ 0) (G_ 1) (by constructor <;> addr3) (by decide) (by decide) Pre0
    (fun m hm => hm.1.ctx) (fun m hm => hm.1.arr_nodes.1)
  have t0 := TestSpec.after e0 t1
    (Q := fun m => g.base.nodeOk (m (X_ 0)) (g.base.nodes.getD (m (X_ 0)) (.src 0)))
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hX', hN', hheap⟩ := nodePre_stable k g (hsG 1 (by norm_num)) (by decide) hag hm
      obtain ⟨hq1, hq2, _⟩ := hm.1.node_at hm.2
      exact ⟨hp0, by rw [hp.1, hX', hN', hheap _ hq1 hq2]⟩)
    (fun m m₁ hm hag hp => by
      obtain ⟨hp0, hX', hN', hheap⟩ := nodePre_stable k g (hsG 1 (by norm_num)) (by decide) hag hm
      obtain ⟨hq1, hq2, hq3, hq4, hrep⟩ := hm.1.node_at hm.2
      have hV1 : ∀ x, x ∈ [G_ 1] → x < IN := fun x hx => ((hsG 1 (by norm_num)) x hx).2.1
      dsimp only
      rw [hp.1, hX', hag.var KK (lt_hp hm.1.ctx.2.2 (by decide)) (by decide) (by decide),
        hag.var MM (lt_hp hm.1.ctx.2.2 (by decide)) (by decide) (by decide),
        hheap _ hq3 (by omega), hheap (m (m NODES + 1 + m (X_ 0)) + 1) (by omega) (by omega),
        nodeOk_eq g.base (m (X_ 0)) hrep, hm.1.kk, hm.1.mm]
      by_cases htag : m (m (m NODES + 1 + m (X_ 0))) = 0
      · rw [if_pos htag, if_pos htag]; rfl
      · rw [if_neg htag, if_neg htag]
        obtain ⟨_, _, _, _, h2, hq5⟩ := hm.1.app_at hm.2 htag
        obtain ⟨g1, g2⟩ := repArr_bounds h2
        rw [hheap (m (m NODES + 1 + m (X_ 0)) + 2) (by omega) (by omega),
          hheap (m (m (m NODES + 1 + m (X_ 0)) + 2)) g1 (by omega), hag.arrAt hV1 _ g1 g2]
        rfl)
  unfold nodeTest
  exact t0.mono (fun x hx => by unfold ntV; simp [Lvars] at hx ⊢; tauto) (by omega) (fun m hm => hm)


theorem nodesOkM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec nodesOkM (FLAG :: (rangeV 0 ++ FLAG :: (FLAG :: ntV))) (n * (n * 15 + 51 + 12) + n * 6 + 21)
      (InstCtx k g) (fun _ => g.base.nodesOk) := by
  have hall := allRangeM_spec 0 NN n (by norm_num) (nodeTest_spec k g n hn)
    (fun x hx => ⟨(ntV_safe x hx).1, (ntV_safe x hx).2.1⟩) (by constructor <;> addr3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun m hm => hm.ctx)
    (fun m hm => by rw [hm.nn]; exact hn.nodes)
    (InstCtx.stableP (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG ntV_safe)))
    (by
      intro m m' hm hag
      have hhp : 200 ≤ m HP := hm.1.ctx.2.2
      dsimp only
      rw [hag.var (X_ 0) (lt_hp hhp (by decide)) (by decide) (by decide)])
  unfold nodesOkM
  refine hall.congr (fun m hm => ?_)
  dsimp only
  unfold Instance.nodesOk
  rw [hm.nn]
  simp only [Mem.write_same]

/-! ### Assembling `isValid` -/

/-- Conjunction of two constant-valued tests in the instance context. -/
theorem andC_spec {k : ℕ} {g : GInstance} {t₁ t₂ : Cmd} {V₁ V₂ : List ℕ} {B₁ B₂ : ℕ} {b₁ b₂ : Bool}
    (h₁ : TestSpec t₁ V₁ B₁ (InstCtx k g) (fun _ => b₁)) (h₂ : TestSpec t₂ V₂ B₂ (InstCtx k g) (fun _ => b₂))
    (hV₁ : SafeVars V₁) :
    TestSpec (andM t₁ t₂) (V₁ ++ V₂) (B₁ + B₂ + 3) (InstCtx k g) (fun _ => b₁ && b₂) :=
  andM_spec h₁ h₂ (fun x hx => (hV₁ x hx).1) (fun m hm => hm.ctx) (InstCtx.stableP hV₁) (fun _ _ _ _ => rfl)

/-- `Instance.isValid` on the machine (the same left-associated conjunction). -/
def isValidM : Cmd :=
  andM (andM (andM (andM (andM (andM (andM (andM (andM (ltTest ONE KK) nodupSrcM) nodupSymM)
    (ltTest XV KK)) (ltTest YV KK)) (notM (eqTest XV YV))) nodesOkM) (ltTest TV NN)) testsBoundsM) guardOkM

/-- `GInstance.isValid` on the machine. -/
def gValidM : Cmd := andM isValidM outsBoundsM

def nodupSrcV : List ℕ := FLAG :: (rangeV 0 ++ FLAG :: (rangeV 1 ++ FLAG :: dupV))
def nodupSymV : List ℕ := FLAG :: (rangeV 0 ++ FLAG :: (rangeV 1 ++ FLAG :: dupSymV))
def nodesOkV : List ℕ := FLAG :: (rangeV 0 ++ FLAG :: (FLAG :: ntV))
def testsBoundsV : List ℕ := FLAG :: (Lvars 0 ++ FLAG :: (FLAG :: tbV))
def guardOkV : List ℕ := Lvars 0 ++ FLAG :: gtV
def outsBoundsV : List ℕ := FLAG :: (Lvars 0 ++ FLAG :: (FLAG :: [FLAG]))

theorem nodupSrcV_safe : SafeVars nodupSrcV :=
  SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
    (SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupV_safe))))
theorem nodupSymV_safe : SafeVars nodupSymV :=
  SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
    (SafeVars.append (safeVars_rangeV 1 (by norm_num)) (SafeVars.cons safeVars_FLAG dupSymV_safe))))
theorem nodesOkV_safe : SafeVars nodesOkV :=
  SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_rangeV 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
    (SafeVars.cons safeVars_FLAG ntV_safe)))
theorem testsBoundsV_safe : SafeVars testsBoundsV :=
  SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
    (SafeVars.cons safeVars_FLAG tbV_safe)))
theorem guardOkV_safe : SafeVars guardOkV :=
  SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG gtV_safe)
theorem flagV_safe : SafeVars [FLAG] := fun x hx => by simp at hx; subst hx; exact safeVars_FLAG
theorem flag2V_safe : SafeVars (FLAG :: [FLAG]) := SafeVars.cons safeVars_FLAG flagV_safe
theorem outsBoundsV_safe : SafeVars outsBoundsV :=
  SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_Lvars 0 (by norm_num)) (SafeVars.cons safeVars_FLAG
    flag2V_safe))

/-- The variables written by `isValidM`. -/
def baseValidV : List ℕ :=
  [FLAG] ++ nodupSrcV ++ nodupSymV ++ [FLAG] ++ [FLAG] ++ (FLAG :: [FLAG]) ++ nodesOkV ++ [FLAG] ++
    testsBoundsV ++ guardOkV

/-- The variables written by `gValidM`. -/
def validV : List ℕ := baseValidV ++ outsBoundsV

theorem baseValidV_safe : SafeVars baseValidV :=
  SafeVars.append (SafeVars.append (SafeVars.append (SafeVars.append (SafeVars.append (SafeVars.append
    (SafeVars.append (SafeVars.append (SafeVars.append flagV_safe nodupSrcV_safe) nodupSymV_safe)
    flagV_safe) flagV_safe) flag2V_safe) nodesOkV_safe) flagV_safe) testsBoundsV_safe) guardOkV_safe

theorem validV_safe : SafeVars validV := SafeVars.append baseValidV_safe outsBoundsV_safe

/-- The step bound of `isValidM`. -/
def baseValidB (n : ℕ) : ℕ := 81 * n * n + 214 * n + 127

/-- The step bound of `gValidM`. -/
def validB (n : ℕ) : ℕ := 81 * n * n + 229 * n + 141

theorem isValidM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec isValidM baseValidV (baseValidB n) (InstCtx k g) (fun _ => g.base.isValid) := by
  have v1 := SafeVars.append flagV_safe nodupSrcV_safe
  have s1 := andC_spec (k2Test_spec k g) (nodupSrcM_spec k g n hn) flagV_safe
  have v2 := SafeVars.append v1 nodupSymV_safe
  have s2 := andC_spec s1 (nodupSymM_spec k g n hn) v1
  have v3 := SafeVars.append v2 flagV_safe
  have s3 := andC_spec s2 (xkTest_spec k g) v2
  have v4 := SafeVars.append v3 flagV_safe
  have s4 := andC_spec s3 (ykTest_spec k g) v3
  have v5 := SafeVars.append v4 flag2V_safe
  have s5 := andC_spec s4 (xyTest_spec k g) v4
  have v6 := SafeVars.append v5 nodesOkV_safe
  have s6 := andC_spec s5 (nodesOkM_spec k g n hn) v5
  have v7 := SafeVars.append v6 flagV_safe
  have s7 := andC_spec s6 (tnTest_spec k g) v6
  have v8 := SafeVars.append v7 testsBoundsV_safe
  have s8 := andC_spec s7 (testsBoundsM_spec k g n hn) v7
  have s9 := andC_spec s8 (guardOkM_spec k g n hn) v8
  unfold isValidM baseValidV baseValidB
  refine (s9.mono (fun x hx => hx) (by nlinarith) (fun m hm => hm)).congr (fun m _ => ?_)
  unfold Instance.isValid
  rfl

theorem gValidM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) :
    TestSpec gValidM validV (validB n) (InstCtx k g) (fun _ => g.isValid) := by
  have s := andC_spec (isValidM_spec k g n hn) (outsBoundsM_spec k g n hn) baseValidV_safe
  unfold gValidM validV validB
  refine (s.mono (fun x hx => hx) (by unfold baseValidB; nlinarith) (fun m hm => hm)).congr (fun m _ => ?_)
  unfold GInstance.isValid
  rfl

end DisequalityDispersion.Machine
