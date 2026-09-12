import MFlow
import Lean

/-! # The complete machine program and its running time

The phases (parsing, loading, validation, canonicalisation, the test scan, the network and
the flow) are assembled into one structured program `mainM`, compiled to the RAM program
`program := compile mainM 0`.  The I/O convention: the input bit string `bs` is placed in
memory by `inputMem bs` (cell `IN` holds the length, the cells above it the bits, every
other cell is `0`) and the machine starts at program counter `0`; it halts when the program
counter leaves the program, with the decision bit in the output cell `RES`.

The main results: `program` halts on every input `bs` with `RES = bitv (decideBits bs)`
(`program_run`), within a number of steps and a logarithmic cost bounded by a fixed
polynomial in `bs.length + 1` (`program_polynomial`), and its acceptance is exactly the
canonical language `StrictBits` (`program_accepts_iff`). -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded Flow

/-- The output cell. -/
def RES : ℕ := 39

theorem RES_eq : RES = 39 := rfl

/-! ### Sizes from the input length -/

theorem Sized.mono {n n' : ℕ} {g : GInstance} (h : Sized n g) (hn : n ≤ n') : Sized n' g :=
  ⟨le_trans h.srcs hn, le_trans h.syms hn, le_trans h.nodes hn, le_trans h.tests hn, le_trans h.outs hn,
    fun nd hnd f args e => le_trans (h.args nd hnd f args e) hn⟩

theorem sized_sizeG (g : GInstance) : Sized (sizeG g) g := by
  have hs := g.sizeInstance_le_sizeG
  refine ⟨le_trans g.base.sources_length_le hs, le_trans g.base.symbols_length_le hs,
    le_trans g.base.nodes_length_le hs, le_trans g.base.tests_length_le hs, g.outs_length_le, ?_⟩
  intro nd hnd f args e
  subst e
  have h1 := length_le_listC natC args (fun x _ => one_le_natC x)
  have h2 := g.base.nodeC_le_of_mem hnd
  simp only [nodeC] at h2
  omega

theorem sized_of_decode {bs : List Bool} {k : ℕ} {g : GInstance} (h : decodeInput bs = some (k, g)) :
    Sized bs.length g := by
  have := decodeInput_sizes bs k g h
  exact (sized_sizeG g).mono (by omega)

/-! ### Initialisation -/

/-- The constants, the parser registers, and the heap pointer above the input. -/
def initM : Cmd :=
  .seq (setc ONE 1) (.seq (setc ZERO 0) (.seq (setc INB (IN + 1)) (.seq (mov N IN)
    (.seq (setc HP (IN + 1)) (.seq (add HP HP N) (setc POS 0))))))

theorem initM_spec (bs : List Bool) (m : Mem) (hin : Input m bs) :
    ∃ m', Cmd.Exec initM m m' 7 ∧ PState m' bs ∧ m' POS = 0 := by
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = m.write ONE 1 := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2, m2 = m1.write ZERO 0 := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m3, m3 = m2.write INB (IN + 1) := ⟨_, rfl⟩
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = m3.write N bs.length := ⟨_, rfl⟩
  obtain ⟨m5, hm5⟩ : ∃ m5, m5 = m4.write HP (IN + 1) := ⟨_, rfl⟩
  obtain ⟨m6, hm6⟩ : ∃ m6, m6 = m5.write HP (IN + 1 + bs.length) := ⟨_, rfl⟩
  obtain ⟨m7, hm7⟩ : ∃ m7, m7 = m6.write POS 0 := ⟨_, rfl⟩
  have q3 : ∀ x, IN ≤ x → m3 x = m x := fun x hx => by
    rw [hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'), hm1, Mem.write_ne _ _ (by addr')]
  have q7 : ∀ x, IN ≤ x → m7 x = m x := fun x hx => by
    rw [hm7, Mem.write_ne _ _ (by addr'), hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'),
      hm4, Mem.write_ne _ _ (by addr'), q3 x hx]
  have e4 : Cmd.Exec (mov N IN) m3 m4 1 := by
    have := Exec.mov N IN m3; rwa [q3 IN le_rfl, hin.1, ← hm4] at this
  have h5a : m5 HP = IN + 1 := by rw [hm5, Mem.write_same]
  have h5b : m5 N = bs.length := by rw [hm5, Mem.write_ne _ _ (by addr'), hm4, Mem.write_same]
  have e6 : Cmd.Exec (add HP HP N) m5 m6 1 := by
    have := Exec.add HP HP N m5
    rw [h5a, h5b] at this
    rw [hm6]; exact this
  refine ⟨m7, ?_, ?_, by rw [hm7, Mem.write_same]⟩
  · have e1 : Cmd.Exec (setc ONE 1) m m1 1 := by rw [hm1]; exact Exec.setc _ _ _
    have e2 : Cmd.Exec (setc ZERO 0) m1 m2 1 := by rw [hm2]; exact Exec.setc _ _ _
    have e3 : Cmd.Exec (setc INB (IN + 1)) m2 m3 1 := by rw [hm3]; exact Exec.setc _ _ _
    have e5 : Cmd.Exec (setc HP (IN + 1)) m4 m5 1 := by rw [hm5]; exact Exec.setc _ _ _
    have e7 : Cmd.Exec (setc POS 0) m6 m7 1 := by rw [hm7]; exact Exec.setc _ _ _
    exact Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.seq e5
      (Cmd.Exec.seq e6 e7)))))
  · refine ⟨⟨by rw [q7 IN le_rfl]; exact hin.1, fun i hi => by rw [q7 _ (by omega)]; exact hin.2 i hi⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm7, Mem.write_ne _ _ (by addr'), hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'),
        hm4, Mem.write_same]
    · rw [hm7, Mem.write_ne _ _ (by addr'), hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'),
        hm4, Mem.write_ne _ _ (by addr'), hm3, Mem.write_same]
    · rw [hm7, Mem.write_ne _ _ (by addr'), hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'),
        hm4, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_ne _ _ (by addr'),
        hm1, Mem.write_same]
    · rw [hm7, Mem.write_ne _ _ (by addr'), hm6, Mem.write_ne _ _ (by addr'), hm5, Mem.write_ne _ _ (by addr'),
        hm4, Mem.write_ne _ _ (by addr'), hm3, Mem.write_ne _ _ (by addr'), hm2, Mem.write_same]
    · rw [hm7, Mem.write_ne _ _ (by addr'), hm6, Mem.write_same]

/-! ### The decision after parsing -/

/-- The decision on the parsed `(k, g)` (record at `VAL`): load, `2 ≤ k`, validate,
canonicalise, the test scan, the network, the flow, `k + 1 ≤ ρ`. -/
def decideM : Cmd :=
  .seq loadInstM
    (.ite (.lt ONE KV)
      (.seq gValidM
        (.ite (.eq FLAG ONE)
          (.seq canonIdsM (.seq testsDistinctM
            (.ite (.eq FLAG ONE)
              (.seq netM (.seq rhoM (.seq (ltTest KV VAL) (mov RES FLAG))))
              (setc RES 0))))
          (setc RES 0)))
      (setc RES 0))

/-- The step bound of `decideM` in terms of the size bound `n`. -/
def decideB (n : ℕ) : ℕ :=
  42 + (validB n + ((n * (canonB n + 8) + 8 + 1) + (n * (20 + 12) + 11) + (netB n + rhoB n + 3 + 1)) + 20)

theorem decideM_spec (k : ℕ) (g : GInstance) (n : ℕ) (hn : Sized n g) (m : Mem) (hctx : Ctx m)
    (hrep : RepKG m IN (m HP) (m VAL) (k, g)) :
    ∃ m' kk, Cmd.Exec decideM m m' kk ∧ kk ≤ decideB n ∧ m' RES = bitv (g.strictDecideP k) := by
  obtain ⟨m1, e1, ag1, hI1⟩ := loadInstM_spec k g m hctx hrep
  have hone1 : m1 ONE = 1 := hI1.ctx.1
  have hkv1 : m1 KV = k := hI1.kv
  have hhp1 : 200 ≤ m1 HP := hI1.ctx.2.2
  by_cases hk : 2 ≤ k
  · have hc1 : (Cond.lt ONE KV).eval m1 = true := by simp [Cond.eval, hone1, hkv1]; omega
    -- validation
    obtain ⟨m2, k2, e2, hk2, ag2, hfl2⟩ := gValidM_spec k g n hn m1 hI1
    have hI2 : InstCtx k g m2 := hI1.of_agree ag2 validV_safe
    have hone2 : m2 ONE = 1 := hI2.ctx.1
    dsimp only at hfl2
    by_cases hv : g.isValid = true
    · have hc2 : (Cond.eq FLAG ONE).eval m2 = true := by simp [Cond.eval, hfl2, hone2, hv]
      -- canonicalisation and the test scan
      obtain ⟨m3, k3, e3, hk3, ag3, hIds3⟩ := canonIdsM_spec k g n hn m2 hI2
      obtain ⟨m4, k4, e4, hk4, ag4, hfl4⟩ := testsDistinctM_spec k g n hn m3 hIds3
      have hIds4 : IdsCtx k g m4 :=
        IdsCtx.stableP (SafeVars.cons safeVars_FLAG (SafeVars.append (safeVars_Lvars 0 (by norm_num))
          (SafeVars.cons safeVars_FLAG (SafeVars.cons safeVars_FLAG dtV_safe)))) (by decide) m3 m4 hIds3 ag4
      have hone4 : m4 ONE = 1 := hIds4.1.ctx.1
      dsimp only at hfl4
      by_cases hd : g.base.testsDistinct g.base.canonIds = true
      · have hc4 : (Cond.eq FLAG ONE).eval m4 = true := by simp [Cond.eval, hfl4, hone4, hd]
        -- the network and the flow
        obtain ⟨m5, k5, e5, hk5, ag5, hN5⟩ := netM_spec k g n hn m4 hIds4
        obtain ⟨m6, k6, e6, hk6, ag6, hN6, hval6⟩ := rhoM_spec k g n hn m5 hN5
        have hkv6 : m6 KV = k := hN6.1.1.1.1.kv
        obtain ⟨m7, k7, e7, hk7, ag7, hfl7⟩ := ltTest_spec KV VAL (fun _ => True) m6 trivial
        have hhp6 : 200 ≤ m6 HP := hN6.1.1.1.1.ctx.2.2
        obtain ⟨m8, hm8⟩ : ∃ m8, m8 = m7.write RES (m7 FLAG) := ⟨_, rfl⟩
        have e8 : Cmd.Exec (mov RES FLAG) m7 m8 1 := by rw [hm8]; exact Exec.mov _ _ _
        refine ⟨m8, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc2
          (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.ite_true hc4 (Cmd.Exec.seq e5 (Cmd.Exec.seq e6
            (Cmd.Exec.seq e7 e8))))))))), by unfold decideB; omega, ?_⟩
        rw [hm8, Mem.write_same, hfl7]
        dsimp only
        rw [hkv6, hval6]
        simp only [GInstance.strictDecideP, hk, hv, hd, if_true]
        rfl
      · have hc4 : (Cond.eq FLAG ONE).eval m4 = false := by simp [Cond.eval, hfl4, hone4, hd]
        refine ⟨m4.write RES 0, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc2
          (Cmd.Exec.seq e3 (Cmd.Exec.seq e4 (Cmd.Exec.ite_false hc4 (Exec.setc _ _ _))))))), by unfold decideB; omega, ?_⟩
        rw [Mem.write_same]
        simp [GInstance.strictDecideP, hk, hv, hd]
    · have hc2 : (Cond.eq FLAG ONE).eval m2 = false := by simp [Cond.eval, hfl2, hone2, hv]
      refine ⟨m2.write RES 0, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_true hc1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_false hc2
        (Exec.setc _ _ _)))), by unfold decideB; omega, ?_⟩
      rw [Mem.write_same]
      simp [GInstance.strictDecideP, hk, hv]
  · have hc1 : (Cond.lt ONE KV).eval m1 = false := by simp [Cond.eval, hone1, hkv1]; omega
    refine ⟨m1.write RES 0, _, Cmd.Exec.seq e1 (Cmd.Exec.ite_false hc1 (Exec.setc _ _ _)), by unfold decideB; omega, ?_⟩
    rw [Mem.write_same]
    simp [GInstance.strictDecideP, hk]

/-! ### The whole program -/

/-- Initialise, parse, and decide (rejecting when the input does not parse). -/
def mainM : Cmd := .seq initM (.seq decodeInputM (.ite (.eq OK ONE) decideM (setc RES 0)))

/-- The step bound of `mainM` in terms of the input length `n`. -/
def mainB (n : ℕ) : ℕ := 7 + (2100 * (n + 1) ^ 3 + 5) + (decideB n + 3)

theorem mainM_spec (bs : List Bool) (m : Mem) (hin : Input m bs) :
    ∃ m' kk, Cmd.Exec mainM m m' kk ∧ kk ≤ mainB bs.length ∧ m' RES = bitv (decideBits bs) := by
  obtain ⟨m1, e1, hs1, hpos1⟩ := initM_spec bs m hin
  obtain ⟨m2, k2, e2, hk2, pres2, hs2, hhp2, res2⟩ := decodeInputM_spec m1 bs hs1 hpos1
  unfold InputResult at res2
  unfold decideBits
  cases hd : decodeInput bs with
  | none =>
      rw [hd] at res2
      have hc : (Cond.eq OK ONE).eval m2 = false := by simp [Cond.eval, res2, hs2.one]
      refine ⟨m2.write RES 0, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_false hc (Exec.setc _ _ _))),
        by unfold mainB; omega, by rw [Mem.write_same]; rfl⟩
  | some kg =>
      obtain ⟨k, g⟩ := kg
      rw [hd] at res2
      obtain ⟨hok, hrep⟩ := res2
      have hc : (Cond.eq OK ONE).eval m2 = true := by simp [Cond.eval, hok, hs2.one]
      have hctx2 : Ctx m2 := ⟨hs2.one, hs2.zero, by have := hs2.hp; omega⟩
      have hrep' : RepKG m2 IN (m2 HP) (m2 VAL) (k, g) :=
        goodRep_KG.mono m2 (m1 HP) (m2 HP) IN (m2 HP) _ _ hrep (by have := hs1.hp; omega) le_rfl
      obtain ⟨m3, k3, e3, hk3, hres3⟩ := decideM_spec k g bs.length (sized_of_decode hd) m2 hctx2 hrep'
      exact ⟨m3, _, Cmd.Exec.seq e1 (Cmd.Exec.seq e2 (Cmd.Exec.ite_true hc e3)), by unfold mainB; omega, hres3⟩

/-! ### The RAM program -/

/-- The RAM program: `mainM` compiled at position `0`. -/
def program : List Instr := Cmd.compile mainM 0

/-- The initial configuration on input `bs`: program counter `0`, the input in memory. -/
def initCfg (bs : List Bool) : Cfg := ⟨0, inputMem bs⟩

theorem program_codeAt : Cmd.CodeAt program 0 (Cmd.compile mainM 0) := by
  intro i _; simp [program]

theorem program_halted (m : Mem) : Halted program ⟨Cmd.len mainM, m⟩ := by
  unfold Halted step
  have : program[Cmd.len mainM]? = none := by
    rw [List.getElem?_eq_none_iff]
    simp [program, Cmd.compile_length]
  simp [this]

/-- **The program halts on every input with the decision in `RES`**, within `mainB bs.length`
steps. -/
theorem program_run (bs : List Bool) :
    ∃ (m' : Mem) (n t : ℕ), Run program (initCfg bs) ⟨Cmd.len mainM, m'⟩ n t ∧
      Halted program ⟨Cmd.len mainM, m'⟩ ∧ m' RES = bitv (decideBits bs) ∧ n ≤ mainB bs.length := by
  obtain ⟨m', kk, e, hk, hres⟩ := mainM_spec bs (inputMem bs) (inputMem_input bs)
  obtain ⟨t, r⟩ := Cmd.compile_correct e program 0 program_codeAt
  exact ⟨m', kk, t, by simpa [initCfg] using r, program_halted m', hres, hk⟩

/-! ### The constants of the program -/

/-- The largest immediate constant of a structured program. -/
def Cmd.constMax : Cmd → ℕ
  | .prim p => p.constOf'
  | .seq c₁ c₂ => max c₁.constMax c₂.constMax
  | .ite _ c₁ c₂ => max c₁.constMax c₂.constMax
  | .loop _ c => c.constMax

theorem foldr_max_append (l l' : List ℕ) : (l ++ l').foldr max 0 = max (l.foldr max 0) (l'.foldr max 0) := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.cons_append, List.foldr_cons, ih, List.foldr_cons, Nat.max_assoc]

theorem constBound_append (P Q : List Instr) : constBound (P ++ Q) = max (constBound P) (constBound Q) := by
  unfold constBound; rw [List.map_append]; exact foldr_max_append _ _

theorem constBound_cons (i : Instr) (P : List Instr) : constBound (i :: P) = max i.constOf (constBound P) := rfl

theorem constBound_nil : constBound [] = 0 := rfl

theorem constBound_compile (c : Cmd) (s : ℕ) : constBound (Cmd.compile c s) = c.constMax := by
  induction c generalizing s with
  | prim p => cases p <;> simp [Cmd.compile, constBound, Cmd.constMax, Instr.constOf, Prim.constOf']
  | seq c₁ c₂ ih₁ ih₂ => rw [Cmd.compile, constBound_append, ih₁, ih₂]; rfl
  | ite b c₁ c₂ ih₁ ih₂ =>
      rw [Cmd.compile, constBound_cons, constBound_cons, constBound_append, constBound_cons, ih₁, ih₂]
      simp [Cmd.constMax, Instr.constOf]
  | loop b c ih =>
      rw [Cmd.compile, constBound_cons, constBound_cons, constBound_append, ih, constBound_cons, constBound_nil]
      simp [Cmd.constMax, Instr.constOf]

theorem mainM_constMax : mainM.constMax ≤ 201 := by decide +kernel

theorem program_constBound : bits (constBound program) ≤ 8 := by
  unfold program
  rw [constBound_compile]
  exact le_trans (bits_mono mainM_constMax) (bits_le_of_lt_pow (by norm_num))

/-! ### Polynomial bounds -/

/-- `f` is bounded by a polynomial in `n + 1`. -/
def PolyB (f : ℕ → ℕ) : Prop := ∃ C c, 1 ≤ C ∧ ∀ n, f n ≤ C * (n + 1) ^ c

theorem PolyB.const (a : ℕ) : PolyB (fun _ => a) :=
  ⟨a + 1, 0, by omega, fun _ => by simp⟩

theorem PolyB.id : PolyB (fun n => n) := ⟨1, 1, le_rfl, fun n => by simp⟩

theorem PolyB.pow_succ (k : ℕ) : PolyB (fun n => (n + 1) ^ k) := ⟨1, k, le_rfl, fun n => by simp⟩

theorem PolyB.add {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB (fun n => f n + g n) := by
  obtain ⟨C₁, c₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, c₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max c₁ c₂, by omega, fun n => ?_⟩
  have e1 : (n + 1) ^ c₁ ≤ (n + 1) ^ max c₁ c₂ := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e2 : (n + 1) ^ c₂ ≤ (n + 1) ^ max c₁ c₂ := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f n + g n ≤ C₁ * (n + 1) ^ c₁ + C₂ * (n + 1) ^ c₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ C₁ * (n + 1) ^ max c₁ c₂ + C₂ * (n + 1) ^ max c₁ c₂ :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (C₁ + C₂) * (n + 1) ^ max c₁ c₂ := by ring

theorem PolyB.mul {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB (fun n => f n * g n) := by
  obtain ⟨C₁, c₁, hC₁, h₁⟩ := hf
  obtain ⟨C₂, c₂, hC₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, c₁ + c₂, Nat.one_le_iff_ne_zero.mpr (by positivity), fun n => ?_⟩
  calc f n * g n ≤ (C₁ * (n + 1) ^ c₁) * (C₂ * (n + 1) ^ c₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = C₁ * C₂ * (n + 1) ^ (c₁ + c₂) := by ring

theorem PolyB.of_le {f g : ℕ → ℕ} (hg : PolyB g) (h : ∀ n, f n ≤ g n) : PolyB f := by
  obtain ⟨C, c, hC, hb⟩ := hg
  exact ⟨C, c, hC, fun n => le_trans (h n) (hb n)⟩

theorem PolyB.sub_left {f g : ℕ → ℕ} (hf : PolyB f) : PolyB (fun n => f n - g n) :=
  hf.of_le (fun n => Nat.sub_le _ _)

theorem PolyB.eta {f : ℕ → ℕ} (hf : PolyB f) : PolyB (fun n => f n) := hf

open Lean Elab Tactic Meta in
/-- Close a goal `PolyB (fun n => e)` by the closure lemmas, following the syntax of `e`;
applications `g n` of named bound functions are closed by hypotheses `PolyB g`. -/
partial def polybCore (goal : MVarId) : TacticM Unit := goal.withContext do
  let t := (← instantiateMVars (← goal.getType)).consumeMData
  let some f := t.app1? ``PolyB | throwError "polyb: goal is not `PolyB _`: {t}"
  let f := (← instantiateMVars f).consumeMData
  let .lam nm dom body bi := f | throwError "polyb: not a lambda: {f}"
  let mkFun (e : Expr) : Expr := .lam nm dom e bi
  if !body.hasLooseBVars then
    let gs ← goal.apply (mkApp (mkConst ``PolyB.const) body)
    unless gs.isEmpty do throwError "polyb: const left goals"
    return
  if body == .bvar 0 then
    let gs ← goal.apply (mkConst ``PolyB.id)
    unless gs.isEmpty do throwError "polyb: id left goals"
    return
  -- a hypothesis with syntactically the same body
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ht := (← instantiateMVars h.type).consumeMData
    if let some f' := ht.app1? ``PolyB then
      if let .lam _ _ body' _ := f'.consumeMData then
        if body' == body then
          let gs ← goal.apply h.toExpr
          unless gs.isEmpty do throwError "polyb: hypothesis left goals"
          return
  match body.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let gs ← goal.apply (mkAppN (mkConst ``PolyB.add) #[mkFun a, mkFun b])
      for g in gs do polybCore g
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let gs ← goal.apply (mkAppN (mkConst ``PolyB.mul) #[mkFun a, mkFun b])
      for g in gs do polybCore g
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      let gs ← goal.apply (mkAppN (mkConst ``PolyB.sub_left) #[mkFun a, mkFun b])
      for g in gs do polybCore g
  | (``HPow.hPow, #[_, _, _, _, _, e]) =>
      if e.hasLooseBVars then throwError "polyb: exponent depends on n"
      let gs ← goal.apply (mkApp (mkConst ``PolyB.pow_succ) e)
      unless gs.isEmpty do throwError "polyb: pow left goals"
  | (_, _) =>
      let .app g (.bvar 0) := body | throwError "polyb: unsupported body {body}"
      if g.hasLooseBVars then throwError "polyb: unsupported body {body}"
      let target := mkApp (mkConst ``PolyB) g
      for h in ← getLCtx do
        if h.isImplementationDetail then continue
        if ← isDefEq (← instantiateMVars h.type).consumeMData target then
          let gs ← goal.apply (mkAppN (mkConst ``PolyB.eta) #[g, h.toExpr])
          unless gs.isEmpty do throwError "polyb: eta left goals"
          return
      throwError "polyb: no hypothesis `PolyB {g}`"

open Lean Elab Tactic in
/-- `polyb` closes `PolyB (fun n => e)` for `e` built from `n`, constants, `+`, `*`, `∸`,
`(n + 1) ^ k` and named bound functions with `PolyB` hypotheses in context. -/
elab "polyb" : tactic => do
  let goal ← getMainGoal
  polybCore goal
  replaceMainGoal []

theorem polyB_arcBound : PolyB arcBound := by unfold arcBound; polyb
theorem polyB_nodeBound : PolyB nodeBound := by unfold nodeBound; polyb
theorem polyB_seenBound : PolyB seenBound := by unfold seenBound; polyb
theorem polyB_flowBound : PolyB flowBound := by
  have := polyB_arcBound; unfold flowBound; polyb
theorem polyB_frontB : PolyB frontB := by
  have := polyB_arcBound; have := polyB_nodeBound; have := polyB_seenBound; have := polyB_flowBound
  unfold frontB; polyb
theorem polyB_layerBodyB : PolyB layerBodyB := by
  have := polyB_nodeBound; have := polyB_seenBound; have := polyB_frontB
  unfold layerBodyB; polyb
theorem polyB_layersB : PolyB layersB := by
  have := polyB_layerBodyB; unfold layersB; polyb
theorem polyB_descB : PolyB descB := by
  have := polyB_arcBound; have := polyB_flowBound; unfold descB; polyb
theorem polyB_consPathB : PolyB (fun n => consPathB (2 * n + 3)) := by unfold consPathB; polyb
theorem polyB_pathB : PolyB pathB := by
  have := polyB_nodeBound; have := polyB_descB; have := polyB_consPathB; unfold pathB; polyb
theorem polyB_augPathB : PolyB augPathB := by
  have := polyB_pathB; unfold augPathB; polyb
theorem polyB_stepsB : PolyB stepsB := by unfold stepsB; polyb
theorem polyB_keepB : PolyB keepB := by unfold keepB; polyb
theorem polyB_augmentB : PolyB augmentB := by
  have := polyB_flowBound; have := polyB_keepB; have := polyB_arcBound; unfold augmentB; polyb
theorem polyB_ffBodyB : PolyB ffBodyB := by
  have := polyB_layersB; have := polyB_seenBound; have := polyB_augPathB; have := polyB_stepsB
  have := polyB_augmentB; unfold ffBodyB; polyb
theorem polyB_ffB : PolyB ffB := by
  have := polyB_arcBound; have := polyB_ffBodyB; unfold ffB; polyb
theorem polyB_countB : PolyB countB := by
  have := polyB_flowBound; unfold countB; polyb
theorem polyB_rhoB : PolyB rhoB := by
  have := polyB_ffB; have := polyB_countB; unfold rhoB; polyb

theorem polyB_validB : PolyB validB := by unfold validB; polyb
theorem polyB_sigB : PolyB sigB := by unfold sigB; polyb
theorem polyB_canonB : PolyB canonB := by have := polyB_sigB; unfold canonB; polyb
theorem polyB_netB : PolyB netB := by unfold netB; polyb
theorem polyB_decideB : PolyB decideB := by
  have := polyB_validB; have := polyB_canonB; have := polyB_netB; have := polyB_rhoB
  unfold decideB; polyb
theorem polyB_mainB : PolyB mainB := by have := polyB_decideB; unfold mainB; polyb

/-- The logarithmic-cost bound in terms of the input length: a run of at most `mainB n` steps
from an input of `n` bits (values of at most `bits n + 1 ≤ n + 1` bits, program constants of
at most `8` bits) costs at most `mainB n * (1 + 2 * (n + 9 + mainB n))`. -/
def costB (n : ℕ) : ℕ := mainB n * (1 + 2 * (n + 9 + mainB n))

theorem polyB_costB : PolyB costB := by have := polyB_mainB; unfold costB; polyb

/-! ### The running-time theorem -/

/-- **Polynomial running time on the RAM.** There are constants `C ≥ 1` and `c` such that on
every bit string `bs`, the program halts with the decision `decideBits bs` in `RES` within
`C * (bs.length + 1) ^ c` steps and, under the logarithmic cost criterion, within total cost
`C * (bs.length + 1) ^ c`. -/
theorem program_polynomial :
    ∃ (C c : ℕ), 1 ≤ C ∧ ∀ bs : List Bool, ∃ (m' : Mem) (n t : ℕ),
      Run program (initCfg bs) ⟨Cmd.len mainM, m'⟩ n t ∧ Halted program ⟨Cmd.len mainM, m'⟩ ∧
      m' RES = bitv (decideBits bs) ∧ n ≤ C * (bs.length + 1) ^ c ∧ t ≤ C * (bs.length + 1) ^ c := by
  obtain ⟨C, c, hC, hb⟩ := polyB_costB
  refine ⟨C, c, hC, fun bs => ?_⟩
  obtain ⟨m', n, t, r, hh, hres, hn⟩ := program_run bs
  refine ⟨m', n, t, r, hh, hres, ?_, ?_⟩
  · have h1 : n ≤ costB bs.length := by
      unfold costB
      have : 1 ≤ 1 + 2 * (bs.length + 9 + mainB bs.length) := by omega
      calc n ≤ mainB bs.length := hn
        _ = mainB bs.length * 1 := (Nat.mul_one _).symm
        _ ≤ mainB bs.length * (1 + 2 * (bs.length + 9 + mainB bs.length)) := Nat.mul_le_mul_left _ this
    exact le_trans h1 (hb _)
  · have hbits : bits bs.length ≤ bs.length := bits_le_self _
    have hm : Bounded (initCfg bs).mem (bits bs.length + 9) :=
      (inputMem_bounded bs).mono (by omega)
    have hP : bits (constBound program) ≤ bits bs.length + 9 := le_trans program_constBound (by omega)
    have ht := Run.cost_le hm hP r
    have h2 : t ≤ costB bs.length := by
      unfold costB
      calc t ≤ n * (1 + 2 * (bits bs.length + 9 + n)) := ht
        _ ≤ mainB bs.length * (1 + 2 * (bs.length + 9 + mainB bs.length)) :=
          Nat.mul_le_mul hn (by omega)
    exact le_trans h2 (hb _)

/-- **Acceptance.** The program accepts (`RES = 1`) exactly the canonical language
`StrictBits`: the encodings `encodeInput k g` with `2 ≤ k` and `g.Strict k`. -/
theorem program_accepts_iff (bs : List Bool) (m' : Mem) (n t : ℕ)
    (r : Run program (initCfg bs) ⟨Cmd.len mainM, m'⟩ n t) : m' RES = 1 ↔ StrictBits bs := by
  obtain ⟨m'', n', t', r', _, hres, _⟩ := program_run bs
  have hu := Run.halted_unique r r' (program_halted m') (program_halted m'')
  rw [← decideBits_iff_StrictBits]
  have hm : m' = m'' := by
    have := congrArg Cfg.mem hu.1
    simpa using this
  rw [hm, hres]
  cases decideBits bs <;> simp [bitv]

end DisequalityDispersion.Machine
