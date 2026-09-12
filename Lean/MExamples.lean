import MMain
import GeneralExamples

/-! # Machine-level examples

An executable, fuelled interpreter of the RAM (`runFuel`, proved sound with respect to `Run`),
used for kernel-checked runs of the compiled program on tiny inputs, and an array-backed
interpreter (`runA`, proved to simulate `runFuel`) used to evaluate the program on the
regression instances of the pure development with `#eval`. -/

namespace DisequalityDispersion.Machine

open DisequalityDispersion.Encoded

/-! ### A fuelled interpreter -/

/-- Fuelled execution: `(final configuration, steps, cost, halted?)`. -/
def runFuel (P : List Instr) : ℕ → Cfg → ℕ → ℕ → Cfg × ℕ × ℕ × Bool
  | 0, c, n, t => (c, n, t, false)
  | f + 1, c, n, t =>
    match step P c with
    | none => (c, n, t, true)
    | some (c', k) => runFuel P f c' (n + 1) (t + k)

theorem runFuel_sound (P : List Instr) : ∀ (f : ℕ) (c : Cfg) (n t : ℕ) (c' : Cfg) (n' t' : ℕ),
    runFuel P f c n t = (c', n', t', true) →
      ∃ n₀ t₀, Run P c c' n₀ t₀ ∧ n' = n + n₀ ∧ t' = t + t₀ ∧ Halted P c'
  | 0, c, n, t, c', n', t', h => by simp [runFuel] at h
  | f + 1, c, n, t, c', n', t', h => by
      simp only [runFuel] at h
      cases hs : step P c with
      | none =>
          rw [hs] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, _⟩ := h
          exact ⟨0, 0, Run.refl c, by omega, by omega, hs⟩
      | some ck =>
          obtain ⟨c₁, k⟩ := ck
          rw [hs] at h
          obtain ⟨n₀, t₀, r, hn, ht, hh⟩ := runFuel_sound P f c₁ (n + 1) (t + k) c' n' t' h
          exact ⟨n₀ + 1, k + t₀, Run.step hs r, by omega, by omega, hh⟩

/-- Kernel-checked run on the empty input: the parser rejects, `RES = 0`. -/
theorem run_empty : (runFuel program 100 (initCfg []) 0 0).2.2.2 = true ∧
    (runFuel program 100 (initCfg []) 0 0).1.mem RES = 0 := by decide +kernel

/-- Kernel-checked run on the input `[1]` (a truncated code): rejected. -/
theorem run_one : (runFuel program 200 (initCfg [true]) 0 0).2.2.2 = true ∧
    (runFuel program 200 (initCfg [true]) 0 0).1.mem RES = 0 := by decide +kernel

/-! ### An array-backed interpreter for evaluation -/

/-- Read with default `0`. -/
def aget (a : Array ℕ) (x : ℕ) : ℕ := a.getD x 0

/-- Write, growing the array as needed. -/
def aset (a : Array ℕ) (x v : ℕ) : Array ℕ :=
  (if x < a.size then a else a ++ Array.replicate (x + 1 - a.size) 0).set! x v

theorem aget_extend (a : Array ℕ) (k y : ℕ) : aget (a ++ Array.replicate k 0) y = aget a y := by
  unfold aget
  simp only [Array.getD_eq_getD_getElem?]
  by_cases hy : y < a.size
  · rw [Array.getElem?_append_left hy]
  · rw [Array.getElem?_append_right (by omega), Array.getElem?_replicate, Array.getElem?_eq_none_iff.mpr (by omega)]
    split <;> rfl

theorem aget_aset (a : Array ℕ) (x v y : ℕ) : aget (aset a x v) y = if y = x then v else aget a y := by
  unfold aset
  have key : ∀ (a' : Array ℕ), x < a'.size → (∀ z, aget a' z = aget a z) →
      aget (a'.set! x v) y = if y = x then v else aget a y := by
    intro a' hx hz
    rw [Array.set!_eq_setIfInBounds]
    unfold aget
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
    by_cases hy : y = x
    · subst hy; simp [hx]
    · rw [if_neg (Ne.symm hy), if_neg hy, ← Array.getD_eq_getD_getElem?]; exact hz y
  by_cases h : x < a.size
  · rw [if_pos h]; exact key a h (fun _ => rfl)
  · rw [if_neg h]; exact key _ (by simp; omega) (fun z => aget_extend a _ z)

/-- Correspondence between a memory and its array representation. -/
def Corr (m : Mem) (a : Array ℕ) : Prop := ∀ x, m x = aget a x

theorem Corr.write {m : Mem} {a : Array ℕ} (h : Corr m a) (x v : ℕ) : Corr (m.write x v) (aset a x v) := by
  intro y
  rw [aget_aset]
  unfold Mem.write
  by_cases hy : y = x
  · rw [if_pos hy, if_pos hy]
  · rw [if_neg hy, if_neg hy]; exact h y

/-- The primitives on arrays. -/
def Prim.execA : Prim → Array ℕ → Array ℕ
  | .const x c, a => aset a x c
  | .mov x y, a => aset a x (aget a y)
  | .load x y, a => aset a x (aget a (aget a y))
  | .store x y, a => aset a (aget a x) (aget a y)
  | .add x y z, a => aset a x (aget a y + aget a z)
  | .sub x y z, a => aset a x (aget a y - aget a z)

def Prim.costA : Prim → Array ℕ → ℕ
  | .const _ c, _ => 1 + bits c
  | .mov _ y, a => 1 + bits (aget a y)
  | .load _ y, a => 1 + bits (aget a y) + bits (aget a (aget a y))
  | .store x y, a => 1 + bits (aget a x) + bits (aget a y)
  | .add _ y z, a => 1 + bits (aget a y) + bits (aget a z)
  | .sub _ y z, a => 1 + bits (aget a y) + bits (aget a z)

def Cond.evalA : Cond → Array ℕ → Bool
  | .lt x y, a => decide (aget a x < aget a y)
  | .eq x y, a => decide (aget a x = aget a y)

def Cond.costA : Cond → Array ℕ → ℕ
  | .lt x y, a => 1 + bits (aget a x) + bits (aget a y)
  | .eq x y, a => 1 + bits (aget a x) + bits (aget a y)

theorem Prim.execA_corr {m : Mem} {a : Array ℕ} (h : Corr m a) (p : Prim) : Corr (p.exec m) (p.execA a) := by
  cases p <;> simp only [Prim.exec, Prim.execA, h _] <;> exact h.write _ _

theorem Prim.costA_corr {m : Mem} {a : Array ℕ} (h : Corr m a) (p : Prim) : p.cost m = p.costA a := by
  cases p <;> simp only [Prim.cost, Prim.costA, h _]

theorem Cond.evalA_corr {m : Mem} {a : Array ℕ} (h : Corr m a) (b : Cond) : b.eval m = b.evalA a := by
  cases b <;> simp only [Cond.eval, Cond.evalA, h _]

theorem Cond.costA_corr {m : Mem} {a : Array ℕ} (h : Corr m a) (b : Cond) : b.cost m = b.costA a := by
  cases b <;> simp only [Cond.cost, Cond.costA, h _]

/-- Array-backed configurations. -/
structure ACfg where
  pc : ℕ
  mem : Array ℕ

def ACfg.Corr (c : Cfg) (ac : ACfg) : Prop := c.pc = ac.pc ∧ Machine.Corr c.mem ac.mem

/-- One step on array configurations (the program as an array). -/
def stepA (P : Array Instr) (c : ACfg) : Option (ACfg × ℕ) :=
  match P[c.pc]? with
  | none => none
  | some .halt => none
  | some (.prim p) => some (⟨c.pc + 1, p.execA c.mem⟩, p.costA c.mem)
  | some (.jmp l) => some (⟨l, c.mem⟩, 1)
  | some (.jcond b l) => some (⟨if b.evalA c.mem then l else c.pc + 1, c.mem⟩, b.costA c.mem)

theorem stepA_corr {P : List Instr} {c : Cfg} {ac : ACfg} (h : ACfg.Corr c ac) :
    (step P c = none ↔ stepA P.toArray ac = none) ∧
    ∀ c' k, step P c = some (c', k) → ∃ ac', stepA P.toArray ac = some (ac', k) ∧ ACfg.Corr c' ac' := by
  obtain ⟨hpc, hm⟩ := h
  have hP : P.toArray[ac.pc]? = P[c.pc]? := by rw [hpc]; simp
  unfold step stepA
  rw [hP]
  cases hi : P[c.pc]? with
  | none => exact ⟨by simp, fun c' k h => by simp at h⟩
  | some i =>
      cases i with
      | prim p =>
          refine ⟨by simp, fun c' k h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨ac.pc + 1, p.execA ac.mem⟩, ?_, ?_⟩
          · rw [Prim.costA_corr hm]
          · exact ⟨by simp [hpc], Prim.execA_corr hm p⟩
      | jmp l =>
          refine ⟨by simp, fun c' k h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨l, ac.mem⟩, rfl, rfl, hm⟩
      | jcond b l =>
          refine ⟨by simp, fun c' k h => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨if b.evalA ac.mem then l else ac.pc + 1, ac.mem⟩, ?_, ?_⟩
          · rw [Cond.costA_corr hm]
          · exact ⟨by simp only [Cond.evalA_corr hm, hpc], hm⟩
      | halt => exact ⟨by simp, fun c' k h => by simp at h⟩

/-- Fuelled array execution. -/
def runA (P : Array Instr) : ℕ → ACfg → ℕ → ℕ → ACfg × ℕ × ℕ × Bool
  | 0, c, n, t => (c, n, t, false)
  | f + 1, c, n, t =>
    match stepA P c with
    | none => (c, n, t, true)
    | some (c', k) => runA P f c' (n + 1) (t + k)

theorem runA_corr (P : List Instr) : ∀ (f : ℕ) (c : Cfg) (ac : ACfg) (n t : ℕ), ACfg.Corr c ac →
    ∀ ac' n' t' b, runA P.toArray f ac n t = (ac', n', t', b) →
      ∃ c', runFuel P f c n t = (c', n', t', b) ∧ ACfg.Corr c' ac'
  | 0, c, ac, n, t, h, ac', n', t', b, hr => by
      simp only [runA, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
      exact ⟨c, rfl, h⟩
  | f + 1, c, ac, n, t, h, ac', n', t', b, hr => by
      simp only [runA] at hr
      obtain ⟨h1, h2⟩ := stepA_corr (P := P) h
      cases hs : step P c with
      | none =>
          rw [h1.mp hs] at hr
          simp only [Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
          exact ⟨c, by simp [runFuel, hs], h⟩
      | some ck =>
          obtain ⟨c₁, k⟩ := ck
          obtain ⟨ac₁, hs', hc₁⟩ := h2 c₁ k hs
          rw [hs'] at hr
          obtain ⟨c', hr', hc'⟩ := runA_corr P f c₁ ac₁ (n + 1) (t + k) hc₁ ac' n' t' b hr
          exact ⟨c', by simp [runFuel, hs, hr'], hc'⟩

/-- The input array: cell `IN` holds the length, the bits follow. -/
def inputArr (bs : List Bool) : Array ℕ :=
  (Array.replicate IN 0).push bs.length ++ (bs.map (fun b => if b then 1 else 0)).toArray

theorem inputArr_corr (bs : List Bool) : Corr (inputMem bs) (inputArr bs) := by
  intro x
  unfold inputMem inputArr aget
  rw [Array.getD_eq_getD_getElem?]
  by_cases hlt : x < IN + 1
  · rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_push, Array.size_replicate,
      Array.getElem?_replicate]
    by_cases h1 : x = IN
    · subst h1; simp
    · rw [if_neg h1, if_neg h1, if_pos (show x < IN by omega),
        if_neg (show ¬ (IN < x ∧ x ≤ IN + bs.length) by omega)]; rfl
  · rw [Array.getElem?_append_right (by simp; omega)]
    simp only [Array.size_push, Array.size_replicate, List.getElem?_toArray, List.getElem?_map]
    by_cases h2 : x ≤ IN + bs.length
    · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [Nat.sub_sub]
    · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl

/-- The compiled program as an array. -/
def programA : Array Instr := program.toArray

/-- **Evaluation contract**: a halting run of the array interpreter is a halting run of the
RAM program with the same step count and cost, and the same value in `RES`. -/
theorem runA_program (bs : List Bool) (f : ℕ) (ac' : ACfg) (n t : ℕ)
    (h : runA programA f ⟨0, inputArr bs⟩ 0 0 = (ac', n, t, true)) :
    ∃ m', Run program (initCfg bs) ⟨ac'.pc, m'⟩ n t ∧ Halted program ⟨ac'.pc, m'⟩ ∧ m' RES = aget ac'.mem RES := by
  obtain ⟨c', hr, hpc, hm⟩ := runA_corr program f (initCfg bs) ⟨0, inputArr bs⟩ 0 0 ⟨rfl, inputArr_corr bs⟩ ac' n t true h
  obtain ⟨n₀, t₀, r, hn, ht, hh⟩ := runFuel_sound program f (initCfg bs) 0 0 c' n t hr
  subst hn; subst ht
  refine ⟨c'.mem, ?_, ?_, hm RES⟩
  · simp only [Nat.zero_add]; rw [← hpc]; exact r
  · rw [← hpc]; exact hh

/-! ### Evaluation on the regression instances (`#eval`; not a kernel check) -/

/-- Run the program on `bs` with fuel `f`: `(halted?, RES, steps, cost, pc)`. -/
def evalProgram (bs : List Bool) (f : ℕ) : Bool × ℕ × ℕ × ℕ × ℕ :=
  let r := runA programA f ⟨0, inputArr bs⟩ 0 0
  (r.2.2.2, aget r.1.mem RES, r.2.1, r.2.2.1, r.1.pc)

/-- The program size. -/
def programSize : ℕ := program.length

/-- A shared-subterm instance: the bottleneck instance with the node `f(z)` duplicated
(nodes `3` and `4` both compute `f(z)`; `g(f(z))` uses node `4`), outputs `(x, y, f(z), g(f(z)))`
through the *other* copy. Canonicalisation identifies the two copies. -/
def sharedG : GInstance :=
  ⟨{ sources := [0, 1, 2], symbols := [(0, 1), (1, 1)],
     nodes := [.src 0, .src 1, .src 2, .app 0 [2], .app 0 [2], .app 1 [4]],
     x := 0, y := 1, t := 3, tests := [(0, 1)] }, [4, 5]⟩

/-- A truncated list announcing an enormous count: `k = 2`, then a source list claiming
`2 ^ 40` entries with no data (the literal bits of `encodeNat 2 ++ encodeNat (2 ^ 40)`, spelled
out so that the kernel can evaluate the decoders on it). -/
def hugeCount : List Bool :=
  [true, true, false, false, true] ++ (List.replicate 41 true ++ false :: (List.replicate 40 false ++ [true]))

-- The literal agrees with the encoder (evaluated, not kernel-checked: `Nat.bits` is defined by
-- well-founded recursion).
#eval hugeCount == encodeNat 2 ++ encodeNat (2 ^ 40)

/-- Kernel-checked run on `[0]` (the code of `k = 0` and nothing else): rejected. -/
theorem run_zero : (runFuel program 300 (initCfg [false]) 0 0).2.2.2 = true ∧
    (runFuel program 300 (initCfg [false]) 0 0).1.mem RES = 0 := by decide +kernel

/-- The pure decisions on the evaluation inputs (kernel-checked), for comparison with the
`#eval` runs below. -/
theorem pure_decisions :
    decideBits (encodeInput 2 bottleneckG) = true ∧ decideBits (encodeInput 3 bottleneckG) = false ∧
    decideBits (encodeInput 1 bottleneckG) = false ∧ decideBits (encodeInput 2 dupInstance) = false ∧
    decideBits (encodeInput 2 sharedG) = true ∧ decideBits (encodeInput (2 ^ 40) sharedG) = false ∧
    decideBits hugeCount = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [decideBits_encodeInput]; decide)
    | decide

#eval programSize
#eval evalProgram [] 1000
#eval evalProgram [true] 1000
#eval evalProgram [false] 1000
#eval (encodeInput 2 bottleneckG).length
#eval evalProgram (encodeInput 2 bottleneckG) 20000000
#eval evalProgram (encodeInput 3 bottleneckG) 20000000
#eval evalProgram (encodeInput 1 bottleneckG) 20000000
#eval evalProgram (encodeInput 2 dupInstance) 20000000
#eval evalProgram (encodeInput 2 sharedG) 20000000
#eval evalProgram (encodeInput (2 ^ 40) sharedG) 20000000
#eval evalProgram (encodeInput 2 bottleneckG ++ [true]) 20000000
#eval evalProgram (List.replicate 40 true) 20000000
#eval hugeCount.length
#eval evalProgram hugeCount 20000000

end DisequalityDispersion.Machine
