import EncodingCost

/-! # A logarithmic-cost random-access machine

The standard machine model used for the running-time theorem: a deterministic
random-access machine in the sense of Aho–Hopcroft–Ullman (*The Design and Analysis of
Computer Algorithms*, §1.2) with the **logarithmic cost criterion**.

* **Memory.** An unbounded array `Mem := ℕ → ℕ` of natural numbers (each cell holds an
  arbitrary natural number); the program is a fixed finite list of instructions and the
  program counter `pc` is a natural number.
* **Instructions** (`Instr`).  Operands are memory addresses written in the program
  (direct addressing), with one level of indirection for `load`/`store`:
  `const a c` (`M[a] := c`), `mov a b` (`M[a] := M[b]`), `load a b` (`M[a] := M[M[b]]`),
  `store a b` (`M[M[a]] := M[b]`), `add a b c` (`M[a] := M[b] + M[c]`),
  `sub a b c` (`M[a] := M[b] ∸ M[c]`, truncated), `jmp l`, `jcond (lt a b) l`
  (`if M[a] < M[b] then pc := l`), `jcond (eq a b) l` (`if M[a] = M[b] then pc := l`) and
  `halt`.  Every instruction reads and writes a bounded number of cells; there is no
  primitive on lists, no equality test on lists, no multiplication, and no operation whose
  cost could hide the size of its operands.
* **Steps and cost.**  A machine step is the execution of one instruction.  Under the
  logarithmic cost criterion an instruction costs `1` plus the binary length
  `bits v = Nat.size v` of every *value* it reads: the contents of the cells it accesses
  (including the cell whose contents serve as an indirect address), the immediate constant
  of `const`, and the two values compared by a conditional jump.  Direct addresses and jump
  targets are part of the fixed program and are not charged (as in AHU); `halt` and `jmp`
  cost `1`.  `Run P c c' n t` records both the number of steps `n` and the total
  logarithmic cost `t` of a run.
* **Cost versus steps.**  Since the only value-producing operations are addition,
  truncated subtraction, copying and loading constants, after `n` steps every value in
  memory has at most `b₀ + n` bits, where `b₀` bounds the bits of the initial memory and
  of the program's constants (`Run.bounded`); hence the logarithmic cost of a run of `n`
  steps is at most `n * (1 + 2 * (b₀ + n))` (`Run.cost_le`).  A polynomial bound on the
  number of steps therefore yields a polynomial bound on the logarithmic cost.
* **Halting.** The machine halts when the program counter points at `halt` (or outside
  the program).

`Machine.lean` builds a structured layer (`Cmd`) on top of this model together with a
compiler into `List Instr` and proves that the compiled code runs exactly as the
structured semantics prescribes, with the same number of steps. -/

namespace DisequalityDispersion.Machine

/-- Binary length of a natural number (`0` has length `0`). -/
abbrev bits (n : ℕ) : ℕ := Nat.size n

theorem bits_le_iff {n b : ℕ} : bits n ≤ b ↔ n < 2 ^ b := Nat.size_le

theorem bits_le_of_lt_pow {n b : ℕ} (h : n < 2 ^ b) : bits n ≤ b := Nat.size_le.mpr h

theorem bits_mono {a b : ℕ} (h : a ≤ b) : bits a ≤ bits b := Nat.size_le_size h

theorem bits_le_self (n : ℕ) : bits n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

/-- Memory: an unbounded array of natural numbers. -/
abbrev Mem := ℕ → ℕ

/-- Write `v` into cell `a`. -/
def Mem.write (m : Mem) (a v : ℕ) : Mem := fun x => if x = a then v else m x

@[simp] theorem Mem.write_same (m : Mem) (a v : ℕ) : m.write a v a = v := by simp [Mem.write]

theorem Mem.write_ne (m : Mem) {a x : ℕ} (v : ℕ) (h : x ≠ a) : m.write a v x = m x := by
  simp [Mem.write, h]

@[simp] theorem Mem.write_apply (m : Mem) (a v x : ℕ) :
    m.write a v x = if x = a then v else m x := rfl

/-- The non-jump instructions ("primitives"). -/
inductive Prim where
  | const (a c : ℕ)
  | mov (a b : ℕ)
  | load (a b : ℕ)
  | store (a b : ℕ)
  | add (a b c : ℕ)
  | sub (a b c : ℕ)
deriving DecidableEq, Repr

namespace Prim

/-- Effect of a primitive on the memory. -/
def exec : Prim → Mem → Mem
  | const a c, m => m.write a c
  | mov a b, m => m.write a (m b)
  | load a b, m => m.write a (m (m b))
  | store a b, m => m.write (m a) (m b)
  | add a b c, m => m.write a (m b + m c)
  | sub a b c, m => m.write a (m b - m c)

/-- Logarithmic cost of a primitive: `1` plus the binary lengths of the values read. -/
def cost : Prim → Mem → ℕ
  | const _ c, _ => 1 + bits c
  | mov _ b, m => 1 + bits (m b)
  | load _ b, m => 1 + bits (m b) + bits (m (m b))
  | store a b, m => 1 + bits (m a) + bits (m b)
  | add _ b c, m => 1 + bits (m b) + bits (m c)
  | sub _ b c, m => 1 + bits (m b) + bits (m c)

/-- The immediate constant of a primitive (`0` for the others). -/
def constOf' : Prim → ℕ
  | const _ c => c
  | _ => 0

/-- The (direct) cell written by a primitive, if it is a direct write. -/
def target : Prim → Mem → ℕ
  | const a _, _ => a
  | mov a _, _ => a
  | load a _, _ => a
  | store a _, m => m a
  | add a _ _, _ => a
  | sub a _ _, _ => a

theorem exec_apply_ne (p : Prim) (m : Mem) {x : ℕ} (h : x ≠ p.target m) : p.exec m x = m x := by
  cases p <;> simp [exec, target, Mem.write] at h ⊢ <;> simp [h]

end Prim

/-- Conditions tested by conditional jumps. -/
inductive Cond where
  | lt (a b : ℕ)
  | eq (a b : ℕ)
deriving DecidableEq, Repr

namespace Cond

def eval : Cond → Mem → Bool
  | lt a b, m => decide (m a < m b)
  | eq a b, m => decide (m a = m b)

/-- Cost of testing a condition: `1` plus the lengths of the two values compared. -/
def cost : Cond → Mem → ℕ
  | lt a b, m => 1 + bits (m a) + bits (m b)
  | eq a b, m => 1 + bits (m a) + bits (m b)

end Cond

/-- Instructions of the machine. -/
inductive Instr where
  | prim (p : Prim)
  | jmp (l : ℕ)
  | jcond (b : Cond) (l : ℕ)
  | halt
deriving DecidableEq, Repr

/-- A configuration: program counter and memory. -/
structure Cfg where
  pc : ℕ
  mem : Mem

/-- One step of the machine on program `P`: the next configuration and the cost of the
executed instruction; `none` when the machine is halted (`halt`, or `pc` outside `P`). -/
def step (P : List Instr) (c : Cfg) : Option (Cfg × ℕ) :=
  match P[c.pc]? with
  | none => none
  | some .halt => none
  | some (.prim p) => some (⟨c.pc + 1, p.exec c.mem⟩, p.cost c.mem)
  | some (.jmp l) => some (⟨l, c.mem⟩, 1)
  | some (.jcond b l) => some (⟨if b.eval c.mem then l else c.pc + 1, c.mem⟩, b.cost c.mem)

/-- The machine is halted in `c`. -/
def Halted (P : List Instr) (c : Cfg) : Prop := step P c = none

/-- `Run P c c' n t`: `c'` is reached from `c` by `n` steps of total logarithmic cost `t`. -/
inductive Run (P : List Instr) : Cfg → Cfg → ℕ → ℕ → Prop
  | refl (c : Cfg) : Run P c c 0 0
  | step {c c₁ c₂ : Cfg} {k n t : ℕ} :
      step P c = some (c₁, k) → Run P c₁ c₂ n t → Run P c c₂ (n + 1) (k + t)

theorem Run.trans {P : List Instr} {c₁ c₂ c₃ : Cfg} {n₁ n₂ t₁ t₂ : ℕ}
    (h₁ : Run P c₁ c₂ n₁ t₁) (h₂ : Run P c₂ c₃ n₂ t₂) : Run P c₁ c₃ (n₁ + n₂) (t₁ + t₂) := by
  induction h₁ with
  | refl c => simpa using h₂
  | @step c c₁ c₂ k n t hs _ ih =>
      have e1 : n + 1 + n₂ = (n + n₂) + 1 := by omega
      have e2 : k + t + t₂ = k + (t + t₂) := by omega
      rw [e1, e2]
      exact Run.step hs (ih h₂)

theorem Run.single {P : List Instr} {c c' : Cfg} {k : ℕ}
    (h : Machine.step P c = some (c', k)) : Run P c c' 1 k := by
  have := Run.step h (Run.refl (P := P) c')
  simpa using this

/-- Determinism: two runs from the same configuration that both end halted coincide. -/
theorem Run.halted_unique {P : List Instr} {c c₁ c₂ : Cfg} {n₁ n₂ t₁ t₂ : ℕ}
    (h₁ : Run P c c₁ n₁ t₁) (h₂ : Run P c c₂ n₂ t₂) (hh₁ : Halted P c₁) (hh₂ : Halted P c₂) :
    c₁ = c₂ ∧ n₁ = n₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing c₂ n₂ t₂ with
  | refl c =>
      cases h₂ with
      | refl => exact ⟨rfl, rfl, rfl⟩
      | step hs _ => rw [Halted, hs] at hh₁; cases hh₁
  | step hs _ ih =>
      cases h₂ with
      | refl => rw [Halted, hs] at hh₂; cases hh₂
      | step hs' hr' =>
          rw [hs] at hs'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs')
          obtain ⟨h1, h2, h3⟩ := ih hr' hh₁ hh₂
          exact ⟨h1, by rw [h2], by rw [h3]⟩

/-! ### Logarithmic cost versus number of steps -/

/-- Every cell holds a value of at most `b` bits. -/
def Bounded (m : Mem) (b : ℕ) : Prop := ∀ x, m x < 2 ^ b

theorem Bounded.mono {m : Mem} {b b' : ℕ} (h : Bounded m b) (hb : b ≤ b') : Bounded m b' :=
  fun x => lt_of_lt_of_le (h x) (Nat.pow_le_pow_right (by norm_num) hb)

theorem Bounded.bits_le {m : Mem} {b : ℕ} (h : Bounded m b) (x : ℕ) : bits (m x) ≤ b :=
  bits_le_of_lt_pow (h x)

/-- The largest immediate constant of a program. -/
def Instr.constOf : Instr → ℕ
  | .prim (.const _ c) => c
  | _ => 0

def constBound (P : List Instr) : ℕ := (P.map Instr.constOf).foldr max 0

theorem constOf_le_constBound {P : List Instr} {i : Instr} (h : i ∈ P) :
    i.constOf ≤ constBound P := by
  unfold constBound
  induction P with
  | nil => cases h
  | cons j P ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem Prim.exec_bounded {p : Prim} {m : Mem} {b : ℕ} (hm : Bounded m b)
    (hc : bits p.constOf' ≤ b) : Bounded (p.exec m) (b + 1) := by
  intro x
  have h2 : 2 ^ b ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; ring
  cases p with
  | const a c =>
      simp only [Prim.exec, Mem.write_apply]
      split_ifs
      · simp only [Prim.constOf'] at hc
        exact lt_of_lt_of_le (bits_le_iff.mp hc) h2
      · exact lt_of_lt_of_le (hm x) h2
  | mov a c => simp only [Prim.exec, Mem.write_apply]; split_ifs <;> exact lt_of_lt_of_le (hm _) h2
  | load a c => simp only [Prim.exec, Mem.write_apply]; split_ifs <;> exact lt_of_lt_of_le (hm _) h2
  | store a c => simp only [Prim.exec, Mem.write_apply]; split_ifs <;> exact lt_of_lt_of_le (hm _) h2
  | add a c d =>
      simp only [Prim.exec, Mem.write_apply]
      split_ifs
      · rw [hp]; exact Nat.add_lt_add (hm _) (hm _)
      · exact lt_of_lt_of_le (hm x) h2
  | sub a c d =>
      simp only [Prim.exec, Mem.write_apply]
      split_ifs
      · exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_lt_of_le (hm _) h2)
      · exact lt_of_lt_of_le (hm x) h2

theorem Prim.cost_le {p : Prim} {m : Mem} {b : ℕ} (hm : Bounded m b)
    (hc : bits p.constOf' ≤ b) : p.cost m ≤ 1 + 2 * b := by
  have hb := hm.bits_le
  cases p with
  | const a c => simp only [Prim.cost, Prim.constOf'] at hc ⊢; omega
  | mov a c => have := hb c; simp only [Prim.cost]; omega
  | load a c => have := hb c; have := hb (m c); simp only [Prim.cost]; omega
  | store a c => have := hb a; have := hb c; simp only [Prim.cost]; omega
  | add a c d => have := hb c; have := hb d; simp only [Prim.cost]; omega
  | sub a c d => have := hb c; have := hb d; simp only [Prim.cost]; omega

theorem Cond.cost_le {c : Cond} {m : Mem} {b : ℕ} (hm : Bounded m b) : c.cost m ≤ 1 + 2 * b := by
  have hb := hm.bits_le
  cases c with
  | lt a d => have := hb a; have := hb d; simp only [Cond.cost]; omega
  | eq a d => have := hb a; have := hb d; simp only [Cond.cost]; omega

theorem step_bounded {P : List Instr} {c c' : Cfg} {k b : ℕ} (hm : Bounded c.mem b)
    (hP : bits (constBound P) ≤ b) (hs : step P c = some (c', k)) :
    Bounded c'.mem (b + 1) ∧ k ≤ 1 + 2 * b := by
  unfold step at hs
  cases hi : P[c.pc]? with
  | none => rw [hi] at hs; cases hs
  | some i =>
      rw [hi] at hs
      have hmem : i ∈ P := List.mem_of_getElem? hi
      cases i with
      | halt => cases hs
      | prim p =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
          have hc : bits p.constOf' ≤ b := by
            refine le_trans (bits_mono ?_) hP
            have := constOf_le_constBound hmem
            cases p with
            | const a c => simpa [Instr.constOf, Prim.constOf'] using this
            | _ => simp [Prim.constOf']
          exact ⟨Prim.exec_bounded hm hc, Prim.cost_le hm hc⟩
      | jmp l =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
          exact ⟨hm.mono (by omega), by omega⟩
      | jcond b' l =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hs)
          exact ⟨hm.mono (by omega), Cond.cost_le hm⟩

/-- After `n` steps every value has at most `b + n` bits. -/
theorem Run.bounded {P : List Instr} {c c' : Cfg} {n t b : ℕ} (hm : Bounded c.mem b)
    (hP : bits (constBound P) ≤ b) (h : Run P c c' n t) : Bounded c'.mem (b + n) := by
  induction h generalizing b with
  | refl c => simpa using hm
  | step hs _ ih =>
      obtain ⟨hb, _⟩ := step_bounded hm hP hs
      have := ih hb (le_trans hP (by omega))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- **Logarithmic cost from the step count**: a run of `n` steps from a memory whose
values have at most `b` bits (with `b` also bounding the program's constants) has
logarithmic cost at most `n * (1 + 2 * (b + n))`. -/
theorem Run.cost_le {P : List Instr} {c c' : Cfg} {n t b : ℕ} (hm : Bounded c.mem b)
    (hP : bits (constBound P) ≤ b) (h : Run P c c' n t) : t ≤ n * (1 + 2 * (b + n)) := by
  induction h generalizing b with
  | refl c => simp
  | @step c c₁ c₂ k n t hs hr ih =>
      obtain ⟨hb, hk⟩ := step_bounded hm hP hs
      have := ih hb (le_trans hP (by omega))
      have e : (n + 1) * (1 + 2 * (b + (n + 1))) = (1 + 2 * b) + n * (1 + 2 * (b + 1 + n)) + 2 * n + 2 := by
        ring
      rw [e]
      omega

/-- Steps of the machine only depend on the instruction at the current program counter. -/
theorem step_congr {P P' : List Instr} {c : Cfg} (h : P[c.pc]? = P'[c.pc]?) :
    step P c = step P' c := by
  unfold step; rw [h]

end DisequalityDispersion.Machine
