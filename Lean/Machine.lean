import Ram

/-! # Structured programs over the RAM and their compilation

`Cmd` is a structured (while-)language whose atoms are exactly the primitive RAM
instructions and whose control structure is `seq`, `ite` and `loop` (while) over the
RAM's conditions.  `Exec c m m' n` is its big-step semantics counting the *machine steps*
`n`: one per primitive, one per condition test, and one per jump the compiler emits, at
the point where the compiled code executes it.

`compile c s` produces the RAM code of `c` placed at program counter `s` (jump targets
are absolute); `compile_correct` proves that whenever `Exec c m m' n`, the machine started
at `s` with memory `m` on any program containing that code at `s` reaches program counter
`s + len c` with memory `m'` in exactly `n` steps.  Thus structured programs are just a
notation for RAM programs, step counts proved for `Exec` are RAM step counts, and
`Run.cost_le` converts them into logarithmic-cost bounds. -/

namespace DisequalityDispersion.Machine

inductive Cmd where
  | prim (p : Prim)
  | seq (c₁ c₂ : Cmd)
  | ite (b : Cond) (c₁ c₂ : Cmd)
  | loop (b : Cond) (c : Cmd)
deriving Repr

namespace Cmd

/-- Big-step semantics counting machine steps. -/
inductive Exec : Cmd → Mem → Mem → ℕ → Prop
  | prim (p : Prim) (m : Mem) : Exec (.prim p) m (p.exec m) 1
  | seq {c₁ c₂ : Cmd} {m m₁ m₂ : Mem} {k₁ k₂ : ℕ} :
      Exec c₁ m m₁ k₁ → Exec c₂ m₁ m₂ k₂ → Exec (.seq c₁ c₂) m m₂ (k₁ + k₂)
  | ite_true {b : Cond} {c₁ c₂ : Cmd} {m m' : Mem} {k : ℕ} :
      b.eval m = true → Exec c₁ m m' k → Exec (.ite b c₁ c₂) m m' (1 + k + 1)
  | ite_false {b : Cond} {c₁ c₂ : Cmd} {m m' : Mem} {k : ℕ} :
      b.eval m = false → Exec c₂ m m' k → Exec (.ite b c₁ c₂) m m' (1 + 1 + k)
  | loop_true {b : Cond} {c : Cmd} {m m₁ m₂ : Mem} {k₁ k₂ : ℕ} :
      b.eval m = true → Exec c m m₁ k₁ → Exec (.loop b c) m₁ m₂ k₂ →
      Exec (.loop b c) m m₂ (1 + k₁ + 1 + k₂)
  | loop_false {b : Cond} {c : Cmd} {m : Mem} :
      b.eval m = false → Exec (.loop b c) m m (1 + 1)

/-- Length of the compiled code (independent of the placement). -/
def len : Cmd → ℕ
  | prim _ => 1
  | seq c₁ c₂ => len c₁ + len c₂
  | ite _ c₁ c₂ => 2 + len c₁ + 1 + len c₂
  | loop _ c => 2 + len c + 1

/-- Compilation to RAM code placed at program counter `s`. -/
def compile : Cmd → ℕ → List Instr
  | prim p, _ => [.prim p]
  | seq c₁ c₂, s => compile c₁ s ++ compile c₂ (s + len c₁)
  | ite b c₁ c₂, s =>
      .jcond b (s + 2) :: .jmp (s + 2 + len c₁ + 1) :: (compile c₁ (s + 2) ++
        (.jmp (s + 2 + len c₁ + 1 + len c₂) :: compile c₂ (s + 2 + len c₁ + 1)))
  | loop b c, s =>
      .jcond b (s + 2) :: .jmp (s + 2 + len c + 1) :: (compile c (s + 2) ++ [.jmp s])

theorem compile_length (c : Cmd) (s : ℕ) : (compile c s).length = len c := by
  induction c generalizing s with
  | prim p => rfl
  | seq c₁ c₂ ih₁ ih₂ => simp [compile, len, ih₁, ih₂]
  | ite b c₁ c₂ ih₁ ih₂ => simp [compile, len, ih₁, ih₂]; omega
  | loop b c ih => simp [compile, len, ih]; omega

/-- `code` is placed at position `s` of `P`. -/
def CodeAt (P : List Instr) (s : ℕ) (code : List Instr) : Prop :=
  ∀ i, i < code.length → P[s + i]? = code[i]?

theorem CodeAt.append_left {P : List Instr} {s : ℕ} {c₁ c₂ : List Instr}
    (h : CodeAt P s (c₁ ++ c₂)) : CodeAt P s c₁ := by
  intro i hi
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem CodeAt.append_right {P : List Instr} {s : ℕ} {c₁ c₂ : List Instr}
    (h : CodeAt P s (c₁ ++ c₂)) : CodeAt P (s + c₁.length) c₂ := by
  intro i hi
  have := h (c₁.length + i) (by simp; omega)
  rw [Nat.add_assoc, this, List.getElem?_append_right (by omega)]
  simp

theorem CodeAt.head {P : List Instr} {s : ℕ} {i : Instr} {c : List Instr}
    (h : CodeAt P s (i :: c)) : P[s]? = some i := by
  have := h 0 (by simp)
  simpa using this

theorem CodeAt.tail {P : List Instr} {s : ℕ} {i : Instr} {c : List Instr}
    (h : CodeAt P s (i :: c)) : CodeAt P (s + 1) c := by
  intro j hj
  have := h (j + 1) (by simp; omega)
  rw [show s + 1 + j = s + (j + 1) by omega, this]
  simp

/-- **Compiler correctness**: the compiled code runs exactly as the structured semantics
prescribes, with the same number of steps (and some logarithmic cost `t`). -/
theorem compile_correct {c : Cmd} {m m' : Mem} {k : ℕ} (h : Exec c m m' k) :
    ∀ (P : List Instr) (s : ℕ), CodeAt P s (compile c s) →
      ∃ t, Run P ⟨s, m⟩ ⟨s + len c, m'⟩ k t := by
  induction h with
  | prim p m =>
      intro P s hc
      refine ⟨p.cost m, Run.single ?_⟩
      have := hc.head
      simp only [step, this]
      rfl
  | seq h₁ h₂ ih₁ ih₂ =>
      intro P s hc
      simp only [compile] at hc
      obtain ⟨t₁, r₁⟩ := ih₁ P s hc.append_left
      obtain ⟨t₂, r₂⟩ := ih₂ P (s + len _) (by
        have := hc.append_right
        rwa [compile_length] at this)
      have := r₁.trans r₂
      exact ⟨_, by simpa [len, Nat.add_assoc] using this⟩
  | @ite_true b c₁ c₂ m m' k hb h ih =>
      intro P s hc
      simp only [compile] at hc
      have h0 := hc.head
      have hc₁ : CodeAt P (s + 2) (compile c₁ (s + 2)) := hc.tail.tail.append_left
      have hj : P[s + 2 + len c₁]? = some (.jmp (s + 2 + len c₁ + 1 + len c₂)) := by
        have := hc.tail.tail.append_right
        rw [compile_length] at this
        exact this.head
      have s₀ : Run P ⟨s, m⟩ ⟨s + 2, m⟩ 1 (b.cost m) := by
        apply Run.single
        simp [step, h0, hb]
      obtain ⟨t₁, s₁⟩ := ih P (s + 2) hc₁
      have s₂ : Run P ⟨s + 2 + len c₁, m'⟩ ⟨s + len (.ite b c₁ c₂), m'⟩ 1 1 := by
        apply Run.single
        simp [step, hj, len]
        omega
      have := (s₀.trans s₁).trans s₂
      exact ⟨_, by simpa using this⟩
  | @ite_false b c₁ c₂ m m' k hb h ih =>
      intro P s hc
      simp only [compile] at hc
      have h0 := hc.head
      have h1 := hc.tail.head
      have hc₂ : CodeAt P (s + 2 + len c₁ + 1) (compile c₂ (s + 2 + len c₁ + 1)) := by
        have := hc.tail.tail.append_right
        rw [compile_length] at this
        exact this.tail
      have s₀ : Run P ⟨s, m⟩ ⟨s + 1, m⟩ 1 (b.cost m) := by
        apply Run.single
        simp [step, h0, hb]
      have s₁ : Run P ⟨s + 1, m⟩ ⟨s + 2 + len c₁ + 1, m⟩ 1 1 := by
        apply Run.single
        simp [step, h1]
      obtain ⟨t₂, s₂⟩ := ih P (s + 2 + len c₁ + 1) hc₂
      have := (s₀.trans s₁).trans s₂
      refine ⟨b.cost m + 1 + t₂, ?_⟩
      simp only [len]
      convert this using 2
      omega
  | @loop_true b c m m₁ m₂ k₁ k₂ hb h₁ h₂ ih₁ ih₂ =>
      intro P s hc
      have hc' := hc
      simp only [compile] at hc
      have h0 := hc.head
      have hcb : CodeAt P (s + 2) (compile c (s + 2)) := hc.tail.tail.append_left
      have hj : P[s + 2 + len c]? = some (.jmp s) := by
        have := hc.tail.tail.append_right
        rw [compile_length] at this
        exact this.head
      have s₀ : Run P ⟨s, m⟩ ⟨s + 2, m⟩ 1 (b.cost m) := by
        apply Run.single
        simp [step, h0, hb]
      obtain ⟨t₁, s₁⟩ := ih₁ P (s + 2) hcb
      have s₂ : Run P ⟨s + 2 + len c, m₁⟩ ⟨s, m₁⟩ 1 1 := by
        apply Run.single
        simp [step, hj]
      obtain ⟨t₃, s₃⟩ := ih₂ P s hc'
      have := ((s₀.trans s₁).trans s₂).trans s₃
      exact ⟨_, by simpa [Nat.add_assoc] using this⟩
  | @loop_false b c m hb =>
      intro P s hc
      simp only [compile] at hc
      have h0 := hc.head
      have h1 := hc.tail.head
      have s₀ : Run P ⟨s, m⟩ ⟨s + 1, m⟩ 1 (b.cost m) := by
        apply Run.single
        simp [step, h0, hb]
      have s₁ : Run P ⟨s + 1, m⟩ ⟨s + 2 + len c + 1, m⟩ 1 1 := by
        apply Run.single
        simp [step, h1]
      have := s₀.trans s₁
      refine ⟨b.cost m + 1, ?_⟩
      simp only [len]
      convert this using 2
      omega

/-! ### Derived reasoning principles -/

theorem Exec.deterministic {c : Cmd} {m m₁ m₂ : Mem} {k₁ k₂ : ℕ}
    (h₁ : Exec c m m₁ k₁) (h₂ : Exec c m m₂ k₂) : m₁ = m₂ ∧ k₁ = k₂ := by
  induction h₁ generalizing m₂ k₂ with
  | prim p m => cases h₂; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
      cases h₂ with
      | seq g₁ g₂ =>
          obtain ⟨rfl, rfl⟩ := ih₁ g₁
          obtain ⟨rfl, rfl⟩ := ih₂ g₂
          exact ⟨rfl, rfl⟩
  | ite_true hb _ ih =>
      cases h₂ with
      | ite_true _ g => obtain ⟨rfl, rfl⟩ := ih g; exact ⟨rfl, rfl⟩
      | ite_false hb' _ => rw [hb] at hb'; cases hb'
  | ite_false hb _ ih =>
      cases h₂ with
      | ite_true hb' _ => rw [hb] at hb'; cases hb'
      | ite_false _ g => obtain ⟨rfl, rfl⟩ := ih g; exact ⟨rfl, rfl⟩
  | loop_true hb _ _ ih₁ ih₂ =>
      cases h₂ with
      | loop_true _ g₁ g₂ =>
          obtain ⟨rfl, rfl⟩ := ih₁ g₁
          obtain ⟨rfl, rfl⟩ := ih₂ g₂
          exact ⟨rfl, rfl⟩
      | loop_false hb' => rw [hb] at hb'; cases hb'
  | loop_false hb =>
      cases h₂ with
      | loop_true hb' _ _ => rw [hb] at hb'; cases hb'
      | loop_false _ => exact ⟨rfl, rfl⟩

/-- Sequencing of specifications. -/
theorem Exec.seq_spec {c₁ c₂ : Cmd} {m : Mem} {P₁ : Mem → Prop} {P₂ : Mem → Prop}
    {B₁ B₂ : ℕ}
    (h₁ : ∃ m₁ k₁, Exec c₁ m m₁ k₁ ∧ P₁ m₁ ∧ k₁ ≤ B₁)
    (h₂ : ∀ m₁, P₁ m₁ → ∃ m₂ k₂, Exec c₂ m₁ m₂ k₂ ∧ P₂ m₂ ∧ k₂ ≤ B₂) :
    ∃ m₂ k, Exec (.seq c₁ c₂) m m₂ k ∧ P₂ m₂ ∧ k ≤ B₁ + B₂ := by
  obtain ⟨m₁, k₁, e₁, p₁, b₁⟩ := h₁
  obtain ⟨m₂, k₂, e₂, p₂, b₂⟩ := h₂ m₁ p₁
  exact ⟨m₂, k₁ + k₂, Exec.seq e₁ e₂, p₂, by omega⟩

/-- A counting loop: `I n` describes the state with `n` iterations still to run; every
iteration takes at most `B` steps. -/
theorem Exec.loop_spec (b : Cond) (c : Cmd) (I : ℕ → Mem → Prop) (B : ℕ)
    (hstep : ∀ n m, I (n + 1) m → b.eval m = true ∧
      ∃ m' k, Exec c m m' k ∧ I n m' ∧ k ≤ B)
    (hexit : ∀ m, I 0 m → b.eval m = false) :
    ∀ n m, I n m → ∃ m' k, Exec (.loop b c) m m' k ∧ I 0 m' ∧ k ≤ n * (B + 2) + 2 := by
  intro n
  induction n with
  | zero =>
      intro m hm
      exact ⟨m, 1 + 1, Exec.loop_false (hexit m hm), hm, by omega⟩
  | succ n ih =>
      intro m hm
      obtain ⟨hb, m₁, k₁, e₁, hI, hk₁⟩ := hstep n m hm
      obtain ⟨m', k₂, e₂, hI', hk₂⟩ := ih m₁ hI
      refine ⟨m', 1 + k₁ + 1 + k₂, Exec.loop_true hb e₁ e₂, hI', ?_⟩
      have e : (n + 1) * (B + 2) = n * (B + 2) + (B + 2) := by ring
      omega

end Cmd

end DisequalityDispersion.Machine
