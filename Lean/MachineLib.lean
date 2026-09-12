import Machine

/-! # Programming conventions and a small library for the RAM

* **Variables.** Cells `0 … 99` are the program's variables (all instructions address
  them directly).  `HP = 0` holds the heap pointer, `ONE = 1` the constant `1`.
* **Input.** The input bit string `bs` is placed at `IN = 200` as an array:
  `M[IN] = |bs|`, `M[IN + 1 + i] = bs[i]` (`1` for `true`, `0` for `false`); all other
  cells are `0` initially (`inputMem`).
* **Heap.** Cells from `IN + 1 + |bs|` upwards form a bump-allocated heap: `M[HP]` is the
  first free cell, and a program only ever writes to variables or to cells at or above the
  heap pointer at the time of the write (*persistent heap*: data below the heap pointer is
  never modified, so representation facts about existing data survive later computation —
  `Pres`).
* **Arrays.** A list of naturals `l` is stored at address `a` as `M[a] = |l|`,
  `M[a + 1 + i] = l[i]` (`Arr`).
* **Specifications.** A subroutine `c` is specified by a lemma of the form
  `∀ m, Pre m → ∃ m' k, Exec c m m' k ∧ Post m m' ∧ k ≤ bound`; steps are machine steps
  (`Machine.lean`), converted into logarithmic cost at the very end (`Run.cost_le`). -/

namespace DisequalityDispersion.Machine

/-! ### Fixed addresses -/

/-- Heap pointer. -/
def HP : ℕ := 0
/-- The constant `1`. -/
def ONE : ℕ := 1
/-- Number of variables; the input starts here. -/
def IN : ℕ := 200

/-! ### Input convention -/

/-- The initial memory for input `bs`. -/
def inputMem (bs : List Bool) : Mem := fun x =>
  if x = IN then bs.length
  else if IN < x ∧ x ≤ IN + bs.length then (if bs.getD (x - IN - 1) false then 1 else 0)
  else 0

/-- `Input m bs`: the input array is present (independently of everything else). -/
def Input (m : Mem) (bs : List Bool) : Prop :=
  m IN = bs.length ∧ ∀ i, (h : i < bs.length) → m (IN + 1 + i) = if bs[i] then 1 else 0

theorem inputMem_input (bs : List Bool) : Input (inputMem bs) bs := by
  refine ⟨by simp [inputMem], fun i h => ?_⟩
  simp only [inputMem]
  have h1 : IN + 1 + i ≠ IN := by omega
  have h2 : IN < IN + 1 + i ∧ IN + 1 + i ≤ IN + bs.length := by omega
  rw [if_neg h1, if_pos h2]
  have : IN + 1 + i - IN - 1 = i := by omega
  rw [this, List.getD_eq_getElem bs false h]

theorem inputMem_bounded (bs : List Bool) : Bounded (inputMem bs) (bits bs.length + 1) := by
  intro x
  simp only [inputMem]
  have hN : bs.length < 2 ^ (bits bs.length) := Nat.lt_size_self _
  have h2 : 2 ^ bits bs.length ≤ 2 ^ (bits bs.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ 2 ^ bits bs.length := Nat.one_le_two_pow
  split_ifs <;> omega

/-! ### Arrays and preservation -/

/-- The list `l` is stored as an array at `a`. -/
def Arr (m : Mem) (a : ℕ) (l : List ℕ) : Prop :=
  m a = l.length ∧ ∀ i, (h : i < l.length) → m (a + 1 + i) = l[i]

/-- Everything below `lo` except the cells in `W` is unchanged. -/
def Pres (m m' : Mem) (lo : ℕ) (W : List ℕ) : Prop :=
  ∀ x, x < lo → x ∉ W → m' x = m x

theorem Pres.refl (m : Mem) (lo : ℕ) (W : List ℕ) : Pres m m lo W := fun _ _ _ => rfl

theorem Pres.trans {m₁ m₂ m₃ : Mem} {lo₁ lo₂ : ℕ} {W₁ W₂ : List ℕ}
    (h₁ : Pres m₁ m₂ lo₁ W₁) (h₂ : Pres m₂ m₃ lo₂ W₂) (hlo : lo₁ ≤ lo₂) :
    Pres m₁ m₃ lo₁ (W₁ ++ W₂) := by
  intro x hx hW
  rw [List.mem_append, not_or] at hW
  rw [h₂ x (by omega) hW.2, h₁ x hx hW.1]

theorem Pres.mono {m m' : Mem} {lo lo' : ℕ} {W W' : List ℕ} (h : Pres m m' lo W)
    (hlo : lo' ≤ lo) (hW : ∀ x, x ∈ W → x ∈ W') : Pres m m' lo' W' :=
  fun x hx hW' => h x (by omega) (fun hm => hW' (hW x hm))

/-- An array below `lo` survives a preserving step whose written cells are all variables. -/
theorem Arr.of_pres {m m' : Mem} {a : ℕ} {l : List ℕ} {lo : ℕ} {W : List ℕ}
    (h : Arr m a l) (hp : Pres m m' lo W) (hlo : a + 1 + l.length ≤ lo)
    (hW : ∀ x, x ∈ W → x < IN) (ha : IN ≤ a) : Arr m' a l := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hp a (by omega) (fun hm => by have := hW a hm; omega), h.1]
  · rw [hp (a + 1 + i) (by omega) (fun hm => by have := hW _ hm; omega), h.2 i hi]

theorem Input.of_pres {m m' : Mem} {bs : List Bool} {lo : ℕ} {W : List ℕ}
    (h : Input m bs) (hp : Pres m m' lo W) (hlo : IN + 1 + bs.length ≤ lo)
    (hW : ∀ x, x ∈ W → x < IN) : Input m' bs := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hp IN (by omega) (fun hm => by have := hW IN hm; omega), h.1]
  · rw [hp (IN + 1 + i) (by omega) (fun hm => by have := hW _ hm; omega), h.2 i hi]

/-! ### Straight-line code -/

/-- Sequential composition of a list of commands (right-nested). -/
def seqs : List Cmd → Cmd
  | [] => .prim (.mov ONE ONE)
  | [c] => c
  | c :: cs => .seq c (seqs cs)

theorem Exec.prim' (p : Prim) (m : Mem) : Cmd.Exec (.prim p) m (p.exec m) 1 := Cmd.Exec.prim p m

/-- A single primitive with an explicit result description. -/
theorem Exec.prim_spec (p : Prim) (m : Mem) :
    ∃ m' k, Cmd.Exec (.prim p) m m' k ∧ m' = p.exec m ∧ k ≤ 1 :=
  ⟨p.exec m, 1, Cmd.Exec.prim p m, rfl, le_rfl⟩

/-- Sequencing with a bound on the total. -/
theorem Exec.seq_le {c₁ c₂ : Cmd} {m m₁ m₂ : Mem} {k₁ k₂ B₁ B₂ : ℕ}
    (h₁ : Cmd.Exec c₁ m m₁ k₁) (h₂ : Cmd.Exec c₂ m₁ m₂ k₂) (b₁ : k₁ ≤ B₁) (b₂ : k₂ ≤ B₂) :
    ∃ k, Cmd.Exec (.seq c₁ c₂) m m₂ k ∧ k ≤ B₁ + B₂ :=
  ⟨k₁ + k₂, Cmd.Exec.seq h₁ h₂, by omega⟩

/-! ### Counting loops

`forLoop i n body`: `while M[i] < M[n] do body; M[i] := M[i] + 1`.  The body must leave
`i`, `n` and `ONE` unchanged. -/

def forLoop (i n : ℕ) (body : Cmd) : Cmd :=
  .loop (.lt i n) (.seq body (.prim (.add i i ONE)))

theorem forLoop_spec (i n : ℕ) (body : Cmd) (I : ℕ → Mem → Prop) (N B : ℕ)
    (hI : ∀ j m, I j m → m i = j ∧ m n = N)
    (hbody : ∀ j m, j < N → I j m → ∃ m' k, Cmd.Exec body m m' k ∧ k ≤ B ∧
      m' i = j ∧ m' ONE = 1 ∧ I (j + 1) (m'.write i (j + 1))) :
    ∀ j m, j ≤ N → I j m → ∃ m' k, Cmd.Exec (forLoop i n body) m m' k ∧ I N m' ∧
      k ≤ (N - j) * (B + 3) + 2 := by
  intro j m hj hm
  have main := Cmd.Exec.loop_spec (.lt i n) (.seq body (.prim (.add i i ONE)))
    (fun r m => I (N - r) m ∧ r ≤ N) (B + 1)
    (by
      intro r m ⟨hm, hr⟩
      obtain ⟨hi, hn⟩ := hI _ m hm
      refine ⟨by simp [Cond.eval, hi, hn]; omega, ?_⟩
      obtain ⟨m', k, e, hk, hi', h1', hI'⟩ := hbody (N - (r + 1)) m (by omega) hm
      have e2 : Cmd.Exec (.prim (.add i i ONE)) m' (m'.write i (N - r)) 1 := by
        have := Cmd.Exec.prim (.add i i ONE) m'
        simp only [Prim.exec, hi', h1'] at this
        have ee : N - (r + 1) + 1 = N - r := by omega
        rw [ee] at this
        exact this
      refine ⟨m'.write i (N - r), k + 1, Cmd.Exec.seq e e2, ?_, by omega⟩
      have ee : N - (r + 1) + 1 = N - r := by omega
      rw [ee] at hI'
      exact ⟨hI', by omega⟩)
    (by
      intro m ⟨hm, _⟩
      obtain ⟨hi, hn⟩ := hI _ m hm
      simp [Cond.eval, hi, hn])
  obtain ⟨m', k, e, ⟨hI', _⟩, hk⟩ := main (N - j) m ⟨by rwa [show N - (N - j) = j by omega], by omega⟩
  refine ⟨m', k, e, by simpa using hI', ?_⟩
  have : (B + 1 + 2) = B + 3 := by omega
  rw [this] at hk
  exact hk

/-! ### Loops with a decreasing measure -/

/-- A `while` loop whose body keeps the invariant `I` and strictly decreases the measure `μ`. -/
theorem Exec.loop_measure (b : Cond) (c : Cmd) (I : Mem → Prop) (μ : Mem → ℕ) (B : ℕ)
    (hstep : ∀ m, I m → b.eval m = true →
      ∃ m' k, Cmd.Exec c m m' k ∧ I m' ∧ k ≤ B ∧ μ m' < μ m) :
    ∀ m, I m → ∃ m' k, Cmd.Exec (.loop b c) m m' k ∧ I m' ∧ b.eval m' = false ∧
      k ≤ μ m * (B + 2) + 2 := by
  intro m hm
  induction' hμ : μ m using Nat.strong_induction_on with n ih generalizing m
  cases hb : b.eval m with
  | false => exact ⟨m, 1 + 1, Cmd.Exec.loop_false hb, hm, hb, by omega⟩
  | true =>
      obtain ⟨m₁, k₁, e₁, hI₁, hk₁, hlt⟩ := hstep m hm hb
      obtain ⟨m', k₂, e₂, hI', hb', hk₂⟩ := ih (μ m₁) (by omega) m₁ hI₁ rfl
      refine ⟨m', 1 + k₁ + 1 + k₂, Cmd.Exec.loop_true hb e₁ e₂, hI', hb', ?_⟩
      have : μ m₁ + 1 ≤ n := by omega
      have h2 : (μ m₁ + 1) * (B + 2) ≤ n * (B + 2) := Nat.mul_le_mul_right _ this
      have e : (μ m₁ + 1) * (B + 2) = μ m₁ * (B + 2) + B + 2 := by ring
      omega

/-! ### Constant addresses as simp-transparent definitions -/

theorem HP_eq : HP = 0 := rfl
theorem ONE_eq : ONE = 1 := rfl
theorem IN_eq : IN = 200 := rfl

end DisequalityDispersion.Machine
