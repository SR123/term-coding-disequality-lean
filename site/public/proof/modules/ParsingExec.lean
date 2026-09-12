import ParsingCost
import CostMonad

/-! # Execution-linked cost of the parser: an instrumented program

`ParsingCost.lean` states one cost function per decoder.  This module removes the doubt
that a hand-written cost function might omit work: every decoder of `Parsing.lean` is
re-implemented as an *instrumented program* in the step-counting monad `Costed`, in which
each primitive operation charges its steps exactly where it is executed:

* `tick 1` at every list cell examined (a `match` on the input or on a result);
* `tick (natC v)` at every operation on a binary counter `v` (increment, decrement,
  pattern match) and at every shift-and-add of the digit fold;
* nothing else — there is no other source of steps (the monad `Costed` is defined in
  `CostMonad.lean`).

The two theorems per decoder, `…M_val` and `…M_cost`, prove that the instrumented program
computes exactly the pure decoder and that its step count is exactly the cost function of
`ParsingCost.lean`.  Hence the bounds of `ParsingCost.lean` (`decodeInputC_le`,
`decideBitsC_le_all`) are bounds on the number of primitive steps executed by these
concrete programs.  The remaining machine-model obligation is the simulation of the
primitives themselves (a list cell match in `O(1)`, a binary-counter operation on `v` in
`O(natC v)` bit steps) on a fixed machine; see the return report. -/

namespace DisequalityDispersion.Encoded

open Costed

variable {α β : Type}

/-! ### Instrumented decoders -/

/-- `readBits`: one cell and one counter decrement per digit. -/
def readBitsM : ℕ → List Bool → Costed (Option (List Bool × List Bool))
  | 0, l => do tick 1; return some ([], l)
  | c + 1, [] => do tick (1 + natC (c + 1)); return none
  | c + 1, b :: l => do
      tick (1 + natC (c + 1))
      let r ← readBitsM c l
      match r with
      | none => return none
      | some (bs, rest) => return some (b :: bs, rest)

theorem readBitsM_val : ∀ (c : ℕ) (l : List Bool), (readBitsM c l).val = readBits c l
  | 0, l => rfl
  | c + 1, [] => rfl
  | c + 1, b :: l => by
      simp only [readBitsM, readBits, bind_val]
      rw [readBitsM_val c l]
      cases readBits c l with
      | none => rfl
      | some p => rfl

theorem readBitsM_cost : ∀ (c : ℕ) (l : List Bool), (readBitsM c l).cost = readBitsC c l
  | 0, l => rfl
  | c + 1, [] => rfl
  | c + 1, b :: l => by
      simp only [readBitsM, readBitsC, bind_cost, tick_cost]
      rw [readBitsM_cost c l, readBitsM_val c l]
      cases readBits c l with
      | none => simp
      | some p => obtain ⟨bs, rest⟩ := p; simp

/-- `fromBits`: a shift-and-add on the partial value per digit. -/
def fromBitsM : List Bool → Costed ℕ
  | [] => do tick 1; return 0
  | b :: bs => do
      let n ← fromBitsM bs
      tick (1 + natC n)
      return Nat.bit b n

theorem fromBitsM_val : ∀ (bs : List Bool), (fromBitsM bs).val = fromBits bs
  | [] => rfl
  | b :: bs => by
      simp only [fromBitsM, bind_val, pure_val, fromBits_cons]
      rw [fromBitsM_val bs]

theorem fromBitsM_cost : ∀ (bs : List Bool), (fromBitsM bs).cost = fromBitsC bs
  | [] => rfl
  | b :: bs => by
      simp only [fromBitsM, fromBitsC, bind_cost, tick_cost, pure_cost]
      rw [fromBitsM_cost bs, fromBitsM_val bs]
      omega

/-- `Canon`: one scan for the last digit. -/
def canonM (bs : List Bool) : Costed Bool := do tick (bs.length + 1); return Canon bs

theorem canonM_val (bs : List Bool) : (canonM bs).val = Canon bs := rfl
theorem canonM_cost (bs : List Bool) : (canonM bs).cost = canonC bs := by
  simp [canonM, canonC]

/-- `decodeNatAux`: a counter increment per leading one, then the digit read, the canonicity
scan and the digit fold. -/
def decodeNatAuxM : ℕ → List Bool → Costed (Option (ℕ × List Bool))
  | c, true :: l => do tick (1 + natC c); decodeNatAuxM (c + 1) l
  | c, false :: l => do
      tick 1
      let r ← readBitsM c l
      match r with
      | none => return none
      | some (bs, rest) => do
          let ok ← canonM bs
          let n ← fromBitsM bs
          return (if ok then some (n, rest) else none)
  | _, [] => do tick 1; return none

theorem decodeNatAuxM_val : ∀ (c : ℕ) (l : List Bool),
    (decodeNatAuxM c l).val = decodeNatAux c l
  | c, [] => rfl
  | c, true :: l => by
      simp only [decodeNatAuxM, decodeNatAux, bind_val]
      exact decodeNatAuxM_val (c + 1) l
  | c, false :: l => by
      simp only [decodeNatAuxM, decodeNatAux, bind_val]
      rw [readBitsM_val]
      cases readBits c l with
      | none => rfl
      | some p =>
          obtain ⟨bs, rest⟩ := p
          simp only [bind_val, canonM_val, fromBitsM_val, pure_val]

theorem decodeNatAuxM_cost : ∀ (c : ℕ) (l : List Bool),
    (decodeNatAuxM c l).cost = decodeNatAuxC c l
  | c, [] => rfl
  | c, true :: l => by
      simp only [decodeNatAuxM, decodeNatAuxC, bind_cost, tick_cost]
      rw [decodeNatAuxM_cost (c + 1) l]
  | c, false :: l => by
      simp only [decodeNatAuxM, decodeNatAuxC, bind_cost, tick_cost]
      rw [readBitsM_cost, readBitsM_val]
      cases readBits c l with
      | none => simp
      | some p =>
          obtain ⟨bs, rest⟩ := p
          simp only [bind_cost, canonM_cost, canonM_val, fromBitsM_cost, fromBitsM_val,
            pure_cost]
          simp only [add_zero]
          ring

def decodeNatM (l : List Bool) : Costed (Option (ℕ × List Bool)) := decodeNatAuxM 0 l

theorem decodeNatM_val (l : List Bool) : (decodeNatM l).val = decodeNat l := decodeNatAuxM_val 0 l
theorem decodeNatM_cost (l : List Bool) : (decodeNatM l).cost = decodeNatC l := decodeNatAuxM_cost 0 l

/-! ### Instrumented combinators -/

/-- `bindP` in the monad: run `f`, and on success run `g` on the remainder. -/
def bindPM (f : List Bool → Costed (Option (α × List Bool)))
    (g : α → List Bool → Costed (Option (β × List Bool))) (l : List Bool) :
    Costed (Option (β × List Bool)) := do
  let r ← f l
  match r with
  | none => return none
  | some (a, rest) => g a rest

def purePM (b : β) (l : List Bool) : Costed (Option (β × List Bool)) := return some (b, l)

theorem bindPM_val {f : List Bool → Costed (Option (α × List Bool))}
    {fp : List Bool → Option (α × List Bool)} (hf : ∀ l, (f l).val = fp l)
    {g : α → List Bool → Costed (Option (β × List Bool))}
    {gp : α → List Bool → Option (β × List Bool)} (hg : ∀ a l, (g a l).val = gp a l) (l : List Bool) :
    (bindPM f g l).val = bindP fp gp l := by
  simp only [bindPM, bindP, bind_val, hf]
  cases fp l with
  | none => rfl
  | some p => obtain ⟨a, rest⟩ := p; exact hg a rest

theorem bindPM_cost {f : List Bool → Costed (Option (α × List Bool))}
    {fp : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : ∀ l, (f l).val = fp l) (hfc : ∀ l, (f l).cost = fc l)
    {g : α → List Bool → Costed (Option (β × List Bool))} {gc : α → List Bool → ℕ}
    (hgc : ∀ a l, (g a l).cost = gc a l) (l : List Bool) :
    (bindPM f g l).cost = bindPC fp fc gc l := by
  simp only [bindPM, bindPC, bind_cost, hf, hfc]
  cases fp l with
  | none => rfl
  | some p => obtain ⟨a, rest⟩ := p; simp [hgc]

theorem purePM_val (b : β) (l : List Bool) : (purePM b l).val = pureP b l := rfl
theorem purePM_cost (b : β) (l : List Bool) : (purePM b l).cost = 0 := rfl

/-- `decodeN`: a counter match per value, the value, the rest, a cons. -/
def decodeNM (f : List Bool → Costed (Option (α × List Bool))) :
    ℕ → List Bool → Costed (Option (List α × List Bool))
  | 0, l => do tick 1; return some ([], l)
  | n + 1, l => do
      tick (1 + natC (n + 1))
      bindPM f (fun a => bindPM (decodeNM f n) (fun as rest => do tick 1; return some (a :: as, rest))) l

theorem decodeNM_val {f : List Bool → Costed (Option (α × List Bool))}
    {fp : List Bool → Option (α × List Bool)} (hf : ∀ l, (f l).val = fp l) :
    ∀ (n : ℕ) (l : List Bool), (decodeNM f n l).val = decodeN fp n l
  | 0, l => rfl
  | n + 1, l => by
      simp only [decodeNM, decodeN, bind_val]
      exact bindPM_val hf (fun a l' => bindPM_val (decodeNM_val hf n) (fun as l'' => rfl) l') l

theorem decodeNM_cost {f : List Bool → Costed (Option (α × List Bool))}
    {fp : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : ∀ l, (f l).val = fp l) (hfc : ∀ l, (f l).cost = fc l) :
    ∀ (n : ℕ) (l : List Bool), (decodeNM f n l).cost = decodeNC fp fc n l
  | 0, l => rfl
  | n + 1, l => by
      simp only [decodeNM, decodeNC, bind_cost, tick_cost]
      rw [bindPM_cost hf hfc (fun a l' =>
        bindPM_cost (decodeNM_val hf n) (decodeNM_cost hf hfc n) (gc := fun _ _ => 1)
          (fun as l'' => rfl) l')]

def decodeListM (f : List Bool → Costed (Option (α × List Bool))) :
    List Bool → Costed (Option (List α × List Bool)) :=
  bindPM decodeNatM (fun n => decodeNM f n)

theorem decodeListM_val {f : List Bool → Costed (Option (α × List Bool))}
    {fp : List Bool → Option (α × List Bool)} (hf : ∀ l, (f l).val = fp l) (l : List Bool) :
    (decodeListM f l).val = decodeList fp l :=
  bindPM_val decodeNatM_val (fun n => decodeNM_val hf n) l

theorem decodeListM_cost {f : List Bool → Costed (Option (α × List Bool))}
    {fp : List Bool → Option (α × List Bool)} {fc : List Bool → ℕ}
    (hf : ∀ l, (f l).val = fp l) (hfc : ∀ l, (f l).cost = fc l) (l : List Bool) :
    (decodeListM f l).cost = decodeListC fp fc l :=
  bindPM_cost decodeNatM_val decodeNatM_cost (fun n => decodeNM_cost hf hfc n) l

def decodePairM : List Bool → Costed (Option ((ℕ × ℕ) × List Bool)) :=
  bindPM decodeNatM (fun a => bindPM decodeNatM (fun b => purePM (a, b)))

theorem decodePairM_val (l : List Bool) : (decodePairM l).val = decodePair l :=
  bindPM_val decodeNatM_val (fun a => bindPM_val decodeNatM_val (fun b => purePM_val (a, b))) l

theorem decodePairM_cost (l : List Bool) : (decodePairM l).cost = decodePairC l :=
  bindPM_cost decodeNatM_val decodeNatM_cost
    (fun a => bindPM_cost decodeNatM_val decodeNatM_cost (fun b => purePM_cost (a, b))) l

/-- `tagP`: one cell for the tag, then the selected branch. -/
def tagPM (f0 f1 : List Bool → Costed (Option (α × List Bool))) :
    List Bool → Costed (Option (α × List Bool))
  | [] => do tick 1; return none
  | false :: l => do tick 1; f0 l
  | true :: l => do tick 1; f1 l

theorem tagPM_val {f0 f1 : List Bool → Costed (Option (α × List Bool))}
    {f0p f1p : List Bool → Option (α × List Bool)} (h0 : ∀ l, (f0 l).val = f0p l)
    (h1 : ∀ l, (f1 l).val = f1p l) : ∀ (l : List Bool), (tagPM f0 f1 l).val = tagP f0p f1p l
  | [] => rfl
  | false :: l => by simp [tagPM, tagP, h0]
  | true :: l => by simp [tagPM, tagP, h1]

theorem tagPM_cost {f0 f1 : List Bool → Costed (Option (α × List Bool))}
    {f0c f1c : List Bool → ℕ} (h0 : ∀ l, (f0 l).cost = f0c l) (h1 : ∀ l, (f1 l).cost = f1c l) :
    ∀ (l : List Bool), (tagPM f0 f1 l).cost = tagPC f0c f1c l
  | [] => rfl
  | false :: l => by simp [tagPM, tagPC, h0]
  | true :: l => by simp [tagPM, tagPC, h1]

def decodeNodeM : List Bool → Costed (Option (Node × List Bool)) :=
  tagPM (bindPM decodeNatM (fun i => purePM (.src i)))
    (bindPM decodeNatM (fun f => bindPM (decodeListM decodeNatM) (fun args => purePM (.app f args))))

theorem decodeNodeM_val (l : List Bool) : (decodeNodeM l).val = decodeNode l :=
  tagPM_val (fun l => bindPM_val decodeNatM_val (fun i => purePM_val (Node.src i)) l)
    (fun l => bindPM_val decodeNatM_val (fun f => bindPM_val (decodeListM_val decodeNatM_val)
      (fun args => purePM_val (Node.app f args))) l) l

theorem decodeNodeM_cost (l : List Bool) : (decodeNodeM l).cost = decodeNodeC l :=
  tagPM_cost (fun l => bindPM_cost decodeNatM_val decodeNatM_cost (fun i => purePM_cost (Node.src i)) l)
    (fun l => bindPM_cost decodeNatM_val decodeNatM_cost (fun f =>
      bindPM_cost (decodeListM_val decodeNatM_val) (decodeListM_cost decodeNatM_val decodeNatM_cost)
        (fun args => purePM_cost (Node.app f args))) l) l

def decodeInstanceM : List Bool → Costed (Option (Instance × List Bool)) :=
  bindPM (decodeListM decodeNatM) (fun sources =>
    bindPM (decodeListM decodePairM) (fun symbols =>
      bindPM (decodeListM decodeNodeM) (fun nodes =>
        bindPM decodeNatM (fun x =>
          bindPM decodeNatM (fun y =>
            bindPM decodeNatM (fun t =>
              bindPM (decodeListM decodePairM) (fun tests =>
                purePM ⟨sources, symbols, nodes, x, y, t, tests⟩)))))))

theorem decodeInstanceM_val (l : List Bool) : (decodeInstanceM l).val = decodeInstance l :=
  bindPM_val (decodeListM_val decodeNatM_val) (fun _ =>
    bindPM_val (decodeListM_val decodePairM_val) (fun _ =>
      bindPM_val (decodeListM_val decodeNodeM_val) (fun _ =>
        bindPM_val decodeNatM_val (fun _ =>
          bindPM_val decodeNatM_val (fun _ =>
            bindPM_val decodeNatM_val (fun _ =>
              bindPM_val (decodeListM_val decodePairM_val) (fun _ =>
                purePM_val _))))))) l

theorem decodeInstanceM_cost (l : List Bool) : (decodeInstanceM l).cost = decodeInstanceC l :=
  bindPM_cost (decodeListM_val decodeNatM_val) (decodeListM_cost decodeNatM_val decodeNatM_cost)
    (fun _ =>
    bindPM_cost (decodeListM_val decodePairM_val) (decodeListM_cost decodePairM_val decodePairM_cost)
      (fun _ =>
      bindPM_cost (decodeListM_val decodeNodeM_val) (decodeListM_cost decodeNodeM_val decodeNodeM_cost)
        (fun _ =>
        bindPM_cost decodeNatM_val decodeNatM_cost (fun _ =>
          bindPM_cost decodeNatM_val decodeNatM_cost (fun _ =>
            bindPM_cost decodeNatM_val decodeNatM_cost (fun _ =>
              bindPM_cost (decodeListM_val decodePairM_val)
                (decodeListM_cost decodePairM_val decodePairM_cost)
                (fun _ => purePM_cost _))))))) l

def decodeGM : List Bool → Costed (Option (GInstance × List Bool)) :=
  bindPM decodeInstanceM (fun base => bindPM (decodeListM decodeNatM) (fun outs => purePM ⟨base, outs⟩))

theorem decodeGM_val (l : List Bool) : (decodeGM l).val = decodeG l :=
  bindPM_val decodeInstanceM_val (fun _ =>
    bindPM_val (decodeListM_val decodeNatM_val) (fun _ => purePM_val _)) l

theorem decodeGM_cost (l : List Bool) : (decodeGM l).cost = decodeGC l :=
  bindPM_cost decodeInstanceM_val decodeInstanceM_cost (fun _ =>
    bindPM_cost (decodeListM_val decodeNatM_val) (decodeListM_cost decodeNatM_val decodeNatM_cost)
      (fun _ => purePM_cost _)) l

def decodePair'M : List Bool → Costed (Option ((ℕ × GInstance) × List Bool)) :=
  bindPM decodeNatM (fun k => bindPM decodeGM (fun g => purePM (k, g)))

theorem decodePair'M_val (l : List Bool) : (decodePair'M l).val = decodePair' l :=
  bindPM_val decodeNatM_val (fun k => bindPM_val decodeGM_val (fun g => purePM_val (k, g))) l

theorem decodePair'M_cost (l : List Bool) : (decodePair'M l).cost = decodePair'C l :=
  bindPM_cost decodeNatM_val decodeNatM_cost (fun k =>
    bindPM_cost decodeGM_val decodeGM_cost (fun g => purePM_cost (k, g))) l

/-- `decodeInput`: the parse, then one match on the remainder. -/
def decodeInputM (l : List Bool) : Costed (Option (ℕ × GInstance)) := do
  let r ← decodePair'M l
  tick 1
  match r with
  | some (kg, []) => return some kg
  | _ => return none

theorem decodeInputM_val (l : List Bool) : (decodeInputM l).val = decodeInput l := by
  simp only [decodeInputM, decodeInput, bind_val, decodePair'M_val]
  cases decodePair' l with
  | none => rfl
  | some p =>
      obtain ⟨kg, rest⟩ := p
      cases rest <;> rfl

theorem decodeInputM_cost (l : List Bool) : (decodeInputM l).cost = decodeInputC l := by
  simp only [decodeInputM, decodeInputC, bind_cost, decodePair'M_cost, decodePair'M_val, tick_cost]
  cases decodePair' l with
  | none => rfl
  | some p =>
      obtain ⟨kg, rest⟩ := p
      cases rest <;> rfl

/-- **The parser's cost function is the step count of the instrumented parser** on every bit
string: value and cost agree with `decodeInput` and `decodeInputC`. -/
theorem decodeInputM_spec (l : List Bool) :
    (decodeInputM l).val = decodeInput l ∧ (decodeInputM l).cost = decodeInputC l :=
  ⟨decodeInputM_val l, decodeInputM_cost l⟩

/-- The instrumented parser executes at most `225 · |l|² + 226` primitive steps. -/
theorem decodeInputM_steps (l : List Bool) : (decodeInputM l).cost ≤ 225 * l.length ^ 2 + 226 := by
  rw [decodeInputM_cost]; exact decodeInputC_le l

end DisequalityDispersion.Encoded
