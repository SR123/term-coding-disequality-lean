import Core

/-! # The step-counting monad

`Costed α` is a value together with the number of primitive steps charged to compute it.
An *instrumented program* is a program written in this monad in which every primitive
operation charges its steps (`tick`) exactly where it is executed; `bind` adds the steps of
the two parts.  The modules `ParsingExec.lean` and `UnitFlowExec.lean` re-implement the
executable definitions of the parser and of the augmenting-path algorithm as instrumented
programs and prove that (i) the value computed is the pure definition and (ii) the step count
is the cost function of `ParsingCost.lean` / `UnitFlowCost.lean`.  This links the charged
cost expressions to the execution of concrete programs whose only primitives are the
declared ones; the simulation of those primitives on a fixed machine is the remaining
obligation stated in the return report. -/

namespace DisequalityDispersion

/-- A value together with the number of primitive steps charged to compute it. -/
structure Costed (α : Type) where
  val : α
  cost : ℕ

namespace Costed

def pure {α : Type} (a : α) : Costed α := ⟨a, 0⟩

def bind {α β : Type} (x : Costed α) (f : α → Costed β) : Costed β :=
  ⟨(f x.val).val, x.cost + (f x.val).cost⟩

instance : Monad Costed where
  pure := Costed.pure
  bind := Costed.bind

/-- Charge `n` primitive steps. -/
def tick (n : ℕ) : Costed Unit := ⟨(), n⟩

@[simp] theorem pure_val {α : Type} (a : α) : (Pure.pure a : Costed α).val = a := rfl
@[simp] theorem pure_cost {α : Type} (a : α) : (Pure.pure a : Costed α).cost = 0 := rfl
@[simp] theorem bind_val {α β : Type} (x : Costed α) (f : α → Costed β) :
    (x >>= f).val = (f x.val).val := rfl
@[simp] theorem bind_cost {α β : Type} (x : Costed α) (f : α → Costed β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl
@[simp] theorem tick_val (n : ℕ) : (tick n).val = () := rfl
@[simp] theorem tick_cost (n : ℕ) : (tick n).cost = n := rfl

/-- Run a computation at every element, charging `k` per cell, keeping the elements whose
result is `true` (a full scan). -/
def filterM {α : Type} (k : ℕ) (p : α → Costed Bool) : List α → Costed (List α)
  | [] => Pure.pure []
  | a :: l => do
      tick k
      let b ← p a
      let r ← filterM k p l
      Pure.pure (if b then a :: r else r)

/-- A full scan deciding whether some element satisfies `p`. -/
def anyM {α : Type} (k : ℕ) (p : α → Costed Bool) : List α → Costed Bool
  | [] => Pure.pure false
  | a :: l => do
      tick k
      let b ← p a
      let r ← anyM k p l
      Pure.pure (b || r)

/-- A full scan returning the first element satisfying `p`. -/
def findM {α : Type} (k : ℕ) (p : α → Costed Bool) : List α → Costed (Option α)
  | [] => Pure.pure none
  | a :: l => do
      tick k
      let b ← p a
      let r ← findM k p l
      Pure.pure (if b then some a else r)

theorem filterM_val {α : Type} (k : ℕ) (p : α → Costed Bool) (q : α → Bool)
    (hp : ∀ a, (p a).val = q a) : ∀ (l : List α), (filterM k p l).val = l.filter q
  | [] => rfl
  | a :: l => by
      simp only [filterM, bind_val, pure_val, hp, List.filter_cons]
      rw [filterM_val k p q hp l]

theorem filterM_cost {α : Type} (k : ℕ) (p : α → Costed Bool) (pc : α → ℕ)
    (hp : ∀ a, (p a).cost = pc a) : ∀ (l : List α),
    (filterM k p l).cost = (l.map (fun a => k + pc a)).sum
  | [] => rfl
  | a :: l => by
      simp only [filterM, bind_cost, tick_cost, pure_cost, hp, List.map_cons, List.sum_cons]
      rw [filterM_cost k p pc hp l]
      omega

theorem anyM_val {α : Type} (k : ℕ) (p : α → Costed Bool) (q : α → Bool)
    (hp : ∀ a, (p a).val = q a) : ∀ (l : List α), (anyM k p l).val = l.any q
  | [] => rfl
  | a :: l => by
      simp only [anyM, bind_val, pure_val, hp, List.any_cons]
      rw [anyM_val k p q hp l]

theorem anyM_cost {α : Type} (k : ℕ) (p : α → Costed Bool) (pc : α → ℕ)
    (hp : ∀ a, (p a).cost = pc a) : ∀ (l : List α),
    (anyM k p l).cost = (l.map (fun a => k + pc a)).sum
  | [] => rfl
  | a :: l => by
      simp only [anyM, bind_cost, tick_cost, pure_cost, hp, List.map_cons, List.sum_cons]
      rw [anyM_cost k p pc hp l]
      omega

theorem findM_val {α : Type} (k : ℕ) (p : α → Costed Bool) (q : α → Bool)
    (hp : ∀ a, (p a).val = q a) : ∀ (l : List α), (findM k p l).val = l.find? q
  | [] => rfl
  | a :: l => by
      simp only [findM, bind_val, pure_val, hp, List.find?_cons]
      rw [findM_val k p q hp l]
      cases q a <;> rfl

theorem findM_cost {α : Type} (k : ℕ) (p : α → Costed Bool) (pc : α → ℕ)
    (hp : ∀ a, (p a).cost = pc a) : ∀ (l : List α),
    (findM k p l).cost = (l.map (fun a => k + pc a)).sum
  | [] => rfl
  | a :: l => by
      simp only [findM, bind_cost, tick_cost, pure_cost, hp, List.map_cons, List.sum_cons]
      rw [findM_cost k p pc hp l]
      omega

/-- Map with a computation at every element, charging `k` per cell. -/
def mapM {α β : Type} (k : ℕ) (f : α → Costed β) : List α → Costed (List β)
  | [] => Pure.pure []
  | a :: l => do
      tick k
      let b ← f a
      let r ← mapM k f l
      Pure.pure (b :: r)

theorem mapM_val {α β : Type} (k : ℕ) (f : α → Costed β) (g : α → β)
    (hf : ∀ a, (f a).val = g a) : ∀ (l : List α), (mapM k f l).val = l.map g
  | [] => rfl
  | a :: l => by
      simp only [mapM, bind_val, pure_val, hf, List.map_cons]
      rw [mapM_val k f g hf l]

theorem mapM_cost {α β : Type} (k : ℕ) (f : α → Costed β) (fc : α → ℕ)
    (hf : ∀ a, (f a).cost = fc a) : ∀ (l : List α),
    (mapM k f l).cost = (l.map (fun a => k + fc a)).sum
  | [] => rfl
  | a :: l => by
      simp only [mapM, bind_cost, tick_cost, pure_cost, hf, List.map_cons, List.sum_cons]
      rw [mapM_cost k f fc hf l]
      omega

/-- A full scan deciding whether every element satisfies `p`. -/
def allM {α : Type} (k : ℕ) (p : α → Costed Bool) : List α → Costed Bool
  | [] => Pure.pure true
  | a :: l => do
      tick k
      let b ← p a
      let r ← allM k p l
      Pure.pure (b && r)

theorem allM_val {α : Type} (k : ℕ) (p : α → Costed Bool) (q : α → Bool)
    (hp : ∀ a, (p a).val = q a) : ∀ (l : List α), (allM k p l).val = l.all q
  | [] => rfl
  | a :: l => by
      simp only [allM, bind_val, pure_val, hp, List.all_cons]
      rw [allM_val k p q hp l]

theorem allM_cost {α : Type} (k : ℕ) (p : α → Costed Bool) (pc : α → ℕ)
    (hp : ∀ a, (p a).cost = pc a) : ∀ (l : List α),
    (allM k p l).cost = (l.map (fun a => k + pc a)).sum
  | [] => rfl
  | a :: l => by
      simp only [allM, bind_cost, tick_cost, pure_cost, hp, List.map_cons, List.sum_cons]
      rw [allM_cost k p pc hp l]
      omega

end Costed
end DisequalityDispersion
