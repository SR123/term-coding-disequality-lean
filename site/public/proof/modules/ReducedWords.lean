import EncodedComputable

/-! # Reduced words versus arbitrary signed lists (T3, classical-input bridge)

The classical input (Bridson–Wilton, from Slobodskoi) concerns freely reduced
words over the generators of one fixed finite presentation.  The Lean
hypothesis of `undecidable_hard_threshold` is stated on all signed lists.
This module supplies the bridge in both directions:

* `Reduced w` (executable `reducedB`, primitive recursive): no two adjacent
  letters are formal inverses; reduced words form a `Primcodable` subtype;
* `reduce w`: computable stack-based free reduction with
  `presentedWord rels (reduce w) = presentedWord rels w` and `Reduced (reduce w)`;
* `hasFiniteQuotient_reduce`: finite-quotient separation is invariant under
  free reduction;
* `not_computable_iff_reduced`: the noncomputability hypothesis on reduced
  words is equivalent to the hypothesis on all signed lists.  The inclusion of
  reduced words is the identity (computable), and `reduce` is the computable
  translation in the other direction. -/

namespace DisequalityDispersion

variable {S : Type}

/-- Formal inverse of a signed letter. -/
def Letter.inv (l : Letter S) : Letter S := (l.1, !l.2)

theorem Letter.inv_inv (l : Letter S) : Letter.inv (Letter.inv l) = l := by
  rcases l with ⟨i, b⟩
  simp [Letter.inv]

theorem Letter.inv_eq_iff (a b : Letter S) : a = Letter.inv b ↔ b = Letter.inv a := by
  constructor
  · rintro rfl; rw [Letter.inv_inv]
  · rintro rfl; rw [Letter.inv_inv]

theorem groupLetter_inv {Q : Type*} [Group Q] (g : S → Q) (l : Letter S) :
    groupLetter g (Letter.inv l) = (groupLetter g l)⁻¹ := by
  rcases l with ⟨i, b⟩
  cases b <;> simp [groupLetter, Letter.inv]

theorem groupWord_append {Q : Type*} [Group Q] (g : S → Q) (v w : List (Letter S)) :
    groupWord g (v ++ w) = groupWord g v * groupWord g w := by
  simp [groupWord, List.map_append, List.prod_append]

section reduction
variable [DecidableEq S]

/-- The next letter (if any) is not the formal inverse of the current one. -/
def headOk (a : Letter S) (l : List (Letter S)) : Bool :=
  match l.head? with
  | none => true
  | some b => decide (b ≠ Letter.inv a)

/-- Executable check that no two adjacent letters are formal inverses. -/
def reducedB : List (Letter S) → Bool
  | [] => true
  | a :: l => headOk a l && reducedB l

/-- Freely reduced signed words. -/
def Reduced (w : List (Letter S)) : Prop := reducedB w = true

instance : DecidablePred (Reduced (S := S)) :=
  fun w => inferInstanceAs (Decidable (reducedB w = true))

theorem headOk_iff (a : Letter S) (l : List (Letter S)) :
    headOk a l = true ↔ ∀ y ∈ l.head?, y ≠ Letter.inv a := by
  cases h : l.head? with
  | none => simp [headOk, h]
  | some b => simp [headOk, h]

/-- Reduced words are exactly the chains of the adjacency relation. -/
theorem reduced_iff_isChain (w : List (Letter S)) :
    Reduced w ↔ w.IsChain (fun a b => b ≠ Letter.inv a) := by
  unfold Reduced
  induction w with
  | nil => simp [reducedB]
  | cons a l ih =>
      rw [List.isChain_cons, ← ih]
      simp only [reducedB, Bool.and_eq_true, headOk_iff]

/-- One step of stack-based free reduction (top of the stack first). -/
def reduceStep (stack : List (Letter S)) (l : Letter S) : List (Letter S) :=
  match stack with
  | [] => [l]
  | b :: rest => if b = Letter.inv l then rest else l :: b :: rest

/-- Free reduction of a signed word. -/
def reduce (w : List (Letter S)) : List (Letter S) := (w.foldl reduceStep []).reverse

theorem reduce_nil : reduce ([] : List (Letter S)) = [] := rfl

/-- The stack invariant: the reversed stack has the group value of the prefix read. -/
theorem foldl_reduceStep_groupWord {Q : Type*} [Group Q] (g : S → Q) (w : List (Letter S)) :
    ∀ stack : List (Letter S),
      groupWord g (w.foldl reduceStep stack).reverse =
        groupWord g stack.reverse * groupWord g w := by
  induction w with
  | nil => intro stack; simp [groupWord]
  | cons l w ih =>
      intro stack
      rw [List.foldl_cons, ih]
      have hw : groupWord g (l :: w) = groupLetter g l * groupWord g w := by
        simp [groupWord]
      rw [hw, ← mul_assoc]
      congr 1
      cases stack with
      | nil => simp [reduceStep, groupWord]
      | cons b rest =>
          simp only [reduceStep]
          split
          · rename_i hb
            rw [hb, List.reverse_cons, groupWord_append]
            simp [groupWord, groupLetter_inv]
          · rw [List.reverse_cons, groupWord_append, List.reverse_cons, groupWord_append]
            simp [groupWord, mul_assoc]

theorem groupWord_reduce {Q : Type*} [Group Q] (g : S → Q) (w : List (Letter S)) :
    groupWord g (reduce w) = groupWord g w := by
  unfold reduce
  rw [foldl_reduceStep_groupWord]
  simp [groupWord]

theorem presentedWord_reduce (rels : List (List (Letter S))) (w : List (Letter S)) :
    presentedWord rels (reduce w) = presentedWord rels w := by
  rw [presentedWord_eq, presentedWord_eq, groupWord_reduce]

/-- Finite-quotient separation is invariant under free reduction. -/
theorem hasFiniteQuotient_reduce (rels : List (List (Letter S))) (w : List (Letter S)) :
    HasFiniteQuotient rels (reduce w) ↔ HasFiniteQuotient rels w := by
  unfold HasFiniteQuotient
  rw [presentedWord_reduce]

/-- The stack stays reduced (top-first adjacency). -/
theorem foldl_reduceStep_isChain (w : List (Letter S)) :
    ∀ stack : List (Letter S), stack.IsChain (fun a b => a ≠ Letter.inv b) →
      (w.foldl reduceStep stack).IsChain (fun a b => a ≠ Letter.inv b) := by
  induction w with
  | nil => intro stack h; simpa using h
  | cons l w ih =>
      intro stack h
      rw [List.foldl_cons]
      apply ih
      cases stack with
      | nil => exact List.isChain_singleton l
      | cons b rest =>
          simp only [reduceStep]
          split
          · exact h.tail
          · rename_i hb
            rw [List.isChain_cons]
            refine ⟨?_, h⟩
            intro y hy
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            subst hy
            intro hl
            exact hb ((Letter.inv_eq_iff _ _).mp hl)

theorem reduced_reduce (w : List (Letter S)) : Reduced (reduce w) := by
  rw [reduced_iff_isChain]
  unfold reduce
  rw [List.isChain_reverse]
  exact foldl_reduceStep_isChain w [] List.isChain_nil

end reduction

/-! ### Primitive recursiveness and the transfer of the classical hypothesis -/

section computable
variable {d : ℕ}

theorem primrec_letterInv : Primrec (Letter.inv (S := Fin d)) :=
  (Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)).of_eq (fun _ => rfl)

theorem primrec_headOk : Primrec₂ (headOk (S := Fin d)) := by
  apply Primrec₂.mk
  have hg : Primrec₂ fun (p : Letter (Fin d) × List (Letter (Fin d))) (b : Letter (Fin d)) =>
      decide (b ≠ Letter.inv p.1) := by
    have := (Primrec.eq.comp (Primrec.snd (α := Letter (Fin d) × List (Letter (Fin d)))
      (β := Letter (Fin d))) (primrec_letterInv.comp (Primrec.fst.comp Primrec.fst))).not
    exact Primrec₂.mk (this.decide.of_eq (fun p => by simp))
  have := Primrec.option_casesOn (Primrec.list_head?.comp Primrec.snd) (Primrec.const true) hg
  refine this.of_eq (fun p => ?_)
  rcases p with ⟨a, l⟩
  cases h : l.head? <;> simp [headOk, h]

theorem primrec_reducedB : Primrec (reducedB (S := Fin d)) := by
  have hh : Primrec₂ fun (_ : List (Letter (Fin d)))
      (q : Letter (Fin d) × (List (Letter (Fin d)) × Bool)) => headOk q.1 q.2.1 && q.2.2 := by
    apply Primrec₂.mk
    have hc : Primrec fun p : List (Letter (Fin d)) ×
        (Letter (Fin d) × (List (Letter (Fin d)) × Bool)) => headOk p.2.1 p.2.2.1 :=
      primrec_headOk.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    have := Primrec.cond hc (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const false)
    refine this.of_eq (fun p => ?_)
    cases headOk p.2.1 p.2.2.1 <;> rfl
  have := Primrec.list_rec Primrec.id (Primrec.const true) hh
  simp only [id_eq] at this
  refine this.of_eq (fun w => ?_)
  induction w with
  | nil => rfl
  | cons a l ih =>
      show (headOk a l && _) = (headOk a l && reducedB l)
      rw [ih]

theorem primrecPred_reduced : PrimrecPred (Reduced (S := Fin d)) :=
  Primrec.primrecPred (primrec_reducedB.of_eq (fun w => by simp [Reduced]))

/-- Reduced words as a `Primcodable` subtype. -/
instance instPrimcodableReduced : Primcodable {w : List (Letter (Fin d)) // Reduced w} :=
  Primcodable.subtype primrecPred_reduced

theorem primrec_reduceStep : Primrec₂ (reduceStep (S := Fin d)) := by
  apply Primrec₂.mk
  have hc : PrimrecPred fun r : (List (Letter (Fin d)) × Letter (Fin d)) ×
      (Letter (Fin d) × List (Letter (Fin d))) => r.2.1 = Letter.inv r.1.2 :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (primrec_letterInv.comp (Primrec.snd.comp Primrec.fst))
  have hh : Primrec₂ fun (q : List (Letter (Fin d)) × Letter (Fin d))
      (p : Letter (Fin d) × List (Letter (Fin d))) =>
      if p.1 = Letter.inv q.2 then p.2 else q.2 :: p.1 :: p.2 := by
    apply Primrec₂.mk
    exact Primrec.ite hc (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
  have := Primrec.list_casesOn (f := fun q : List (Letter (Fin d)) × Letter (Fin d) => q.1)
    (g := fun q => [q.2]) Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) hh
  refine this.of_eq (fun q => ?_)
  rcases q with ⟨s, l⟩
  cases s with
  | nil => rfl
  | cons b rest => rfl

theorem primrec_reduce : Primrec (reduce (S := Fin d)) := by
  have := Primrec.list_foldl (f := fun w : List (Letter (Fin d)) => w)
    (g := fun _ => ([] : List (Letter (Fin d))))
    (h := fun _ (p : List (Letter (Fin d)) × Letter (Fin d)) => reduceStep p.1 p.2)
    Primrec.id (Primrec.const []) (Primrec₂.mk (primrec_reduceStep.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
  exact Primrec.list_reverse.comp this

theorem computable_reduce : Computable (reduce (S := Fin d)) := primrec_reduce.to_comp

/-- **Transfer of the classical input.**  Noncomputability of finite-quotient
separation on freely reduced words is equivalent to noncomputability on all
signed lists: reduced words include into all words by the identity, and
`reduce` is a computable translation back that preserves the presented element. -/
theorem not_computable_iff_reduced (rels : List (List (Letter (Fin d)))) :
    ¬ ComputablePred (fun w : {w : List (Letter (Fin d)) // Reduced w} =>
        HasFiniteQuotient rels w.1) ↔
      ¬ ComputablePred (HasFiniteQuotient rels) := by
  constructor
  · intro h hall
    apply h
    obtain ⟨f, hf, hpf⟩ := ComputablePred.computable_iff.mp hall
    refine ComputablePred.computable_iff.mpr
      ⟨fun w => f w.1, hf.comp (Primrec.subtype_val (hp := primrecPred_reduced)).to_comp, ?_⟩
    funext w
    exact congrFun hpf w.1
  · intro h hred
    apply h
    obtain ⟨f, hf, hpf⟩ := ComputablePred.computable_iff.mp hred
    refine ComputablePred.computable_iff.mpr
      ⟨fun w => f ⟨reduce w, reduced_reduce w⟩,
        hf.comp (Primrec.subtype_mk (hp := primrecPred_reduced) primrec_reduce).to_comp, ?_⟩
    funext w
    have := congrFun hpf ⟨reduce w, reduced_reduce w⟩
    simp only at this
    rw [← hasFiniteQuotient_reduce rels w, this]

end computable

end DisequalityDispersion
