import TableSearch
import DegreeCompiler

/-! # Primitive recursiveness of the table search (R6)

Every function of `TableSearch.lean` is built from lists of naturals; here
each is shown primitive recursive with mathlib's `Primrec` combinators.  The
result is `primrec_lowerAtG`/`primrec_strictAtG`: the finite threshold tests
at one alphabet size are primitive recursive in `(degree, instance, alphabet)`.
Consequences (RE of the degree languages, no computable alphabet bound) are in
`GeneralSemidecision.lean`. -/

namespace DisequalityDispersion.Encoded

open Primrec

theorem primrec_pow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow

/-! ### Enumerators -/

theorem allLists_eq_rec (n : ℕ) : ∀ L : ℕ, allLists n L = Nat.rec (motive := fun _ => List (List ℕ))
    [[]] (fun _ IH => IH.flatMap (fun l => (List.range n).map (fun v => v :: l))) L
  | 0 => rfl
  | L + 1 => by
      show (allLists n L).flatMap _ = (Nat.rec (motive := fun _ => List (List ℕ)) [[]] _ L).flatMap _
      rw [allLists_eq_rec n L]

theorem primrec_allLists : Primrec₂ allLists := by
  have hg : Primrec fun q : ℕ × (ℕ × List (List ℕ)) =>
      q.2.2.flatMap (fun l => (List.range q.1).map (fun v => v :: l)) := by
    apply list_flatMap (snd.comp snd)
    show Primrec fun r : (ℕ × (ℕ × List (List ℕ))) × List ℕ =>
      (List.range r.1.1).map (fun v => v :: r.2)
    apply list_map (list_range.comp (fst.comp fst))
    show Primrec fun s : ((ℕ × (ℕ × List (List ℕ))) × List ℕ) × ℕ => s.2 :: s.1.2
    exact list_cons.comp snd (snd.comp fst)
  have := nat_rec (f := fun _ : ℕ => ([[]] : List (List ℕ)))
    (g := fun (n : ℕ) (p : ℕ × List (List ℕ)) =>
      p.2.flatMap (fun l => (List.range n).map (fun v => v :: l))) (const _) hg
  exact this.of_eq (fun n L => (allLists_eq_rec n L).symm)

theorem cartesian_eq_foldr {α : Type} : ∀ xss : List (List α), cartesian xss =
    xss.foldr (fun xs acc => xs.flatMap (fun x => acc.map (fun l => x :: l))) [[]]
  | [] => rfl
  | xs :: xss => by
      show xs.flatMap _ = xs.flatMap _
      rw [cartesian_eq_foldr xss]

theorem primrec_cartesian {α : Type} [Primcodable α] : Primrec (cartesian (α := α)) := by
  have hh : Primrec fun q : List (List α) × (List α × List (List α)) =>
      q.2.1.flatMap (fun x => q.2.2.map (fun l => x :: l)) := by
    apply list_flatMap (fst.comp snd)
    show Primrec fun r : (List (List α) × (List α × List (List α))) × α =>
      r.1.2.2.map (fun l => r.2 :: l)
    apply list_map (snd.comp (snd.comp fst))
    show Primrec fun s : ((List (List α) × (List α × List (List α))) × α) × List α => s.1.2 :: s.2
    exact list_cons.comp (snd.comp fst) snd
  have := list_foldr (f := fun xss : List (List α) => xss) (g := fun _ => ([[]] : List (List α)))
    (h := fun (_ : List (List α)) (p : List α × List (List α)) =>
      p.1.flatMap (fun x => p.2.map (fun l => x :: l))) Primrec.id (const _) hh
  exact this.of_eq (fun xss => (cartesian_eq_foldr xss).symm)

theorem idxL_eq_foldr (n : ℕ) (l : List ℕ) :
    idxL n l = l.foldr (fun a acc => a + n * acc) 0 := rfl

theorem primrec_idxL : Primrec₂ idxL := by
  have hh : Primrec fun q : ℕ × (ℕ × ℕ) => q.2.1 + q.1 * q.2.2 :=
    nat_add.comp (fst.comp snd) (nat_mul.comp fst (snd.comp snd))
  have := list_foldr (f := fun p : ℕ × List ℕ => p.2) (g := fun _ => (0 : ℕ))
    (h := fun (p : ℕ × List ℕ) (q : ℕ × ℕ) => q.1 + p.1 * q.2) snd (const 0)
    (hh.comp (Primrec.pair (fst.comp fst) snd))
  exact this.of_eq (fun p => rfl)

/-! ### Instance projections -/

theorem primrec_instance_symbols : Primrec Instance.symbols := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).2.1 :=
    fst.comp (snd.comp Primrec.of_equiv)
  exact this.of_eq (fun γ => rfl)

theorem primrec_instance_sources : Primrec Instance.sources := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).1 := fst.comp Primrec.of_equiv
  exact this.of_eq (fun γ => rfl)

theorem primrec_instance_x : Primrec Instance.x := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).2.2.2.1 :=
    fst.comp (snd.comp (snd.comp (snd.comp Primrec.of_equiv)))
  exact this.of_eq (fun γ => rfl)

theorem primrec_instance_y : Primrec Instance.y := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).2.2.2.2.1 :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp Primrec.of_equiv))))
  exact this.of_eq (fun γ => rfl)

theorem primrec_instance_t : Primrec Instance.t := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).2.2.2.2.2.1 :=
    fst.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp Primrec.of_equiv)))))
  exact this.of_eq (fun _ => rfl)

theorem primrec_instance_tests : Primrec Instance.tests := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).2.2.2.2.2.2 :=
    snd.comp (snd.comp (snd.comp (snd.comp (snd.comp (snd.comp Primrec.of_equiv)))))
  exact this.of_eq (fun _ => rfl)

theorem primrec_instance_m : Primrec Instance.m :=
  (list_length.comp primrec_instance_symbols).of_eq (fun _ => rfl)

theorem primrec_instance_k : Primrec Instance.k :=
  (list_length.comp primrec_instance_sources).of_eq (fun _ => rfl)

theorem primrec_instance_arityOf : Primrec₂ Instance.arityOf := by
  have : Primrec fun p : Instance × ℕ => (p.1.symbols.getD p.2 (0, 0)).2 :=
    snd.comp ((list_getD (0, 0)).comp (primrec_instance_symbols.comp fst) snd)
  exact this.of_eq (fun p => rfl)

theorem primrec_ginstance_base : Primrec GInstance.base := by
  have : Primrec fun g : GInstance => (GInstance.equiv g).1 := fst.comp Primrec.of_equiv
  exact this.of_eq (fun g => rfl)

theorem primrec_ginstance_outs : Primrec GInstance.outs := by
  have : Primrec fun g : GInstance => (GInstance.equiv g).2 := snd.comp Primrec.of_equiv
  exact this.of_eq (fun g => rfl)

/-- All tables, as a function of `(n, γ)`. -/
theorem primrec_allTables : Primrec₂ allTables := by
  have hg : Primrec₂ fun (q : ℕ × Instance) (f : ℕ) => allLists q.1 (q.1 ^ q.2.arityOf f) :=
    Primrec₂.mk (primrec_allLists.comp (fst.comp fst)
      (primrec_pow.comp (fst.comp fst) (primrec_instance_arityOf.comp (snd.comp fst) snd)))
  have : Primrec fun p : ℕ × Instance =>
      cartesian ((List.range p.2.m).map (fun f => allLists p.1 (p.1 ^ p.2.arityOf f))) :=
    primrec_cartesian.comp (list_map (list_range.comp (primrec_instance_m.comp snd)) hg)
  exact this.of_eq (fun p => rfl)

/-! ### The evaluator -/

/-- Parameters of the evaluator: `((γ, n), (tabs, a))`. -/
abbrev EvalParams := (Instance × ℕ) × (List (List ℕ) × List ℕ)

theorem evalStepL_eq_cases (γ : Instance) (n : ℕ) (tabs : List (List ℕ)) (a vals : List ℕ)
    (j : ℕ) : γ.evalStepL n tabs a vals j =
      Sum.casesOn (Node.equiv (γ.nodes.getD j (.src 0)))
        (fun i => a.getD i 0)
        (fun p => (tabs.getD p.1 []).getD (idxL n (p.2.map (fun q => vals.getD q 0))) 0) := by
  unfold Instance.evalStepL
  cases γ.nodes.getD j (.src 0) <;> rfl

theorem primrec_evalStepL :
    Primrec fun t : (EvalParams × List ℕ) × ℕ =>
      t.1.1.1.1.evalStepL t.1.1.1.2 t.1.1.2.1 t.1.1.2.2 t.1.2 t.2 := by
  have hf : Primrec fun t : (EvalParams × List ℕ) × ℕ =>
      Node.equiv (t.1.1.1.1.nodes.getD t.2 (.src 0)) :=
    Primrec.of_equiv.comp ((list_getD (Node.src 0)).comp
      (primrec_instance_nodes.comp (fst.comp (fst.comp (fst.comp fst)))) snd)
  have hg : Primrec₂ fun (r : (EvalParams × List ℕ) × ℕ) (i : ℕ) => r.1.1.2.2.getD i 0 :=
    Primrec₂.mk ((list_getD 0).comp (snd.comp (snd.comp (fst.comp (fst.comp fst)))) snd)
  have hinner : Primrec₂ fun (s : ((EvalParams × List ℕ) × ℕ) × (ℕ × List ℕ)) (q : ℕ) =>
      s.1.1.2.getD q 0 :=
    Primrec₂.mk ((list_getD 0).comp (snd.comp (fst.comp (fst.comp fst))) snd)
  have hh : Primrec₂ fun (r : (EvalParams × List ℕ) × ℕ) (p : ℕ × List ℕ) =>
      (r.1.1.2.1.getD p.1 []).getD (idxL r.1.1.1.2 (p.2.map (fun q => r.1.2.getD q 0))) 0 :=
    Primrec₂.mk ((list_getD 0).comp
      ((list_getD []).comp (fst.comp (snd.comp (fst.comp (fst.comp fst)))) (fst.comp snd))
      (primrec_idxL.comp (snd.comp (fst.comp (fst.comp (fst.comp fst))))
        (list_map (snd.comp snd) hinner)))
  have := sumCasesOn hf hg hh
  exact this.of_eq (fun t => (evalStepL_eq_cases _ _ _ _ _ _).symm)

theorem primrec_evalNodesL :
    Primrec fun p : EvalParams => p.1.1.evalNodesL p.1.2 p.2.1 p.2.2 := by
  have hh : Primrec₂ fun (p : EvalParams) (q : List ℕ × ℕ) =>
      q.1 ++ [p.1.1.evalStepL p.1.2 p.2.1 p.2.2 q.1 q.2] :=
    Primrec₂.mk (list_concat.comp (fst.comp snd)
      (primrec_evalStepL.comp (Primrec.pair (Primrec.pair fst (fst.comp snd)) (snd.comp snd))))
  have := list_foldl (f := fun p : EvalParams => List.range p.1.1.nodes.length)
    (g := fun _ : EvalParams => ([] : List ℕ))
    (list_range.comp (list_length.comp (primrec_instance_nodes.comp (fst.comp fst)))) (const _) hh
  exact this.of_eq (fun p => rfl)

/-! ### Tests, tuples, counting -/

theorem list_all_eq_foldr {α : Type} (p : α → Bool) (l : List α) :
    l.all p = l.foldr (fun x b => p x && b) true := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.all_cons, ih]; rfl

theorem list_any_eq_foldr {α : Type} (p : α → Bool) (l : List α) :
    l.any p = l.foldr (fun x b => p x || b) false := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.any_cons, ih]; rfl

theorem primrec_band : Primrec₂ (fun a b : Bool => a && b) := dom_bool₂ _
theorem primrec_bor : Primrec₂ (fun a b : Bool => a || b) := dom_bool₂ _

/-- Parameters of the counting stage: `((g, n), (tabs, a))`. -/
abbrev CountParams := (GInstance × ℕ) × (List (List ℕ) × List ℕ)

theorem primrec_count_evalNodesL :
    Primrec fun p : CountParams => p.1.1.base.evalNodesL p.1.2 p.2.1 p.2.2 :=
  primrec_evalNodesL.comp (Primrec.pair (Primrec.pair (primrec_ginstance_base.comp (fst.comp fst))
    (snd.comp fst)) snd)

theorem primrec_passesL : Primrec fun p : CountParams => p.1.1.passesL p.1.2 p.2.1 p.2.2 := by
  have hv : Primrec fun q : CountParams × ((ℕ × ℕ) × Bool) =>
      q.1.1.1.base.evalNodesL q.1.1.2 q.1.2.1 q.1.2.2 := primrec_count_evalNodesL.comp fst
  have h1 : Primrec fun q : CountParams × ((ℕ × ℕ) × Bool) =>
      decide ((q.1.1.1.base.evalNodesL q.1.1.2 q.1.2.1 q.1.2.2).getD q.2.1.1 0 =
        (q.1.1.1.base.evalNodesL q.1.1.2 q.1.2.1 q.1.2.2).getD q.2.1.2 0) :=
    (Primrec.eq.comp ((list_getD 0).comp hv (fst.comp (fst.comp snd)))
      ((list_getD 0).comp hv (snd.comp (fst.comp snd)))).decide
  have hh : Primrec₂ fun (p : CountParams) (q : (ℕ × ℕ) × Bool) =>
      (decide ((p.1.1.base.evalNodesL p.1.2 p.2.1 p.2.2).getD q.1.1 0 ≠
        (p.1.1.base.evalNodesL p.1.2 p.2.1 p.2.2).getD q.1.2 0)) && q.2 := by
    apply Primrec₂.mk
    have h2 := primrec_band.comp (Primrec.not.comp h1) (snd.comp snd)
    exact h2.of_eq (fun q => by simp [decide_not])
  have := list_foldr (f := fun p : CountParams => p.1.1.base.tests) (g := fun _ => true)
    (primrec_instance_tests.comp (primrec_ginstance_base.comp (fst.comp fst))) (const true) hh
  refine this.of_eq (fun p => ?_)
  unfold GInstance.passesL
  rw [list_all_eq_foldr]

theorem primrec_outTupleL : Primrec fun p : CountParams => p.1.1.outTupleL p.1.2 p.2.1 p.2.2 := by
  have hx : Primrec fun p : CountParams => p.2.2.getD p.1.1.base.x 0 :=
    (list_getD 0).comp (snd.comp snd)
      (primrec_instance_x.comp (primrec_ginstance_base.comp (fst.comp fst)))
  have hy : Primrec fun p : CountParams => p.2.2.getD p.1.1.base.y 0 :=
    (list_getD 0).comp (snd.comp snd)
      (primrec_instance_y.comp (primrec_ginstance_base.comp (fst.comp fst)))
  have hg : Primrec₂ fun (p : CountParams) (j : ℕ) =>
      (p.1.1.base.evalNodesL p.1.2 p.2.1 p.2.2).getD j 0 :=
    Primrec₂.mk ((list_getD 0).comp (primrec_count_evalNodesL.comp fst) snd)
  have hrest : Primrec fun p : CountParams =>
      p.1.1.outs.map (fun j => (p.1.1.base.evalNodesL p.1.2 p.2.1 p.2.2).getD j 0) :=
    list_map (primrec_ginstance_outs.comp (fst.comp fst)) hg
  have := list_append.comp (list_cons.comp hx (list_cons.comp hy (const []))) hrest
  exact this.of_eq (fun p => rfl)

theorem primrec_mem_list {α : Type} [Primcodable α] [DecidableEq α] :
    PrimrecRel (fun (x : α) (l : List α) => x ∈ l) := by
  have := nat_lt.comp (list_idxOf.comp (fst : Primrec fun p : α × List α => p.1) snd)
    (list_length.comp (snd : Primrec fun p : α × List α => p.2))
  exact this.of_eq (fun p => by simp [List.idxOf_lt_length_iff])

theorem dedupList_eq_foldr {α : Type} [DecidableEq α] : ∀ l : List α,
    dedupList l = l.foldr (fun x d => if x ∈ d then d else x :: d) []
  | [] => rfl
  | x :: l => by
      show (if x ∈ dedupList l then dedupList l else x :: dedupList l) = _
      rw [dedupList_eq_foldr l]
      rfl

theorem primrec_dedupList {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupList (α := α)) := by
  have hh : Primrec₂ fun (_ : List α) (q : α × List α) =>
      if q.1 ∈ q.2 then q.2 else q.1 :: q.2 :=
    Primrec₂.mk (Primrec.ite (c := fun q : List α × (α × List α) => q.2.1 ∈ q.2.2)
      (primrec_mem_list.comp (fst.comp snd) (snd.comp snd)) (snd.comp snd)
      (list_cons.comp (fst.comp snd) (snd.comp snd)))
  have := list_foldr (f := fun l : List α => l) (g := fun _ => ([] : List α)) Primrec.id (const _) hh
  exact this.of_eq (fun l => (dedupList_eq_foldr l).symm)

/-- Parameters of the image count: `((g, n), tabs)`. -/
abbrev ImageParams := (GInstance × ℕ) × List (List ℕ)

theorem primrec_filter_pair :
    Primrec fun q : ImageParams × (List ℕ × List (List ℕ)) => (q.1.1, (q.1.2, q.2.1)) :=
  Primrec.pair (fst.comp fst) (Primrec.pair (snd.comp fst) (fst.comp snd))

theorem primrec_filter_cond :
    Primrec fun q : ImageParams × (List ℕ × List (List ℕ)) =>
      q.1.1.1.passesL q.1.1.2 q.1.2 q.2.1 := by
  have := primrec_passesL.comp primrec_filter_pair
  exact this

theorem primrec_filter_step :
    Primrec fun q : ImageParams × (List ℕ × List (List ℕ)) =>
      bif q.1.1.1.passesL q.1.1.2 q.1.2 q.2.1 then q.2.1 :: q.2.2 else q.2.2 :=
  Primrec.cond primrec_filter_cond (list_cons.comp (fst.comp snd) (snd.comp snd)) (snd.comp snd)

theorem primrec_filtered :
    Primrec fun p : ImageParams => (allLists p.1.2 p.1.1.base.k).filter (p.1.1.passesL p.1.2 p.2) := by
  have hh : Primrec₂ fun (p : ImageParams) (q : List ℕ × List (List ℕ)) =>
      bif p.1.1.passesL p.1.2 p.2 q.1 then q.1 :: q.2 else q.2 := Primrec₂.mk primrec_filter_step
  have hf : Primrec fun p : ImageParams => allLists p.1.2 p.1.1.base.k :=
    primrec_allLists.comp (snd.comp fst) (primrec_instance_k.comp (primrec_ginstance_base.comp (fst.comp fst)))
  have := list_foldr (g := fun _ : ImageParams => ([] : List (List ℕ))) hf (const _) hh
  exact this.of_eq (fun p => (List.filter_eq_foldr _ _).symm)

theorem primrec_tuple_pair :
    Primrec fun q : ImageParams × List ℕ => (q.1.1, (q.1.2, q.2)) :=
  Primrec.pair (fst.comp fst) (Primrec.pair (snd.comp fst) snd)

theorem primrec_tuple_step :
    Primrec fun q : ImageParams × List ℕ => q.1.1.1.outTupleL q.1.1.2 q.1.2 q.2 := by
  have := primrec_outTupleL.comp primrec_tuple_pair
  exact this

theorem primrec_imageCountL : Primrec fun p : ImageParams => p.1.1.imageCountL p.1.2 p.2 := by
  have hg : Primrec₂ fun (p : ImageParams) (a : List ℕ) => p.1.1.outTupleL p.1.2 p.2 a :=
    Primrec₂.mk primrec_tuple_step
  have hmap : Primrec fun p : ImageParams =>
      ((allLists p.1.2 p.1.1.base.k).filter (p.1.1.passesL p.1.2 p.2)).map
        (p.1.1.outTupleL p.1.2 p.2) :=
    list_map primrec_filtered hg
  have := list_length.comp (primrec_dedupList.comp hmap)
  exact this.of_eq (fun p => rfl)

theorem primrec_max_pair :
    Primrec fun q : (GInstance × ℕ) × (List (List ℕ) × ℕ) => (q.1, q.2.1) :=
  Primrec.pair fst (fst.comp snd)

theorem primrec_max_count :
    Primrec fun q : (GInstance × ℕ) × (List (List ℕ) × ℕ) => q.1.1.imageCountL q.1.2 q.2.1 := by
  have := primrec_imageCountL.comp primrec_max_pair
  exact this

theorem primrec_dispersionExecG : Primrec₂ GInstance.dispersionExecG := by
  have hh : Primrec₂ fun (p : GInstance × ℕ) (q : List (List ℕ) × ℕ) =>
      max (p.1.imageCountL p.2 q.1) q.2 :=
    Primrec₂.mk (nat_max.comp primrec_max_count (snd.comp snd))
  have hf : Primrec fun p : GInstance × ℕ => allTables p.2 p.1.base :=
    primrec_allTables.comp snd (primrec_ginstance_base.comp fst)
  have := list_foldr (g := fun _ : GInstance × ℕ => (0 : ℕ)) hf (const 0) hh
  exact this.of_eq (fun p => rfl)

/-! ### Validity -/

theorem primrec_nodup_decide {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec fun l : List α => decide l.Nodup := by
  have := (Primrec.eq.comp (list_length.comp (primrec_dedupList (α := α))) list_length).decide
  exact this.of_eq (fun l => by simp [nodup_iff_dedupList_length])

theorem nodeOk_eq_cases (γ : Instance) (j : ℕ) (nd : Node) :
    γ.nodeOk j nd = Sum.casesOn (Node.equiv nd)
      (fun i => decide (i < γ.k))
      (fun p => decide (p.1 < γ.m) && decide (p.2.length = γ.arityOf p.1) &&
        p.2.all (fun a => decide (a < j))) := by
  cases nd <;> rfl

theorem primrec_nodeOk : Primrec fun t : (Instance × ℕ) × Node => t.1.1.nodeOk t.1.2 t.2 := by
  have hf : Primrec fun t : (Instance × ℕ) × Node => Node.equiv t.2 := Primrec.of_equiv.comp snd
  have hg : Primrec₂ fun (r : (Instance × ℕ) × Node) (i : ℕ) => decide (i < r.1.1.k) :=
    Primrec₂.mk (nat_lt.comp snd (primrec_instance_k.comp (fst.comp (fst.comp fst)))).decide
  have hall : Primrec fun r : ((Instance × ℕ) × Node) × (ℕ × List ℕ) =>
      r.2.2.all (fun a => decide (a < r.1.1.2)) := by
    have hh : Primrec₂ fun (r : ((Instance × ℕ) × Node) × (ℕ × List ℕ)) (s : ℕ × Bool) =>
        decide (s.1 < r.1.1.2) && s.2 :=
      Primrec₂.mk (primrec_band.comp (nat_lt.comp (fst.comp snd)
        (snd.comp (fst.comp (fst.comp fst)))).decide (snd.comp snd))
    have := list_foldr (f := fun r : ((Instance × ℕ) × Node) × (ℕ × List ℕ) => r.2.2)
      (g := fun _ => true) (snd.comp snd) (const true) hh
    exact this.of_eq (fun r => by rw [list_all_eq_foldr])
  have hh : Primrec₂ fun (r : (Instance × ℕ) × Node) (p : ℕ × List ℕ) =>
      decide (p.1 < r.1.1.m) && decide (p.2.length = r.1.1.arityOf p.1) &&
        p.2.all (fun a => decide (a < r.1.2)) :=
    Primrec₂.mk (primrec_band.comp (primrec_band.comp
      (nat_lt.comp (fst.comp snd) (primrec_instance_m.comp (fst.comp (fst.comp fst)))).decide
      (Primrec.eq.comp (list_length.comp (snd.comp snd))
        (primrec_instance_arityOf.comp (fst.comp (fst.comp fst)) (fst.comp snd))).decide) hall)
  have := sumCasesOn hf hg hh
  exact this.of_eq (fun t => (nodeOk_eq_cases _ _ _).symm)

theorem primrec_nodesOk : Primrec Instance.nodesOk := by
  have hh : Primrec₂ fun (γ : Instance) (q : ℕ × Bool) =>
      γ.nodeOk q.1 (γ.nodes.getD q.1 (.src 0)) && q.2 :=
    Primrec₂.mk (primrec_band.comp (primrec_nodeOk.comp (Primrec.pair (Primrec.pair fst (fst.comp snd))
      ((list_getD (Node.src 0)).comp (primrec_instance_nodes.comp fst) (fst.comp snd))))
      (snd.comp snd))
  have := list_foldr (f := fun γ : Instance => List.range γ.nodes.length) (g := fun _ => true)
    (list_range.comp (list_length.comp primrec_instance_nodes)) (const true) hh
  exact this.of_eq (fun γ => by unfold Instance.nodesOk; rw [list_all_eq_foldr])

theorem primrec_node_src : Primrec Node.src :=
  (Primrec.of_equiv_symm.comp (Primrec.sumInl (α := ℕ) (β := ℕ × List ℕ))).of_eq (fun _ => rfl)

theorem primrec_guardOk : Primrec Instance.guardOk := by
  have hh : Primrec₂ fun (γ : Instance) (q : (ℕ × ℕ) × Bool) =>
      (decide (γ.nodes.getD q.1.1 (.app 0 []) = .src γ.x) &&
        decide (γ.nodes.getD q.1.2 (.app 0 []) = .src γ.y)) || q.2 := by
    apply Primrec₂.mk
    refine primrec_bor.comp (primrec_band.comp ?_ ?_) (snd.comp snd)
    · exact (Primrec.eq.comp ((list_getD (Node.app 0 [])).comp (primrec_instance_nodes.comp fst)
        (fst.comp (fst.comp snd))) (primrec_node_src.comp (primrec_instance_x.comp fst))).decide
    · exact (Primrec.eq.comp ((list_getD (Node.app 0 [])).comp (primrec_instance_nodes.comp fst)
        (snd.comp (fst.comp snd))) (primrec_node_src.comp (primrec_instance_y.comp fst))).decide
  have := list_foldr (f := fun γ : Instance => γ.tests) (g := fun _ => false)
    primrec_instance_tests (const false) hh
  exact this.of_eq (fun γ => by unfold Instance.guardOk; rw [list_any_eq_foldr])

theorem primrec_instance_isValid : Primrec Instance.isValid := by
  have h1 : Primrec fun γ : Instance => decide (2 ≤ γ.k) :=
    (nat_le.comp (const 2) primrec_instance_k).decide
  have h2 : Primrec fun γ : Instance => decide γ.sources.Nodup :=
    primrec_nodup_decide.comp primrec_instance_sources
  have hmap : Primrec fun γ : Instance => γ.symbols.map Prod.fst :=
    list_map primrec_instance_symbols (Primrec₂.mk (fst.comp snd))
  have h3 : Primrec fun γ : Instance => decide (γ.symbols.map Prod.fst).Nodup :=
    primrec_nodup_decide.comp hmap
  have h4 : Primrec fun γ : Instance => decide (γ.x < γ.k) :=
    (nat_lt.comp primrec_instance_x primrec_instance_k).decide
  have h5 : Primrec fun γ : Instance => decide (γ.y < γ.k) :=
    (nat_lt.comp primrec_instance_y primrec_instance_k).decide
  have h6 : Primrec fun γ : Instance => decide (γ.x ≠ γ.y) :=
    (Primrec.not.comp (Primrec.eq.comp primrec_instance_x primrec_instance_y).decide).of_eq
      (fun γ => by simp [decide_not])
  have h8 : Primrec fun γ : Instance => decide (γ.t < γ.nodes.length) :=
    (nat_lt.comp primrec_instance_t (list_length.comp primrec_instance_nodes)).decide
  have h9 : Primrec fun γ : Instance =>
      γ.tests.all (fun ij => decide (ij.1 < γ.nodes.length) && decide (ij.2 < γ.nodes.length)) := by
    have hh : Primrec₂ fun (γ : Instance) (q : (ℕ × ℕ) × Bool) =>
        (decide (q.1.1 < γ.nodes.length) && decide (q.1.2 < γ.nodes.length)) && q.2 :=
      Primrec₂.mk (primrec_band.comp (primrec_band.comp
        (nat_lt.comp (fst.comp (fst.comp snd))
          (list_length.comp (primrec_instance_nodes.comp fst))).decide
        (nat_lt.comp (snd.comp (fst.comp snd))
          (list_length.comp (primrec_instance_nodes.comp fst))).decide)
        (snd.comp snd))
    have := list_foldr (f := fun γ : Instance => γ.tests) (g := fun _ => true)
      primrec_instance_tests (const true) hh
    exact this.of_eq (fun γ => by rw [list_all_eq_foldr])
  have := primrec_band.comp (primrec_band.comp (primrec_band.comp (primrec_band.comp
    (primrec_band.comp (primrec_band.comp (primrec_band.comp (primrec_band.comp
      (primrec_band.comp h1 h2) h3) h4) h5) h6) primrec_nodesOk) h8) h9) primrec_guardOk
  exact this.of_eq (fun γ => rfl)

theorem primrec_ginstance_isValid : Primrec GInstance.isValid := by
  have h2 : Primrec fun g : GInstance => g.outs.all (fun j => decide (j < g.base.nodes.length)) := by
    have hh : Primrec₂ fun (g : GInstance) (q : ℕ × Bool) =>
        decide (q.1 < g.base.nodes.length) && q.2 :=
      Primrec₂.mk (primrec_band.comp (nat_lt.comp (fst.comp snd)
        (list_length.comp (primrec_instance_nodes.comp (primrec_ginstance_base.comp fst)))).decide
        (snd.comp snd))
    have := list_foldr (f := fun g : GInstance => g.outs) (g := fun _ => true)
      primrec_ginstance_outs (const true) hh
    exact this.of_eq (fun g => by rw [list_all_eq_foldr])
  have := primrec_band.comp (primrec_instance_isValid.comp primrec_ginstance_base) h2
  exact this.of_eq (fun g => rfl)

/-! ### The threshold tests -/

theorem primrec_threshold : Primrec₂ threshold := by
  have : Primrec fun p : ℕ × ℕ => p.2 ^ p.1 - p.2 ^ (p.1 - 1) :=
    nat_sub.comp (primrec_pow.comp snd fst) (primrec_pow.comp snd (nat_sub.comp fst (const 1)))
  exact this.of_eq (fun p => rfl)

/-- The lower threshold test is primitive recursive in `(k, (g, n))`. -/
theorem primrec_lowerAtG : Primrec fun p : ℕ × (GInstance × ℕ) => lowerAtG p.1 p.2.1 p.2.2 := by
  have h1 : Primrec fun p : ℕ × (GInstance × ℕ) => p.2.1.isValid :=
    primrec_ginstance_isValid.comp (fst.comp snd)
  have h2 : Primrec fun p : ℕ × (GInstance × ℕ) => decide (2 ≤ p.2.2) :=
    (nat_le.comp (const 2) (snd.comp snd)).decide
  have h3 : Primrec fun p : ℕ × (GInstance × ℕ) =>
      decide (threshold p.1 p.2.2 ≤ p.2.1.dispersionExecG p.2.2) :=
    (nat_le.comp (primrec_threshold.comp fst (snd.comp snd))
      (primrec_dispersionExecG.comp (fst.comp snd) (snd.comp snd))).decide
  have := primrec_band.comp (primrec_band.comp h1 h2) h3
  exact this.of_eq (fun p => rfl)

/-- The strict threshold test is primitive recursive in `(k, (g, n))`. -/
theorem primrec_strictAtG : Primrec fun p : ℕ × (GInstance × ℕ) => strictAtG p.1 p.2.1 p.2.2 := by
  have h1 : Primrec fun p : ℕ × (GInstance × ℕ) => p.2.1.isValid :=
    primrec_ginstance_isValid.comp (fst.comp snd)
  have h2 : Primrec fun p : ℕ × (GInstance × ℕ) => decide (2 ≤ p.2.2) :=
    (nat_le.comp (const 2) (snd.comp snd)).decide
  have h3 : Primrec fun p : ℕ × (GInstance × ℕ) =>
      decide (threshold p.1 p.2.2 + 1 ≤ p.2.1.dispersionExecG p.2.2) :=
    (nat_le.comp (succ.comp (primrec_threshold.comp fst (snd.comp snd)))
      (primrec_dispersionExecG.comp (fst.comp snd) (snd.comp snd))).decide
  have := primrec_band.comp (primrec_band.comp h1 h2) h3
  exact this.of_eq (fun p => rfl)

theorem computable_lowerAtG (k : ℕ) : Computable₂ (lowerAtG k) :=
  (primrec_lowerAtG.comp (Primrec.pair (const k) Primrec.id)).to_comp

theorem computable_strictAtG (k : ℕ) : Computable₂ (strictAtG k) :=
  (primrec_strictAtG.comp (Primrec.pair (const k) Primrec.id)).to_comp

end DisequalityDispersion.Encoded
