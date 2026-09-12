import MengerTheorem
import DegreeThreshold

/-! # Menger's theorem on the term DAG: the routing input is a theorem

`MengerInput outputs tests` (GeneralRouting) asked for a routing table with
`cutSize outputs tests` vertex-disjoint source paths.  Here it is proved from
the abstract `Menger.menger`: the term DAG of the finite support with the
argument edges, terminal sets = outputs and sources; `Avoids` is reachability,
`IsCut` is separation, and disjoint walks assemble into a `RoutingData`. -/

namespace DisequalityDispersion
variable {V F : Type} {arity : F → ℕ}

/-! ### Term size: walks along argument edges never repeat a vertex -/

/-- A size measure making every argument strictly smaller. -/
def Term.size : Term V F arity → ℕ
  | .var _ => 0
  | .app _ ts => (Finset.univ.sup fun i => Term.size (ts i)) + 1

theorem Term.size_arg_lt (f : F) (ts : Fin (arity f) → Term V F arity) (i : Fin (arity f)) :
    (ts i).size < (Term.app f ts).size :=
  Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (ts i).size) (Finset.mem_univ i))

theorem isArg_size_lt {u t : Term V F arity} (h : IsArg u t) : u.size < t.size := by
  obtain ⟨f, ts, i, rfl, rfl⟩ := h
  exact Term.size_arg_lt f ts i

section bridge
open Classical

/-- The argument edges inside a finite set of terms. -/
noncomputable def argEdges (S : Finset (Term V F arity)) :
    Finset (Term V F arity × Term V F arity) :=
  (S ×ˢ S).filter (fun p => IsArg p.2 p.1)

theorem mem_argEdges (S : Finset (Term V F arity)) (t u : Term V F arity) :
    (t, u) ∈ argEdges S ↔ t ∈ S ∧ u ∈ S ∧ IsArg u t := by
  simp [argEdges, and_assoc]

/-- The source vertices inside `S`. -/
noncomputable def varVerts (S : Finset (Term V F arity)) : Finset (Term V F arity) :=
  S.filter (fun t => ∃ v, t = Term.var v)

theorem mem_varVerts (S : Finset (Term V F arity)) (t : Term V F arity) :
    t ∈ varVerts S ↔ t ∈ S ∧ ∃ v, t = Term.var v := by
  simp [varVerts]

/-- Walks along argument edges have no repeated vertices. -/
theorem walk_nodup (S : Finset (Term V F arity)) (l : List (Term V F arity))
    (h : l.IsChain (Menger.Adj (argEdges S))) : l.Nodup := by
  have h1 : l.IsChain (fun a b : Term V F arity => b.size < a.size) :=
    h.imp (fun a b hab => isArg_size_lt ((mem_argEdges S a b).mp hab).2.2)
  have h2 : l.Pairwise (fun a b : Term V F arity => b.size < a.size) := by
    haveI : Trans (fun a b : Term V F arity => b.size < a.size)
        (fun a b : Term V F arity => b.size < a.size)
        (fun a b : Term V F arity => b.size < a.size) := ⟨fun h1 h2 => lt_trans h2 h1⟩
    exact List.isChain_iff_pairwise.mp h1
  exact h2.imp (fun hab heq => by rw [heq] at hab; exact lt_irrefl _ hab)

/-- A walk from `{t}` to the sources avoiding `K` is exactly `Avoids K t`. -/
theorem walk_avoids (S : Finset (Term V F arity)) (K : Finset (Term V F arity)) :
    ∀ (l : List (Term V F arity)) (t : Term V F arity),
      Menger.Walk (argEdges S) {t} (varVerts S) K l → Avoids K t
  | [], t, hl => by
      obtain ⟨_, _, h⟩ := hl.head
      simp at h
  | [a], t, hl => by
      obtain ⟨a', ha', hhead⟩ := hl.head
      obtain ⟨b, hb, hlast⟩ := hl.last
      simp only [List.head?_cons, Option.some.injEq] at hhead
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      rw [Finset.mem_singleton] at ha'
      obtain ⟨hbS, v, rfl⟩ := (mem_varVerts S b).mp hb
      rw [← ha', ← hhead, hlast]
      exact Avoids.var v (hl.avoid _ (by rw [hlast]; exact List.mem_cons_self))
  | a :: b :: l, t, hl => by
      obtain ⟨a', ha', hhead⟩ := hl.head
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [Finset.mem_singleton] at ha'
      have hab := (List.isChain_cons_cons.mp hl.chain).1
      obtain ⟨_, _, f, ts, i, rfl, rfl⟩ := (mem_argEdges S a b).mp hab
      have ih := walk_avoids S K (ts i :: l) (ts i)
        ⟨(List.isChain_cons_cons.mp hl.chain).2, ⟨ts i, Finset.mem_singleton_self _, rfl⟩,
          by simpa using hl.last, fun v hv => hl.avoid v (List.mem_cons_of_mem _ hv)⟩
      rw [← ha', ← hhead]
      exact Avoids.app f ts (hl.avoid _ List.mem_cons_self) i ih

theorem avoids_walk (S : Finset (Term V F arity)) (hS : SubtermClosed S)
    (K : Finset (Term V F arity)) (t : Term V F arity) (ht : t ∈ S) (h : Avoids K t) :
    ∃ l, Menger.Walk (argEdges S) {t} (varVerts S) K l := by
  induction h with
  | var v hv =>
      refine ⟨[Term.var v], List.isChain_singleton _, ⟨_, Finset.mem_singleton_self _, rfl⟩,
        ⟨_, (mem_varVerts S _).mpr ⟨ht, v, rfl⟩, rfl⟩, ?_⟩
      intro u hu
      rw [List.mem_singleton] at hu
      rw [hu]
      exact hv
  | app f ts hn i hi ih =>
      obtain ⟨l, hl⟩ := ih (hS f ts ht i)
      obtain ⟨a, ha, hhead⟩ := hl.head
      rw [Finset.mem_singleton] at ha
      subst ha
      obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
      refine ⟨Term.app f ts :: l, ?_, ⟨_, Finset.mem_singleton_self _, rfl⟩, ?_, ?_⟩
      · rw [hys, List.isChain_cons_cons]
        refine ⟨(mem_argEdges S _ _).mpr ⟨ht, hS f ts ht i, ⟨f, ts, i, rfl, rfl⟩⟩, ?_⟩
        rw [← hys]
        exact hl.chain
      · obtain ⟨b, hb, hlast⟩ := hl.last
        refine ⟨b, hb, ?_⟩
        rw [show Term.app f ts :: l = [Term.app f ts] ++ l by simp, List.getLast?_append, hlast]
        rfl
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hn
        · exact hl.avoid u hu

/-- Separation of outputs from sources is exactly `IsCut`. -/
theorem separates_iff_isCut (S : Finset (Term V F arity)) (hS : SubtermClosed S)
    (outputs : List (Term V F arity)) (hout : ∀ t ∈ outputs, t ∈ S)
    (K : Finset (Term V F arity)) :
    Menger.Separates (argEdges S) K outputs.toFinset (varVerts S) ↔ IsCut K outputs := by
  constructor
  · intro h t ht ha
    obtain ⟨l, hl⟩ := avoids_walk S hS K t (hout t ht) ha
    apply h l
    refine ⟨hl.chain, ?_, hl.last, hl.avoid⟩
    obtain ⟨a, ha, hhead⟩ := hl.head
    rw [Finset.mem_singleton] at ha
    exact ⟨a, by rw [ha]; exact List.mem_toFinset.mpr ht, hhead⟩
  · intro h l hl
    obtain ⟨a, ha, hhead⟩ := hl.head
    exact h a (List.mem_toFinset.mp ha)
      (walk_avoids S K l a ⟨hl.chain, ⟨a, Finset.mem_singleton_self _, hhead⟩, hl.last, hl.avoid⟩)

/-! ### Assembling disjoint walks into a routing table -/

/-- The successor of `t` in a list. -/
noncomputable def nextOf : List (Term V F arity) → Term V F arity → Option (Term V F arity)
  | [], _ => none
  | [_], _ => none
  | a :: b :: l, t => if a = t then some b else nextOf (b :: l) t

theorem nextOf_cons_cons_self (a b : Term V F arity) (l : List (Term V F arity)) :
    nextOf (a :: b :: l) a = some b := by
  simp [nextOf]

theorem nextOf_cons_cons_of_ne (a b t : Term V F arity) (l : List (Term V F arity)) (h : a ≠ t) :
    nextOf (a :: b :: l) t = nextOf (b :: l) t := by
  simp [nextOf, h]

/-- Following the successors of a nonrepeating argument walk ending at `var z` is `Routed`. -/
theorem routed_of_walk (S : Finset (Term V F arity))
    (pred : Term V F arity → Option (Term V F arity)) (z : V) :
    ∀ (l : List (Term V F arity)) (a : Term V F arity),
      (a :: l).IsChain (Menger.Adj (argEdges S)) → (a :: l).Nodup →
      (a :: l).getLast? = some (Term.var z) →
      (∀ t ∈ a :: l, pred t = nextOf (a :: l) t) → Routed pred z a
  | [], a, _, _, hlast, _ => by
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      rw [hlast]
      exact Routed.start z
  | b :: l, a, hchain, hnd, hlast, hpred => by
      have hab := (List.isChain_cons_cons.mp hchain).1
      obtain ⟨_, _, f, ts, i, rfl, rfl⟩ := (mem_argEdges S a b).mp hab
      have ih := routed_of_walk S pred z l (ts i) (List.isChain_cons_cons.mp hchain).2
        (List.Nodup.of_cons hnd) (by simpa using hlast) (by
          intro t ht
          rw [hpred t (List.mem_cons_of_mem _ ht), nextOf_cons_cons_of_ne]
          intro he
          rw [he] at hnd
          exact (List.nodup_cons.mp hnd).1 ht)
      refine Routed.step z f ts i ?_ ih
      rw [hpred _ List.mem_cons_self, nextOf_cons_cons_self]

/-- **Menger's theorem for the term DAG**: the routing input of `GeneralRouting` holds. -/
theorem mengerInput [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : MengerInput outputs tests := by
  set S := tupleSupport outputs tests with hSdef
  have hS : SubtermClosed S := tupleSupport_closed outputs tests
  have hout : ∀ t ∈ outputs, t ∈ S := fun t ht => output_mem_tupleSupport outputs tests t ht
  obtain ⟨ps, hps, hd⟩ := Menger.menger (argEdges S) outputs.toFinset (varVerts S)
    (cutSize outputs tests) (fun X hX =>
      cutSize_le_card_of_isCut outputs tests X ((separates_iff_isCut S hS outputs hout X).mp hX))
  -- endpoints
  have hne : ∀ j, ps j ≠ [] := fun j => (hps j).ne_nil
  have hlast : ∀ j, ∃ v : V, (ps j).getLast? = some (Term.var v) := by
    intro j
    obtain ⟨b, hb, hlast⟩ := (hps j).last
    obtain ⟨_, v, rfl⟩ := (mem_varVerts S b).mp hb
    exact ⟨v, hlast⟩
  choose z hz using hlast
  have hnd : ∀ j, (ps j).Nodup := fun j => walk_nodup S (ps j) (hps j).chain
  -- the predecessor table: the successor inside the unique walk through `t`
  let pred : Term V F arity → Option (Term V F arity) := fun t =>
    if h : ∃ j, t ∈ ps j then nextOf (ps (Classical.choose h)) t else none
  have hpred : ∀ j, ∀ t ∈ ps j, pred t = nextOf (ps j) t := by
    intro j t ht
    have h : ∃ j, t ∈ ps j := ⟨j, ht⟩
    simp only [pred, dif_pos h]
    have hj : Classical.choose h = j := by
      by_contra hne
      exact hd _ _ hne t (Classical.choose_spec h) ht
    rw [hj]
  refine ⟨⟨cutSize outputs tests, pred, z, fun j => (ps j).head (hne j), ?_, ?_, ?_⟩, rfl⟩
  · -- distinct sources
    intro i j hij
    by_contra hne'
    have hi : Term.var (z i) ∈ ps i := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp (hz i)
      rw [hys]; simp
    have hj : Term.var (z i) ∈ ps j := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp (hz j)
      rw [hys, hij]; simp
    exact hd i j hne' _ hi hj
  · -- heads are outputs
    intro j
    obtain ⟨a, ha, hhead⟩ := (hps j).head
    have : (ps j).head (hne j) = a :=
      Option.some.inj ((List.head?_eq_some_head (hne j)).symm.trans hhead)
    show (ps j).head (hne j) ∈ outputs
    rw [this]
    exact List.mem_toFinset.mp ha
  · -- each walk is routed
    intro j
    obtain ⟨a, l, hal⟩ : ∃ a l, ps j = a :: l := by
      cases h : ps j with
      | nil => exact absurd h (hne j)
      | cons a l => exact ⟨a, l, rfl⟩
    have hhead : (ps j).head (hne j) = a := by simp [hal]
    show Routed pred (z j) ((ps j).head (hne j))
    rw [hhead]
    apply routed_of_walk S pred (z j) l a
    · rw [← hal]; exact (hps j).chain
    · rw [← hal]; exact hnd j
    · rw [← hal]; exact hz j
    · rw [← hal]; exact hpred j

end bridge

/-! ### Unconditional routing consequences -/

/-- The routing lower bound `(n/s)^ρ ≤ D` without any hypothesis. -/
theorem routing_lower_bound [Fintype V] [Fintype F] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity))
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (x : V) (n : ℕ)
    (hn : (tupleSupport outputs tests).card ≤ n) :
    (n / (tupleSupport outputs tests).card) ^ cutSize outputs tests ≤
      dispersionTuple (A := Fin n) outputs tests :=
  routing_lower_bound_of_menger outputs tests (mengerInput outputs tests) distinct x n hn

/-- The strict witness `n = s^(k+1)` without any hypothesis. -/
theorem strict_witness' [Fintype V] [Fintype F] (k : ℕ) (hk : 1 ≤ k) (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (hρ : k + 1 ≤ cutSize outputs tests) :
    2 ≤ (tupleSupport outputs tests).card ^ (k + 1) ∧
      threshold k ((tupleSupport outputs tests).card ^ (k + 1)) + 1 ≤
        dispersionTuple (A := Fin ((tupleSupport outputs tests).card ^ (k + 1))) outputs tests :=
  strict_witness k hk x y hxy outputs tests (mengerInput outputs tests) distinct hρ

/-- **Exact strict criterion at every degree** (`thm:main`, strict part), unconditional:
`StrictT k` iff no test has identical sides and `k + 1 ≤ ρ`. -/
theorem strict_degree_iff' [Fintype V] [Fintype F] (k : ℕ) (hk : 2 ≤ k) (x y : V) (hxy : x ≠ y)
    (outputs : List (Term V F arity)) (tests : List (Term V F arity × Term V F arity))
    (hx : Term.var x ∈ outputs) (hy : Term.var y ∈ outputs) (hguard : (.var x, .var y) ∈ tests) :
    StrictT k outputs tests ↔ (∀ uv ∈ tests, uv.1 ≠ uv.2) ∧ k + 1 ≤ cutSize outputs tests :=
  strict_degree_iff k hk x y hxy outputs tests hx hy hguard (mengerInput outputs tests)

end DisequalityDispersion
