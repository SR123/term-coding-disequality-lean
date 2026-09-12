import SharpCut

/-! # General shared tagged routing (R3)

Given `q` vertex-disjoint source-output paths, encoded by a predecessor
function `pred` on terms (`Routed pred z t` says that following `pred`
from `t` reaches the source `var z` through immediate arguments), we build
ONE table per symbol on the tagged alphabet `Term × B`: the result tag is the
term formed from the input tags, and the payload is copied from the argument
carrying the predecessor's tag (or a default off the paths and for
nullaries).  Since rules are attached to terms, shared symbols cause no
conflict, every supported term evaluates with its own tag
(`route_eval_tag`), every test with different sides passes, and the `q`
path payloads are recovered at the outputs.  Restricting to the finite
support `S` and embedding into `Fin n` gives `(n / s)^q ≤ D(n)` for `n ≥ s`.

The existence of `ρ` disjoint paths for the minimum cut `ρ` is the finite
directed vertex Menger theorem; it is an explicit named input `MengerInput`
(see `routing_lower_bound_of_menger`), not a custom axiom. -/

namespace DisequalityDispersion

variable {V F B : Type} {arity : F → ℕ}

/-- Following `pred` from `t` reaches the source `var z` through immediate arguments. -/
inductive Routed (pred : Term V F arity → Option (Term V F arity)) : V → Term V F arity → Prop
  | start (z : V) : Routed pred z (.var z)
  | step (z : V) (f : F) (ts : Fin (arity f) → Term V F arity) (j : Fin (arity f))
      (hp : pred (.app f ts) = some (ts j)) (h : Routed pred z (ts j)) : Routed pred z (.app f ts)

/-- The shared routing table on the tagged alphabet. -/
noncomputable def routeTable (pred : Term V F arity → Option (Term V F arity)) (b₀ : B) (f : F)
    (a : Fin (arity f) → Term V F arity × B) : Term V F arity × B := by
  classical
  exact (.app f (fun i => (a i).1),
    match pred (.app f (fun i => (a i).1)) with
    | none => b₀
    | some p => if h : ∃ i, (a i).1 = p then (a (Classical.choose h)).2 else b₀)

theorem route_eval_tag (pred : Term V F arity → Option (Term V F arity)) (b₀ : B) (a : V → B)
    (t : Term V F arity) : (t.eval (routeTable pred b₀) (taggedSources a)).1 = t := by
  induction t with
  | var v => rfl
  | app f ts ih =>
      change Term.app f (fun i => ((ts i).eval (routeTable pred b₀) (taggedSources a)).1) =
        Term.app f ts
      congr 1
      funext i
      exact ih i

theorem route_eval_payload (pred : Term V F arity → Option (Term V F arity)) (b₀ : B)
    (a : V → B) (z : V) (t : Term V F arity) (hr : Routed pred z t) :
    (t.eval (routeTable pred b₀) (taggedSources a)).2 = a z := by
  classical
  induction hr with
  | start => rfl
  | step f ts j hp h ih =>
      have htags : (fun i => ((ts i).eval (routeTable pred b₀) (taggedSources a)).1) = ts := by
        funext i
        exact route_eval_tag pred b₀ a (ts i)
      change (match pred (.app f (fun i => ((ts i).eval (routeTable pred b₀) (taggedSources a)).1))
        with
        | none => b₀
        | some p => if h : ∃ i, ((ts i).eval (routeTable pred b₀) (taggedSources a)).1 = p then
            ((ts (Classical.choose h)).eval (routeTable pred b₀) (taggedSources a)).2 else b₀) = a z
      rw [htags, hp]
      have hex : ∃ i, ((ts i).eval (routeTable pred b₀) (taggedSources a)).1 = ts j :=
        ⟨j, route_eval_tag pred b₀ a (ts j)⟩
      simp only [dif_pos hex]
      have hspec := Classical.choose_spec hex
      rw [route_eval_tag] at hspec
      rw [hspec]
      exact ih

theorem route_distinct_terms_pass (pred : Term V F arity → Option (Term V F arity)) (b₀ : B)
    (a : V → B) (u v : Term V F arity) (hne : u ≠ v) :
    u.eval (routeTable pred b₀) (taggedSources a) ≠ v.eval (routeTable pred b₀) (taggedSources a) := by
  intro he
  apply hne
  simpa only [route_eval_tag] using congrArg Prod.fst he

/-! ### Restriction to the finite support -/

noncomputable def finiteRouteTable (S : Finset (Term V F arity)) (d : {t // t ∈ S})
    (pred : Term V F arity → Option (Term V F arity)) (b₀ : B) (f : F)
    (a : Fin (arity f) → TagAlphabet S B) : TagAlphabet S B :=
  clampTag S d (routeTable pred b₀ f (fun i => embedTag S (a i)))

theorem finite_route_eval_embed (S : Finset (Term V F arity)) (d : {t // t ∈ S})
    (closed : SubtermClosed S) (pred : Term V F arity → Option (Term V F arity)) (b₀ : B)
    (a : V → B) (t : Term V F arity) (ht : t ∈ S) :
    embedTag S (t.eval (finiteRouteTable S d pred b₀) (finiteTaggedSources S d a)) =
      t.eval (routeTable pred b₀) (taggedSources a) := by
  induction t with
  | var v => exact embed_clamp S d (.var v, a v) ht
  | app f ts ih =>
      change embedTag S (clampTag S d (routeTable pred b₀ f
        (fun i => embedTag S ((ts i).eval (finiteRouteTable S d pred b₀)
          (finiteTaggedSources S d a))))) = _
      have he : (fun i => embedTag S ((ts i).eval (finiteRouteTable S d pred b₀)
          (finiteTaggedSources S d a))) =
        (fun i => (ts i).eval (routeTable pred b₀) (taggedSources a)) := by
        funext i
        exact ih i (closed f ts ht i)
      rw [he, embed_clamp]
      · rfl
      · simpa only [routeTable, route_eval_tag] using ht

theorem finite_route_distinct_terms_pass (S : Finset (Term V F arity)) (d : {t // t ∈ S})
    (closed : SubtermClosed S) (pred : Term V F arity → Option (Term V F arity)) (b₀ : B)
    (a : V → B) (u v : Term V F arity) (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    u.eval (finiteRouteTable S d pred b₀) (finiteTaggedSources S d a) ≠
      v.eval (finiteRouteTable S d pred b₀) (finiteTaggedSources S d a) := by
  intro he
  have he' := congrArg (embedTag S) he
  rw [finite_route_eval_embed S d closed pred b₀ a u hu,
    finite_route_eval_embed S d closed pred b₀ a v hv] at he'
  exact route_distinct_terms_pass pred b₀ a u v hne he'

theorem finite_route_eval_payload (S : Finset (Term V F arity)) (d : {t // t ∈ S})
    (closed : SubtermClosed S) (pred : Term V F arity → Option (Term V F arity)) (b₀ : B)
    (a : V → B) (z : V) (t : Term V F arity) (ht : t ∈ S) (hr : Routed pred z t) :
    (t.eval (finiteRouteTable S d pred b₀) (finiteTaggedSources S d a)).2 = a z := by
  have h := congrArg Prod.snd (finite_route_eval_embed S d closed pred b₀ a t ht)
  exact h.trans (route_eval_payload pred b₀ a z t hr)

/-! ### Routing data and the image lower bound -/

/-- `q` vertex-disjoint source-output paths, encoded by a predecessor function:
`q` distinct sources `z i` are routed to output terms `o i`.  (Disjointness is
what makes a single predecessor function possible; the endpoints are then
automatically distinct terms.) -/
structure RoutingData (outputs : List (Term V F arity)) where
  q : ℕ
  pred : Term V F arity → Option (Term V F arity)
  z : Fin q → V
  o : Fin q → Term V F arity
  z_inj : Function.Injective z
  o_mem : ∀ i, o i ∈ outputs
  routed : ∀ i, Routed pred (z i) (o i)

/-- Payload assignment: independent payloads at the routed sources, a default elsewhere. -/
noncomputable def routeAssign {q : ℕ} (z : Fin q → V) (b₀ : B) (c : Fin q → B) : V → B := by
  classical
  exact fun v => if h : ∃ i, z i = v then c (Classical.choose h) else b₀

theorem routeAssign_apply {q : ℕ} (z : Fin q → V) (hz : Function.Injective z) (b₀ : B)
    (c : Fin q → B) (i : Fin q) : routeAssign z b₀ c (z i) = c i := by
  classical
  have hex : ∃ i', z i' = z i := ⟨i, rfl⟩
  simp only [routeAssign, dif_pos hex]
  have := Classical.choose_spec hex
  rw [hz this]

open Classical in
/-- The routed image contains `|B|^q` distinct tuples. -/
theorem finite_route_image_lower [Fintype V] [Fintype B] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (R : RoutingData outputs)
    (S : Finset (Term V F arity)) (d : {t // t ∈ S}) (closed : SubtermClosed S)
    (houts : ∀ t ∈ outputs, t ∈ S) (support : ∀ uv ∈ tests, uv.1 ∈ S ∧ uv.2 ∈ S)
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (b₀ : B) :
    Fintype.card B ^ R.q ≤
      (filteredImage outputs tests (finiteRouteTable S d R.pred b₀)).card := by
  let asg := fun c : Fin R.q → B => finiteTaggedSources S d (routeAssign R.z b₀ c)
  let f := fun c : Fin R.q → B => tupleEval outputs (finiteRouteTable S d R.pred b₀) (asg c)
  have hinj : Function.Injective f := by
    intro c c' he
    funext i
    obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp (R.o_mem i)
    have h1 := congrArg (fun l : List (TagAlphabet S B) => l[idx]?) he
    simp only [f, tupleEval, List.getElem?_map, List.getElem?_eq_getElem hidx, Option.map_some,
      Option.some.injEq] at h1
    have h2 := congrArg Prod.snd h1
    rw [hget, finite_route_eval_payload S d closed R.pred b₀ _ (R.z i) (R.o i)
      (houts _ (R.o_mem i)) (R.routed i),
      finite_route_eval_payload S d closed R.pred b₀ _ (R.z i) (R.o i)
      (houts _ (R.o_mem i)) (R.routed i), routeAssign_apply R.z R.z_inj,
      routeAssign_apply R.z R.z_inj] at h2
    exact h2
  have hsub : Finset.univ.image f ⊆ filteredImage outputs tests (finiteRouteTable S d R.pred b₀) := by
    intro o ho
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp ho
    simp only [filteredImage, Finset.mem_image]
    refine ⟨asg c, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro uv huv
    exact finite_route_distinct_terms_pass S d closed R.pred b₀ _ uv.1 uv.2
      (support uv huv).1 (support uv huv).2 (distinct uv huv)
  calc Fintype.card B ^ R.q = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin]
    _ ≤ _ := Finset.card_le_card hsub

/-- Routing lower bound on the tagged alphabet. -/
theorem routing_lower_tag [Fintype V] [Fintype F] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (R : RoutingData outputs)
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (x : V) (m : ℕ) (hm : 0 < m) :
    m ^ R.q ≤ dispersionTuple (A := TagAlphabet (tupleSupport outputs tests) (Fin m)) outputs tests := by
  classical
  let S := tupleSupport outputs tests
  let d : {u // u ∈ S} := ⟨.var x, source_mem_tupleSupport outputs tests x⟩
  let b₀ : Fin m := ⟨0, hm⟩
  have h := finite_route_image_lower outputs tests R S d (tupleSupport_closed outputs tests)
    (fun t ht => output_mem_tupleSupport outputs tests t ht) (tests_mem_tupleSupport outputs tests)
    distinct b₀
  have h' : m ^ R.q ≤ (filteredImage outputs tests (finiteRouteTable S d R.pred b₀)).card := by
    simpa only [Fintype.card_fin] using h
  exact h'.trans (image_le_dispersionTuple outputs tests _)

/-- Routing lower bound on `Fin n` for `n ≥ s`: `(n / s)^q ≤ D(n)`. -/
theorem routing_lower [Fintype V] [Fintype F] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (R : RoutingData outputs)
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (x : V) (n : ℕ)
    (hn : (tupleSupport outputs tests).card ≤ n) :
    (n / (tupleSupport outputs tests).card) ^ R.q ≤ dispersionTuple (A := Fin n) outputs tests := by
  classical
  let S := tupleSupport outputs tests
  have hs : 0 < S.card := Finset.card_pos.mpr ⟨.var x, source_mem_tupleSupport outputs tests x⟩
  let m := n / S.card
  have hm : 0 < m := Nat.div_pos hn hs
  have hcard : Fintype.card (TagAlphabet S (Fin m)) ≤ Fintype.card (Fin n) := by
    rw [card_tagAlphabet, Fintype.card_fin, Fintype.card_fin]
    exact (Nat.mul_comm S.card m).trans_le (Nat.div_mul_le_self n S.card)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  letI : Nonempty (TagAlphabet S (Fin m)) :=
    ⟨⟨⟨.var x, source_mem_tupleSupport outputs tests x⟩, ⟨0, hm⟩⟩⟩
  exact (routing_lower_tag outputs tests R distinct x m hm).trans
    (dispersionTuple_embedding_le e outputs tests)

/-! ### The Menger input -/

/-- **Named classical input (finite directed vertex Menger theorem)** for the term
DAG of the instance: there are as many vertex-disjoint source-output paths as the
minimum vertex cut, i.e. routing data with `q = ρ`. -/
def MengerInput [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) : Prop :=
  ∃ R : RoutingData outputs, R.q = cutSize outputs tests

/-- The routing lower bound at the minimum cut, relative to `MengerInput`. -/
theorem routing_lower_bound_of_menger [Fintype V] [Fintype F] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (hM : MengerInput outputs tests)
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (x : V) (n : ℕ)
    (hn : (tupleSupport outputs tests).card ≤ n) :
    (n / (tupleSupport outputs tests).card) ^ cutSize outputs tests ≤
      dispersionTuple (A := Fin n) outputs tests := by
  obtain ⟨R, hq⟩ := hM
  rw [← hq]
  exact routing_lower outputs tests R distinct x n hn

/-- `u` lies on the predecessor chain starting at `t`. -/
inductive Passes (pred : Term V F arity → Option (Term V F arity)) :
    Term V F arity → Term V F arity → Prop
  | refl (t : Term V F arity) : Passes pred t t
  | step (f : F) (ts : Fin (arity f) → Term V F arity) (j : Fin (arity f)) (u : Term V F arity)
      (hp : pred (.app f ts) = some (ts j)) (h : Passes pred (ts j) u) : Passes pred (.app f ts) u

theorem routed_app_inv (pred : Term V F arity → Option (Term V F arity)) (z : V) (f : F)
    (ts : Fin (arity f) → Term V F arity) (hr : Routed pred z (.app f ts)) :
    ∃ j, pred (.app f ts) = some (ts j) ∧ Routed pred z (ts j) := by
  cases hr with
  | step _ _ j hp h => exact ⟨j, hp, h⟩

theorem routed_var_inv (pred : Term V F arity → Option (Term V F arity)) (z v : V)
    (hr : Routed pred z (.var v)) : z = v := by
  cases hr
  rfl

theorem routed_of_passes (pred : Term V F arity → Option (Term V F arity)) (z : V)
    (t u : Term V F arity) (hr : Routed pred z t) (hp : Passes pred t u) : Routed pred z u := by
  induction hp with
  | refl t => exact hr
  | step f ts j u hpj h ih =>
      apply ih
      obtain ⟨j', hp', hr'⟩ := routed_app_inv pred z f ts hr
      rw [hpj] at hp'
      have : ts j = ts j' := Option.some.inj hp'
      rw [this]
      exact hr'

/-- The predecessor chain from a term reaches a unique source. -/
theorem routed_unique (pred : Term V F arity → Option (Term V F arity)) (z z' : V)
    (t : Term V F arity) (h : Routed pred z t) (h' : Routed pred z' t) : z = z' := by
  induction h with
  | start => exact (routed_var_inv pred z' _ h').symm
  | step f ts j hp h ih =>
      obtain ⟨j', hp', hr'⟩ := routed_app_inv pred z' f ts h'
      rw [hp] at hp'
      have : ts j = ts j' := Option.some.inj hp'
      rw [← this] at hr'
      exact ih hr'

/-- Every routed chain ending at an output meets every cut. -/
theorem chain_meets_cut (pred : Term V F arity → Option (Term V F arity)) (z : V)
    (K : Finset (Term V F arity)) (t : Term V F arity) (hr : Routed pred z t) (hc : ¬ Avoids K t) :
    ∃ u ∈ K, Passes pred t u := by
  induction hr with
  | start =>
      have : Term.var z ∈ K := by
        by_contra h
        exact hc (Avoids.var z h)
      exact ⟨_, this, Passes.refl _⟩
  | step f ts j hp h ih =>
      by_cases hK : Term.app f ts ∈ K
      · exact ⟨_, hK, Passes.refl _⟩
      · have hc' : ¬ Avoids K (ts j) := fun ha => hc (Avoids.app f ts hK j ha)
        obtain ⟨u, hu, hpass⟩ := ih hc'
        exact ⟨u, hu, Passes.step f ts j u hp hpass⟩

open Classical in
/-- The easy direction of Menger: disjoint paths never exceed a cut. -/
theorem routingData_q_le_cut (outputs : List (Term V F arity)) (R : RoutingData outputs)
    (K : Finset (Term V F arity)) (hK : IsCut K outputs) : R.q ≤ K.card := by
  have hex : ∀ i : Fin R.q, ∃ u ∈ K, Passes R.pred (R.o i) u :=
    fun i => chain_meets_cut R.pred (R.z i) K (R.o i) (R.routed i) (hK _ (R.o_mem i))
  let g : Fin R.q → {u // u ∈ K} := fun i => ⟨Classical.choose (hex i), (Classical.choose_spec (hex i)).1⟩
  have hinj : Function.Injective g := by
    intro i i' h
    have h1 := (Classical.choose_spec (hex i)).2
    have h2 := (Classical.choose_spec (hex i')).2
    have heq : Classical.choose (hex i) = Classical.choose (hex i') := congrArg Subtype.val h
    rw [heq] at h1
    have r1 := routed_of_passes R.pred (R.z i) _ _ (R.routed i) h1
    have r2 := routed_of_passes R.pred (R.z i') _ _ (R.routed i') h2
    exact R.z_inj (routed_unique R.pred _ _ _ r1 r2)
  have := Fintype.card_le_of_injective g hinj
  simpa using this

end DisequalityDispersion
