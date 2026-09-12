import Semantics

/-! An actual shared-table tagged construction for a selected source.
This module constructs the table, rather than assuming a routing witness.
The first construction uses the ambient term type as tag carrier; restricting
it to a finite subterm-closed set is a separate finite-alphabet obligation. -/
namespace DisequalityDispersion
variable {V F B : Type} {arity : F → ℕ}

noncomputable def taggedTable (z : V) (b₀ : B) (f : F)
    (a : Fin (arity f) → Term V F arity × B) : Term V F arity × B := by
  classical
  exact (.app f (fun i => (a i).1),
    if h : ∃ i, ((a i).1).Uses z then (a (Classical.choose h)).2 else b₀)

def taggedSources (a : V → B) : V → Term V F arity × B := fun v => (.var v, a v)

theorem eval_tag (z : V) (b₀ : B) (a : V → B) (t : Term V F arity) :
    (t.eval (taggedTable z b₀) (taggedSources a)).1 = t := by
  induction t with
  | var v => rfl
  | app f ts ih =>
      change Term.app f (fun i => ((ts i).eval (taggedTable z b₀) (taggedSources a)).1) =
        Term.app f ts
      congr 1
      funext i
      exact ih i

theorem eval_tagged_payload (z : V) (b₀ : B) (a : V → B)
    (t : Term V F arity) (hz : t.Uses z) :
    (t.eval (taggedTable z b₀) (taggedSources a)).2 = a z := by
  classical
  induction t with
  | var v =>
      change v = z at hz
      subst v
      rfl
  | app f ts ih =>
      have h : ∃ i, (((ts i).eval (taggedTable z b₀) (taggedSources a)).1).Uses z := by
        simpa only [eval_tag] using hz
      change (if h : ∃ i, (((ts i).eval (taggedTable z b₀) (taggedSources a)).1).Uses z
        then ((ts (Classical.choose h)).eval (taggedTable z b₀) (taggedSources a)).2
        else b₀) = a z
      rw [dif_pos h]
      apply ih (Classical.choose h)
      simpa only [eval_tag] using Classical.choose_spec h

theorem distinct_terms_pass (z : V) (b₀ : B) (a : V → B)
    (u v : Term V F arity) (hne : u ≠ v) :
    u.eval (taggedTable z b₀) (taggedSources a) ≠
      v.eval (taggedTable z b₀) (taggedSources a) := by
  intro he
  apply hne
  simpa only [eval_tag] using congrArg Prod.fst he

/-- Three selected source payloads are recoverable from the actual outputs. -/
theorem tagged_triple_separates (x y z : V) (b₀ : B)
    (t : Term V F arity) (hz : t.Uses z) (a b : V → B)
    (he : (taggedSources (arity := arity) a x, taggedSources (arity := arity) a y,
        t.eval (taggedTable z b₀) (taggedSources a)) =
      (taggedSources b x, taggedSources (arity := arity) b y,
        t.eval (taggedTable z b₀) (taggedSources b))) :
    (a x, a y, a z) = (b x, b y, b z) := by
  have hx := congrArg (fun q => q.1.2) he
  have hy := congrArg (fun q => q.2.1.2) he
  have htz := congrArg (fun q => q.2.2.2) he
  dsimp only at htz
  rw [eval_tagged_payload z b₀ a t hz, eval_tagged_payload z b₀ b t hz] at htz
  exact Prod.ext hx (Prod.ext hy htz)


abbrev TagAlphabet (S : Finset (Term V F arity)) (B : Type) :=
  {t // t ∈ S} × B

def embedTag (S : Finset (Term V F arity)) : TagAlphabet S B → Term V F arity × B :=
  fun q => (q.1.val, q.2)

noncomputable def clampTag (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (q : Term V F arity × B) : TagAlphabet S B := by
  classical
  exact (if h : q.1 ∈ S then ⟨q.1, h⟩ else d, q.2)

theorem embed_clamp (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (q : Term V F arity × B) (hq : q.1 ∈ S) :
    embedTag S (clampTag S d q) = q := by
  classical
  simp only [clampTag, dif_pos hq, embedTag]

noncomputable def finiteTaggedTable (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (z : V) (b₀ : B) (f : F)
    (a : Fin (arity f) → TagAlphabet S B) : TagAlphabet S B :=
  clampTag S d (taggedTable z b₀ f (fun i => embedTag S (a i)))

noncomputable def finiteTaggedSources (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (a : V → B) : V → TagAlphabet S B :=
  fun v => clampTag S d (.var v, a v)

/-- Immediate-subterm closure is checked separately from tag membership. -/
def SubtermClosed (S : Finset (Term V F arity)) : Prop :=
  ∀ f ts, Term.app f ts ∈ S → ∀ i, ts i ∈ S

theorem finite_eval_embed (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (closed : SubtermClosed S)
    (z : V) (b₀ : B) (a : V → B) (t : Term V F arity) (ht : t ∈ S) :
    embedTag S (t.eval (finiteTaggedTable S d z b₀) (finiteTaggedSources S d a)) =
      t.eval (taggedTable z b₀) (taggedSources a) := by
  induction t with
  | var v => exact embed_clamp S d (.var v, a v) ht
  | app f ts ih =>
      change embedTag S (clampTag S d (taggedTable z b₀ f
        (fun i => embedTag S ((ts i).eval (finiteTaggedTable S d z b₀)
          (finiteTaggedSources S d a))))) = _
      have he : (fun i => embedTag S ((ts i).eval (finiteTaggedTable S d z b₀)
          (finiteTaggedSources S d a))) =
        (fun i => (ts i).eval (taggedTable z b₀) (taggedSources a)) := by
        funext i
        exact ih i (closed f ts ht i)
      rw [he, embed_clamp]
      · rfl
      · simpa only [taggedTable, eval_tag] using ht

theorem finite_distinct_terms_pass (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (closed : SubtermClosed S)
    (z : V) (b₀ : B) (a : V → B) (u v : Term V F arity)
    (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    u.eval (finiteTaggedTable S d z b₀) (finiteTaggedSources S d a) ≠
      v.eval (finiteTaggedTable S d z b₀) (finiteTaggedSources S d a) := by
  intro he
  have he' := congrArg (embedTag S) he
  rw [finite_eval_embed S d closed z b₀ a u hu,
    finite_eval_embed S d closed z b₀ a v hv] at he'
  exact distinct_terms_pass z b₀ a u v hne he'

/-- The finite alphabet really has one copy of the payload alphabet per tag. -/
theorem card_tagAlphabet (S : Finset (Term V F arity)) [Fintype B] :
    Fintype.card (TagAlphabet S B) = S.card * Fintype.card B := by
  classical
  simp [TagAlphabet]


theorem finite_eval_payload (S : Finset (Term V F arity))
    (d : {t // t ∈ S}) (closed : SubtermClosed S)
    (z : V) (b₀ : B) (a : V → B) (t : Term V F arity)
    (ht : t ∈ S) (hz : t.Uses z) :
    (t.eval (finiteTaggedTable S d z b₀) (finiteTaggedSources S d a)).2 = a z := by
  have h := congrArg Prod.snd (finite_eval_embed S d closed z b₀ a t ht)
  exact h.trans (eval_tagged_payload z b₀ a t hz)

noncomputable def payloadAssignment (x y z : V) (b₀ : B) (q : B × B × B) : V → B := by
  classical
  exact fun v => if v = x then q.1 else if v = y then q.2.1 else
    if v = z then q.2.2 else b₀

/-- The constructed interpretation has at least |B|^3 distinct valid outputs.
S is any finite subterm-closed support containing the outputs and tests. -/
theorem finite_tagged_image_lower [Fintype V] [Fintype B]
    (S : Finset (Term V F arity)) (d : {t // t ∈ S}) (closed : SubtermClosed S)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (b₀ : B) (t : Term V F arity) (ht : t ∈ S) (hz : t.Uses z)
    (tests : List (Term V F arity × Term V F arity))
    (support : ∀ uv ∈ tests, uv.1 ∈ S ∧ uv.2 ∈ S)
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) :
    Fintype.card B ^ 3 ≤
      (filteredTriples x y t tests (finiteTaggedTable S d z b₀)).card := by
  classical
  let a := fun q : B × B × B => payloadAssignment x y z b₀ q
  let f := fun q : B × B × B =>
    (finiteTaggedSources S d (a q) x, finiteTaggedSources S d (a q) y,
      t.eval (finiteTaggedTable S d z b₀) (finiteTaggedSources S d (a q)))
  let recover := fun q : TagAlphabet S B × TagAlphabet S B × TagAlphabet S B =>
    (q.1.2, q.2.1.2, q.2.2.2)
  have hr (q : B × B × B) : recover (f q) = q := by
    change ((finiteTaggedSources S d (a q) x).2,
      (finiteTaggedSources S d (a q) y).2,
      (t.eval (finiteTaggedTable S d z b₀) (finiteTaggedSources S d (a q))).2) = q
    rw [finite_eval_payload S d closed z b₀ (a q) t ht hz]
    simp [finiteTaggedSources, clampTag, a, payloadAssignment,
      Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  have hinj : Function.Injective f := by
    intro q r he
    have hh := congrArg recover he
    simpa only [hr] using hh
  have hsub : Finset.univ.image f ⊆
      filteredTriples x y t tests (finiteTaggedTable S d z b₀) := by
    intro o ho
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ho
    simp only [filteredTriples, Finset.mem_image]
    refine ⟨finiteTaggedSources S d (a q), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro uv huv
    exact finite_distinct_terms_pass S d closed z b₀ (a q) uv.1 uv.2
      (support uv huv).1 (support uv huv).2 (distinct uv huv)
  calc
    Fintype.card B ^ 3 = (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ hinj]
      simp [pow_succ, mul_assoc]
    _ ≤ _ := Finset.card_le_card hsub


noncomputable def Term.support (t : Term V F arity) : Finset (Term V F arity) := by
  classical
  exact t.rec (fun v => {Term.var v})
    (fun f ts ss => insert (.app f ts) (Finset.univ.biUnion ss))

theorem Term.mem_support_self (t : Term V F arity) : t ∈ t.support := by
  classical
  cases t <;> simp [Term.support]

theorem Term.support_closed (t : Term V F arity) : SubtermClosed t.support := by
  classical
  induction t with
  | var v =>
      intro f us h
      simp [Term.support] at h
  | app g ts ih =>
      intro f us h i
      simp only [Term.support, Finset.mem_insert, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at h ⊢
      rcases h with he | ⟨j, hj⟩
      · cases he
        exact Or.inr ⟨i, Term.mem_support_self (ts i)⟩
      · exact Or.inr ⟨j, ih j f us hj i⟩

theorem SubtermClosed.union [DecidableEq (Term V F arity)] {S T : Finset (Term V F arity)}
    (hS : SubtermClosed S) (hT : SubtermClosed T) : SubtermClosed (S ∪ T) := by
  classical
  intro f ts h i
  rcases Finset.mem_union.mp h with h | h
  · exact Finset.mem_union_left _ (hS f ts h i)
  · exact Finset.mem_union_right _ (hT f ts h i)

noncomputable def instanceSupport [Fintype V] (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : Finset (Term V F arity) := by
  classical
  exact (Finset.univ.image Term.var ∪ t.support) ∪
    tests.toFinset.biUnion (fun uv => uv.1.support ∪ uv.2.support)

theorem instanceSupport_closed [Fintype V] (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) :
    SubtermClosed (instanceSupport t tests) := by
  classical
  apply SubtermClosed.union
  · apply SubtermClosed.union
    · intro f ts h
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨v, hv⟩ := h
      cases hv
    · exact t.support_closed
  · intro f ts h i
    obtain ⟨uv, huv, hmem⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨uv, huv,
      (SubtermClosed.union uv.1.support_closed uv.2.support_closed) f ts hmem i⟩

theorem source_mem_instanceSupport [Fintype V] (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (v : V) :
    Term.var v ∈ instanceSupport t tests := by
  classical
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

theorem output_mem_instanceSupport [Fintype V] (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) : t ∈ instanceSupport t tests := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ t.mem_support_self)

theorem tests_mem_instanceSupport [Fintype V] (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (uv) (huv : uv ∈ tests) :
    uv.1 ∈ instanceSupport t tests ∧ uv.2 ∈ instanceSupport t tests := by
  classical
  constructor
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨uv, List.mem_toFinset.mpr huv, Finset.mem_union_left _ uv.1.mem_support_self⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨uv, List.mem_toFinset.mpr huv, Finset.mem_union_right _ uv.2.mem_support_self⟩)

/-- Constructive cubic lower bound on the explicit finite tagged alphabet,
now with the support constructed from the actual input syntax. -/
theorem cubic_on_tagAlphabet [Fintype V] [Fintype F]
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (t : Term V F arity) (hz : t.Uses z)
    (tests : List (Term V F arity × Term V F arity))
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (m : ℕ) (hm : 0 < m) :
    m ^ 3 ≤ dispersionOn (A := TagAlphabet (instanceSupport t tests) (Fin m))
      x y t tests := by
  classical
  let S := instanceSupport t tests
  let d : {u // u ∈ S} := ⟨.var x, source_mem_instanceSupport t tests x⟩
  let b₀ : Fin m := ⟨0, hm⟩
  have h := finite_tagged_image_lower S d (instanceSupport_closed t tests)
    x y z hxy hxz hyz b₀ t (output_mem_instanceSupport t tests) hz tests
    (tests_mem_instanceSupport t tests) distinct
  have h' : m ^ 3 ≤ (filteredTriples x y t tests (finiteTaggedTable S d z b₀)).card := by
    simpa only [Fintype.card_fin] using h
  exact h'.trans (image_le_dispersion x y t tests (finiteTaggedTable S d z b₀))


theorem instanceSupport_card_two [Fintype V] (x y : V) (hxy : x ≠ y)
    (t : Term V F arity) (tests : List (Term V F arity × Term V F arity)) :
    2 ≤ (instanceSupport t tests).card := by
  classical
  apply Finset.one_lt_card.mpr
  exact ⟨.var x, source_mem_instanceSupport t tests x,
    .var y, source_mem_instanceSupport t tests y, fun h => hxy (Term.var.inj h)⟩

theorem cubic_lower_bound [Fintype V] [Fintype F]
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (t : Term V F arity) (hz : t.Uses z)
    (tests : List (Term V F arity × Term V F arity))
    (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) (n : ℕ)
    (hn : (instanceSupport t tests).card ≤ n) :
    (n / (instanceSupport t tests).card) ^ 3 ≤
      dispersionOn (A := Fin n) x y t tests := by
  classical
  let S := instanceSupport t tests
  have hs : 0 < S.card := lt_of_lt_of_le (by decide : 0 < 2)
    (instanceSupport_card_two x y hxy t tests)
  let m := n / S.card
  have hm : 0 < m := Nat.div_pos hn hs
  have hcard : Fintype.card (TagAlphabet S (Fin m)) ≤ Fintype.card (Fin n) := by
    rw [card_tagAlphabet, Fintype.card_fin, Fintype.card_fin]
    exact (Nat.mul_comm S.card m).trans_le (Nat.div_mul_le_self n S.card)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  letI : Nonempty (TagAlphabet S (Fin m)) :=
    ⟨⟨⟨.var x, source_mem_instanceSupport t tests x⟩, ⟨0, hm⟩⟩⟩
  exact (cubic_on_tagAlphabet x y z hxy hxz hyz t hz tests distinct m hm).trans
    (dispersion_embedding_le e x y t tests)

/-- Exact strict-threshold semantics, with the same existential n>=2 as in
the manuscript. No routing, cut, or growth assertion is an input hypothesis. -/
theorem strict_threshold_iff [Fintype V] [Fintype F]
    (x y : V) (hxy : x ≠ y) (t : Term V F arity)
    (tests : List (Term V F arity × Term V F arity))
    (hguard : (.var x, .var y) ∈ tests) :
    (∃ n : ℕ, 2 ≤ n ∧ n * (n - 1) + 1 ≤ dispersionOn (A := Fin n) x y t tests) ↔
      (∀ uv ∈ tests, uv.1 ≠ uv.2) ∧ ∃ z, t.Uses z ∧ z ≠ x ∧ z ≠ y := by
  classical
  constructor
  · rintro ⟨n, hn, hd⟩
    constructor
    · intro uv huv he
      have hu : (uv.1,uv.1) ∈ tests := by
        have hp : uv = (uv.1,uv.1) := Prod.ext rfl he.symm
        rw [← hp]
        exact huv
      have hz := identical_test_zero (A := Fin n) x y t uv.1 tests hu
      omega
    · by_contra h
      have huses : ∀ z, t.Uses z → z = x ∨ z = y := by
        intro z hz
        by_contra he
        push_neg at he
        exact h ⟨z, hz, he.1, he.2⟩
      have hu := retained_term_dispersion_le (A := Fin n) x y t tests hguard huses
      simp only [Fintype.card_fin] at hu
      omega
  · rintro ⟨distinct, z, hz, hzx, hzy⟩
    let s := (instanceSupport t tests).card
    have hs : 2 ≤ s := instanceSupport_card_two x y hxy t tests
    have hsn : s ≤ s ^ 3 := le_self_pow (by omega) (by decide)
    refine ⟨s ^ 3, le_trans hs hsn, ?_⟩
    exact (cubic_witness_arithmetic s hs).trans
      (cubic_lower_bound x y z hxy (Ne.symm hzx) (Ne.symm hzy) t hz tests distinct
        (s ^ 3) hsn)

end DisequalityDispersion
