import Core

/-! # Menger's theorem for finite digraphs (vertex version, terminal sets)

Let `E` be a finite set of directed edges on a type `α` and `A, B` finite sets
of vertices.  A *walk from `A` to `B` avoiding `X`* is a nonempty list of
vertices with consecutive pairs in `E`, first vertex in `A`, last vertex in
`B`, and no vertex in `X`.  A set `X` *separates* `A` from `B` when no such
walk exists (vertices of `A` and `B` may be used as separator vertices).

`menger` : if every separator has at least `q` vertices, then there are `q`
pairwise vertex-disjoint walks from `A` to `B`.

The proof is Göring's edge-deletion argument, by strong induction on the
number of edges.  Everything is elementary list combinatorics; no graph
library is used. -/

namespace DisequalityDispersion
namespace Menger

variable {α : Type}

/-- Adjacency of a finite edge set. -/
def Adj (E : Finset (α × α)) (a b : α) : Prop := (a, b) ∈ E

/-- A walk from `A` to `B` in `E` avoiding `X`. -/
structure Walk (E : Finset (α × α)) (A B X : Finset α) (l : List α) : Prop where
  chain : l.IsChain (Adj E)
  head : ∃ a ∈ A, l.head? = some a
  last : ∃ b ∈ B, l.getLast? = some b
  avoid : ∀ v ∈ l, v ∉ X

/-- `X` separates `A` from `B`. -/
def Separates (E : Finset (α × α)) (X A B : Finset α) : Prop := ∀ l, ¬ Walk E A B X l

/-- Pairwise vertex-disjoint families. -/
def PairwiseDisjoint {q : ℕ} (ps : Fin q → List α) : Prop :=
  ∀ i j, i ≠ j → ∀ v, v ∈ ps i → v ∉ ps j

theorem PairwiseDisjoint.of_subset {q : ℕ} {ps ps' : Fin q → List α}
    (h : PairwiseDisjoint ps) (hsub : ∀ j, ∀ v ∈ ps' j, v ∈ ps j) : PairwiseDisjoint ps' :=
  fun i j hij v hv hv' => h i j hij v (hsub i v hv) (hsub j v hv')

namespace Walk
variable {E E' : Finset (α × α)} {A B X X' : Finset α} {l : List α}

theorem ne_nil (h : Walk E A B X l) : l ≠ [] := by
  obtain ⟨a, _, ha⟩ := h.head
  intro hl
  simp [hl] at ha

theorem mono_edges (hE : E' ⊆ E) (h : Walk E' A B X l) : Walk E A B X l :=
  ⟨h.chain.imp (fun _ _ hab => hE hab), h.head, h.last, h.avoid⟩

theorem mono_avoid (hX : X' ⊆ X) (h : Walk E A B X l) : Walk E A B X' l :=
  ⟨h.chain, h.head, h.last, fun v hv hv' => h.avoid v hv (hX hv')⟩

theorem to_empty (h : Walk E A B X l) : Walk E A B ∅ l :=
  ⟨h.chain, h.head, h.last, fun _ _ => Finset.notMem_empty _⟩

/-- A walk that is not a walk avoiding `S` meets `S`. -/
theorem exists_mem_of_not (h : Walk E A B X l) (hS : ¬ Walk E A B S l) : ∃ s ∈ l, s ∈ S := by
  by_contra hc
  push_neg at hc
  exact hS ⟨h.chain, h.head, h.last, hc⟩

end Walk

/-! ### List lemmas -/

theorem isChain_erase_or_mem [DecidableEq α] (E : Finset (α × α)) (e : α × α) :
    ∀ (l : List α), l.IsChain (Adj E) → l.IsChain (Adj (E.erase e)) ∨ (e.1 ∈ l ∧ e.2 ∈ l)
  | [], _ => Or.inl List.IsChain.nil
  | [a], _ => Or.inl (List.isChain_singleton a)
  | a :: b :: l, h => by
      rw [List.isChain_cons_cons] at h
      obtain ⟨hab, hl⟩ := h
      rcases isChain_erase_or_mem E e (b :: l) hl with hl' | ⟨h1, h2⟩
      · by_cases he : (a, b) = e
        · right
          subst he
          simp
        · left
          rw [List.isChain_cons_cons]
          exact ⟨Finset.mem_erase.mpr ⟨he, hab⟩, hl'⟩
      · right
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem isChain_erase_of_first_ne [DecidableEq α] (E : Finset (α × α)) (e : α × α) (z : α) :
    ∀ (l₁ : List α), (l₁ ++ [z]).IsChain (Adj E) → (∀ a ∈ l₁, a ≠ e.1) →
      (l₁ ++ [z]).IsChain (Adj (E.erase e))
  | [], _, _ => List.isChain_singleton z
  | a :: l₁, h, hne => by
      have ih := isChain_erase_of_first_ne E e z l₁
      cases l₁ with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.isChain_cons_cons] at h ⊢
          refine ⟨Finset.mem_erase.mpr ⟨?_, h.1⟩, List.isChain_singleton z⟩
          intro he
          exact hne a (List.mem_singleton_self a) (by rw [← he])
      | cons b l₁ =>
          simp only [List.cons_append, List.isChain_cons_cons] at h ⊢
          refine ⟨Finset.mem_erase.mpr ⟨?_, h.1⟩, ih h.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx))⟩
          intro he
          exact hne a (List.mem_cons_self) (by rw [← he])

theorem isChain_erase_of_second_ne [DecidableEq α] (E : Finset (α × α)) (e : α × α) (z : α) :
    ∀ (l₂ : List α), (z :: l₂).IsChain (Adj E) → (∀ b ∈ l₂, b ≠ e.2) →
      (z :: l₂).IsChain (Adj (E.erase e))
  | [], _, _ => List.isChain_singleton z
  | b :: l₂, h, hne => by
      rw [List.isChain_cons_cons] at h ⊢
      refine ⟨Finset.mem_erase.mpr ⟨?_, h.1⟩,
        isChain_erase_of_second_ne E e b l₂ h.2 (fun x hx => hne x (List.mem_cons_of_mem _ hx))⟩
      intro he
      exact hne b List.mem_cons_self (by rw [← he])

/-- Cut a list at its first element of `Z`. -/
theorem exists_prefix_until (Z : Finset α) :
    ∀ (l : List α), (∃ z ∈ l, z ∈ Z) → ∃ l₁ z, (l₁ ++ [z]) <+: l ∧ z ∈ Z ∧ ∀ v ∈ l₁, v ∉ Z
  | [], h => by simp at h
  | a :: l, h => by
      by_cases ha : a ∈ Z
      · exact ⟨[], a, ⟨l, rfl⟩, ha, by simp⟩
      · have : ∃ z ∈ l, z ∈ Z := by
          obtain ⟨z, hz, hzZ⟩ := h
          rcases List.mem_cons.mp hz with rfl | hz
          · exact absurd hzZ ha
          · exact ⟨z, hz, hzZ⟩
        obtain ⟨l₁, z, ⟨t, ht⟩, hz, hl₁⟩ := exists_prefix_until Z l this
        refine ⟨a :: l₁, z, ⟨t, ?_⟩, hz, ?_⟩
        · rw [List.cons_append, List.cons_append, ht]
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ha
          · exact hl₁ v hv

/-- Cut a list at its last element of `Z`. -/
theorem exists_suffix_from (Z : Finset α) (l : List α) (h : ∃ z ∈ l, z ∈ Z) :
    ∃ z l₂, (z :: l₂) <:+ l ∧ z ∈ Z ∧ ∀ v ∈ l₂, v ∉ Z := by
  obtain ⟨l₁, z, hpre, hz, hl₁⟩ := exists_prefix_until Z l.reverse (by
    obtain ⟨z, hz, hzZ⟩ := h
    exact ⟨z, List.mem_reverse.mpr hz, hzZ⟩)
  refine ⟨z, l₁.reverse, ?_, hz, fun v hv => hl₁ v (List.mem_reverse.mp hv)⟩
  have := List.reverse_suffix.mpr hpre
  simpa using this

theorem head?_of_prefix {l₁ l : List α} (h : l₁ <+: l) (hne : l₁ ≠ []) : l₁.head? = l.head? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.head?_append]
  cases l₁ with
  | nil => exact absurd rfl hne
  | cons a l₁ => rfl

theorem getLast?_of_suffix {l₂ l : List α} (h : l₂ <:+ l) (hne : l₂ ≠ []) :
    l₂.getLast? = l.getLast? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getLast?_append]
  cases l₂ with
  | nil => exact absurd rfl hne
  | cons a l₂ => simp [List.getLast?_cons]

/-! ### Separator lemmas for the edge-deletion step -/

section step
variable [DecidableEq α] (E : Finset (α × α)) (e : α × α) (A B S : Finset α)

/-- A separator of `A` from `S ∪ {e.1}` in `E - e` separates `A` from `B` in `E`. -/
theorem separates_left (hS : Separates (E.erase e) S A B) (T : Finset α)
    (hT : Separates (E.erase e) T A (insert e.1 S)) : Separates E T A B := by
  intro l hl
  have hmeet : ∃ z ∈ l, z ∈ insert e.1 S := by
    rcases isChain_erase_or_mem E e l hl.chain with hc | ⟨h1, _⟩
    · obtain ⟨s, hs, hsS⟩ := Walk.exists_mem_of_not ⟨hc, hl.head, hl.last, hl.avoid⟩ (hS l)
      exact ⟨s, hs, Finset.mem_insert_of_mem hsS⟩
    · exact ⟨e.1, h1, Finset.mem_insert_self _ _⟩
  obtain ⟨l₁, z, hpre, hz, hl₁⟩ := exists_prefix_until _ l hmeet
  apply hT (l₁ ++ [z])
  refine ⟨?_, ?_, ⟨z, hz, by simp⟩, fun v hv => hl.avoid v (hpre.subset hv)⟩
  · apply isChain_erase_of_first_ne E e z l₁ (hl.chain.infix hpre.isInfix)
    intro a ha hae
    exact hl₁ a ha (hae ▸ Finset.mem_insert_self _ _)
  · rw [head?_of_prefix hpre (by simp)]
    exact hl.head

/-- A separator of `S ∪ {e.2}` from `B` in `E - e` separates `A` from `B` in `E`. -/
theorem separates_right (hS : Separates (E.erase e) S A B) (T : Finset α)
    (hT : Separates (E.erase e) T (insert e.2 S) B) : Separates E T A B := by
  intro l hl
  have hmeet : ∃ z ∈ l, z ∈ insert e.2 S := by
    rcases isChain_erase_or_mem E e l hl.chain with hc | ⟨_, h2⟩
    · obtain ⟨s, hs, hsS⟩ := Walk.exists_mem_of_not ⟨hc, hl.head, hl.last, hl.avoid⟩ (hS l)
      exact ⟨s, hs, Finset.mem_insert_of_mem hsS⟩
    · exact ⟨e.2, h2, Finset.mem_insert_self _ _⟩
  obtain ⟨z, l₂, hsuf, hz, hl₂⟩ := exists_suffix_from _ l hmeet
  apply hT (z :: l₂)
  refine ⟨?_, ⟨z, hz, rfl⟩, ?_, fun v hv => hl.avoid v (hsuf.subset hv)⟩
  · apply isChain_erase_of_second_ne E e z l₂ (hl.chain.infix hsuf.isInfix)
    intro b hb hbe
    exact hl₂ b hb (hbe ▸ Finset.mem_insert_self _ _)
  · rw [getLast?_of_suffix hsuf (by simp)]
    exact hl.last

end step

/-! ### Truncated families -/

theorem exists_truncated_prefix {E : Finset (α × α)} {A Z X : Finset α} {q : ℕ}
    (P : Fin q → List α) (hP : ∀ j, Walk E A Z X (P j)) :
    ∃ (L : Fin q → List α) (z : Fin q → α), ∀ j,
      Walk E A Z X (L j ++ [z j]) ∧ (∀ v ∈ L j ++ [z j], v ∈ P j) ∧ z j ∈ Z ∧ ∀ v ∈ L j, v ∉ Z := by
  have : ∀ j, ∃ (L : List α) (z : α),
      Walk E A Z X (L ++ [z]) ∧ (∀ v ∈ L ++ [z], v ∈ P j) ∧ z ∈ Z ∧ ∀ v ∈ L, v ∉ Z := by
    intro j
    obtain ⟨b, hb, hlast⟩ := (hP j).last
    have hbmem : b ∈ P j := by
      obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
      rw [hys]; simp
    obtain ⟨L, z, hpre, hz, hL⟩ := exists_prefix_until Z (P j) ⟨b, hbmem, hb⟩
    refine ⟨L, z, ⟨(hP j).chain.infix hpre.isInfix, ?_, ⟨z, hz, by simp⟩,
      fun v hv => (hP j).avoid v (hpre.subset hv)⟩, fun v hv => hpre.subset hv, hz, hL⟩
    rw [head?_of_prefix hpre (by simp)]
    exact (hP j).head
  choose L z h using this
  exact ⟨L, z, h⟩

theorem exists_truncated_suffix {E : Finset (α × α)} {Z B X : Finset α} {q : ℕ}
    (Q : Fin q → List α) (hQ : ∀ j, Walk E Z B X (Q j)) :
    ∃ (r : Fin q → α) (M : Fin q → List α), ∀ j,
      Walk E Z B X (r j :: M j) ∧ (∀ v ∈ r j :: M j, v ∈ Q j) ∧ r j ∈ Z ∧ ∀ v ∈ M j, v ∉ Z := by
  have : ∀ j, ∃ (r : α) (M : List α),
      Walk E Z B X (r :: M) ∧ (∀ v ∈ r :: M, v ∈ Q j) ∧ r ∈ Z ∧ ∀ v ∈ M, v ∉ Z := by
    intro j
    obtain ⟨a, ha, hhead⟩ := (hQ j).head
    have hamem : a ∈ Q j := List.mem_of_mem_head? (by rw [hhead]; rfl)
    obtain ⟨r, M, hsuf, hr, hM⟩ := exists_suffix_from Z (Q j) ⟨a, hamem, ha⟩
    refine ⟨r, M, ⟨(hQ j).chain.infix hsuf.isInfix, ⟨r, hr, rfl⟩, ?_,
      fun v hv => (hQ j).avoid v (hsuf.subset hv)⟩, fun v hv => hsuf.subset hv, hr, hM⟩
    rw [getLast?_of_suffix hsuf (by simp)]
    exact (hQ j).last
  choose r M h using this
  exact ⟨r, M, h⟩

/-! ### The gluing step -/

/-- Two truncated walks meet only inside the separator. -/
theorem meet_in_S {E : Finset (α × α)} {A B S Z₁ Z₂ : Finset α} (hS : Separates E S A B)
    (h1 : S ⊆ Z₁) (h2 : S ⊆ Z₂) (L : List α) (p : α) (hP : Walk E A Z₁ ∅ (L ++ [p]))
    (hL : ∀ v ∈ L, v ∉ Z₁) (r : α) (M : List α) (hQ : Walk E Z₂ B ∅ (r :: M))
    (hM : ∀ v ∈ M, v ∉ Z₂) (w : α) (hw1 : w ∈ L ++ [p]) (hw2 : w ∈ r :: M) : w ∈ S := by
  by_contra hwS
  obtain ⟨X₁, X₂, hX⟩ := List.append_of_mem hw1
  obtain ⟨Y₁, Y₂, hY⟩ := List.append_of_mem hw2
  have hX₁ : X₁ <+: L := by
    apply List.prefix_of_prefix_length_le (l₃ := L ++ [p])
    · rw [hX]; exact List.prefix_append _ _
    · exact List.prefix_append _ _
    · have := congrArg List.length hX
      simp at this
      omega
  have hY₂ : Y₂ <:+ M := by
    apply List.suffix_of_suffix_length_le (l₃ := r :: M)
    · rw [hY]; exact (List.suffix_cons _ _).trans (List.suffix_append _ _)
    · exact List.suffix_cons _ _
    · have := congrArg List.length hY
      simp at this
      omega
  apply hS (X₁ ++ w :: Y₂)
  have hcP : (X₁ ++ [w]).IsChain (Adj E) := by
    apply hP.chain.infix
    rw [hX]
    exact (List.prefix_append (X₁ ++ [w]) X₂).isInfix.trans (by simp)
  have hcQ : (w :: Y₂).IsChain (Adj E) := by
    apply hQ.chain.infix
    rw [hY]
    exact (List.suffix_append Y₁ (w :: Y₂)).isInfix
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show X₁ ++ w :: Y₂ = (X₁ ++ [w]) ++ Y₂ by simp]
    rw [List.isChain_append]
    refine ⟨hcP, hcQ.tail, ?_⟩
    intro x hx y hy
    rw [show w :: Y₂ = [w] ++ Y₂ by simp, List.isChain_append] at hcQ
    simp only [List.getLast?_append, List.getLast?_singleton, Option.mem_def] at hx
    have : x = w := by
      cases hx' : X₁.getLast? <;> simp [hx'] at hx <;> simp [hx]
    rw [this]
    exact hcQ.2.2 w (by simp) y hy
  · obtain ⟨a, ha, hhead⟩ := hP.head
    refine ⟨a, ha, ?_⟩
    rw [hX] at hhead
    rw [List.head?_append] at hhead ⊢
    simpa using hhead
  · obtain ⟨b, hb, hlast⟩ := hQ.last
    refine ⟨b, hb, ?_⟩
    rw [hY] at hlast
    rw [List.getLast?_append] at hlast ⊢
    rw [show w :: Y₂ = [w] ++ Y₂ by simp, List.getLast?_append] at hlast ⊢
    simpa using hlast
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact fun hvS => hL v (hX₁.subset hv) (h1 hvS)
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hwS
      · exact fun hvS => hM v (hY₂.subset hv) (h2 hvS)

/-- Combine `q` disjoint `A`–`(S ∪ {u})` walks and `q` disjoint `(S ∪ {v})`–`B` walks in
`E - (u, v)` into `q` disjoint `A`–`B` walks in `E`. -/
theorem combine [DecidableEq α] (E : Finset (α × α)) (e : α × α) (he : e ∈ E) (A B S : Finset α) (q : ℕ)
    (hS : Separates (E.erase e) S A B) (hv : e.2 ∉ S) (hcard : S.card + 1 = q)
    (P : Fin q → List α) (hP : ∀ j, Walk (E.erase e) A (insert e.1 S) ∅ (P j))
    (hPd : PairwiseDisjoint P)
    (Q : Fin q → List α) (hQ : ∀ j, Walk (E.erase e) (insert e.2 S) B ∅ (Q j))
    (hQd : PairwiseDisjoint Q) :
    ∃ W : Fin q → List α, (∀ j, Walk E A B ∅ (W j)) ∧ PairwiseDisjoint W := by
  classical
  obtain ⟨L, p, hLp⟩ := exists_truncated_prefix P hP
  obtain ⟨r, M, hrM⟩ := exists_truncated_suffix Q hQ
  have hPd' : PairwiseDisjoint (fun j => L j ++ [p j]) :=
    hPd.of_subset (fun j v hv => (hLp j).2.1 v hv)
  have hQd' : PairwiseDisjoint (fun j => r j :: M j) :=
    hQd.of_subset (fun j v hv => (hrM j).2.1 v hv)
  -- the starts of the `Q`-walks exhaust `S ∪ {e.2}`
  have hr_inj : Function.Injective r := by
    intro i j hij
    by_contra hne
    exact hQd' i j hne (r i) List.mem_cons_self (by rw [hij]; exact List.mem_cons_self)
  have hp_inj : Function.Injective p := by
    intro i j hij
    by_contra hne
    exact hPd' i j hne (p i) (by simp) (by rw [hij]; simp)
  have hr_surj : ∀ t ∈ insert e.2 S, ∃ j, r j = t := by
    let f : Fin q → (insert e.2 S : Finset α) := fun j => ⟨r j, (hrM j).2.2.1⟩
    have hf : Function.Injective f := fun i j h => hr_inj (congrArg Subtype.val h)
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hf, ?_⟩
      rw [Fintype.card_fin, Fintype.card_coe, Finset.card_insert_of_notMem hv, hcard]
    intro t ht
    obtain ⟨j, hj⟩ := hbij.surjective ⟨t, ht⟩
    exact ⟨j, congrArg Subtype.val hj⟩
  -- the matching
  let tgt : Fin q → α := fun j => if p j ∈ S then p j else e.2
  have htgt : ∀ j, tgt j ∈ insert e.2 S := by
    intro j
    simp only [tgt]
    split_ifs with h
    · exact Finset.mem_insert_of_mem h
    · exact Finset.mem_insert_self _ _
  choose σ hσ using fun j => hr_surj (tgt j) (htgt j)
  have hp_mem : ∀ j, p j ∉ S → p j = e.1 := by
    intro j hj
    rcases Finset.mem_insert.mp (hLp j).2.2.1 with h | h
    · exact h
    · exact absurd h hj
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    have := congrArg r hij
    rw [hσ i, hσ j] at this
    simp only [tgt] at this
    by_cases hi : p i ∈ S <;> by_cases hj : p j ∈ S <;> simp only [hi, hj, if_true, if_false] at this
    · exact hp_inj this
    · exact absurd (this ▸ hi) hv
    · exact absurd (this.symm ▸ hj) hv
    · exact hp_inj ((hp_mem i hi).trans (hp_mem j hj).symm)
  -- the glued walks
  let W : Fin q → List α := fun j =>
    if p j ∈ S then (L j ++ [p j]) ++ M (σ j) else (L j ++ [p j]) ++ (r (σ j) :: M (σ j))
  have hW_sub : ∀ j, ∀ w ∈ W j, w ∈ L j ++ [p j] ∨ w ∈ r (σ j) :: M (σ j) := by
    intro j w hw
    simp only [W] at hw
    split_ifs at hw with h
    · rcases List.mem_append.mp hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr (List.mem_cons_of_mem _ hw)
    · rcases List.mem_append.mp hw with hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
  have hE' : E.erase e ⊆ E := Finset.erase_subset _ _
  refine ⟨W, ?_, ?_⟩
  · intro j
    have hPj := ((hLp j).1).mono_edges hE'
    have hQj := ((hrM (σ j)).1).mono_edges hE'
    simp only [W]
    split_ifs with h
    · -- glue at the common vertex `p j = r (σ j)`
      have hr : r (σ j) = p j := by rw [hσ j]; simp [tgt, h]
      refine ⟨?_, ?_, ?_, fun _ _ => Finset.notMem_empty _⟩
      · rw [List.isChain_append]
        refine ⟨hPj.chain, hQj.chain.tail, ?_⟩
        intro x hx y hy
        have hc := hQj.chain
        rw [show r (σ j) :: M (σ j) = [r (σ j)] ++ M (σ j) by simp, List.isChain_append] at hc
        have hx' : p j = x := by simpa using hx
        rw [← hx', ← hr]
        exact hc.2.2 _ (by simp) y hy
      · obtain ⟨a, ha, hhead⟩ := hPj.head
        exact ⟨a, ha, by rw [List.head?_append, hhead]; rfl⟩
      · obtain ⟨b, hb, hlast⟩ := hQj.last
        refine ⟨b, hb, ?_⟩
        rw [show r (σ j) :: M (σ j) = [r (σ j)] ++ M (σ j) by simp, List.getLast?_append] at hlast
        rw [List.getLast?_append]
        simpa [hr] using hlast
    · -- glue along the edge `e`
      have hpj : p j = e.1 := hp_mem j h
      have hr : r (σ j) = e.2 := by rw [hσ j]; simp [tgt, h]
      refine ⟨?_, ?_, ?_, fun _ _ => Finset.notMem_empty _⟩
      · rw [List.isChain_append]
        refine ⟨hPj.chain, hQj.chain, ?_⟩
        intro x hx y hy
        have hx' : p j = x := by simpa using hx
        have hy' : r (σ j) = y := by simpa using hy
        rw [← hx', ← hy', hpj, hr]
        exact he
      · obtain ⟨a, ha, hhead⟩ := hPj.head
        exact ⟨a, ha, by rw [List.head?_append, hhead]; rfl⟩
      · obtain ⟨b, hb, hlast⟩ := hQj.last
        exact ⟨b, hb, by rw [List.getLast?_append, hlast]; rfl⟩
  · intro i j hij w hwi hwj
    have hS1 : S ⊆ insert e.1 S := Finset.subset_insert _ _
    have hS2 : S ⊆ insert e.2 S := Finset.subset_insert _ _
    -- a vertex of a truncated `P`-walk lying in `S` is its endpoint
    have hPS : ∀ j w, w ∈ L j ++ [p j] → w ∈ S → w = p j := by
      intro j w hw hwS
      rcases List.mem_append.mp hw with hw | hw
      · exact absurd (hS1 hwS) ((hLp j).2.2.2 w hw)
      · simpa using hw
    have hQS : ∀ j w, w ∈ r j :: M j → w ∈ S → w = r j := by
      intro j w hw hwS
      rcases List.mem_cons.mp hw with hw | hw
      · exact hw
      · exact absurd (hS2 hwS) ((hrM j).2.2.2 w hw)
    -- `r (σ j) ∈ S` forces `p j ∈ S` and `r (σ j) = p j`
    have hrS : ∀ j, r (σ j) ∈ S → r (σ j) = p j := by
      intro j hj
      rw [hσ j] at hj ⊢
      simp only [tgt] at hj ⊢
      split_ifs at hj ⊢ with h
      · rfl
      · exact absurd hj hv
    have key : ∀ i j, i ≠ j → w ∈ L i ++ [p i] → w ∈ r (σ j) :: M (σ j) → False := by
      intro i j hij hwi hwj
      have hwS := meet_in_S hS hS1 hS2 (L i) (p i) (hLp i).1 (hLp i).2.2.2 (r (σ j)) (M (σ j))
        (hrM (σ j)).1 (hrM (σ j)).2.2.2 w hwi hwj
      have h1 := hPS i w hwi hwS
      have h2 := hQS (σ j) w hwj hwS
      have h3 := hrS j (h2 ▸ hwS)
      exact hij (hp_inj (h1.symm.trans (h2.trans h3)))
    rcases hW_sub i w hwi with h1 | h1 <;> rcases hW_sub j w hwj with h2 | h2
    · exact hPd' i j hij w h1 h2
    · exact key i j hij h1 h2
    · exact key j i (Ne.symm hij) h2 h1
    · exact hQd' (σ i) (σ j) (fun h => hij (hσ_inj h)) w h1 h2

/-! ### Menger's theorem -/

/-- Without edges, separators are exactly the supersets of `A ∩ B`. -/
theorem separates_empty_iff [DecidableEq α] (A B X : Finset α) :
    Separates (∅ : Finset (α × α)) X A B ↔ A ∩ B ⊆ X := by
  constructor
  · intro h a ha
    rw [Finset.mem_inter] at ha
    by_contra hx
    exact h [a] ⟨List.isChain_singleton a, ⟨a, ha.1, rfl⟩, ⟨a, ha.2, rfl⟩,
      fun v hv => by rw [List.mem_singleton] at hv; rw [hv]; exact hx⟩
  · intro h l hl
    obtain ⟨a, ha, hhead⟩ := hl.head
    obtain ⟨b, hb, hlast⟩ := hl.last
    cases l with
    | nil => simp at hhead
    | cons c l =>
        cases l with
        | nil =>
            simp only [List.head?_cons, Option.some.injEq] at hhead
            simp only [List.getLast?_singleton, Option.some.injEq] at hlast
            exact hl.avoid c List.mem_cons_self
              (h (Finset.mem_inter.mpr ⟨hhead ▸ ha, hlast ▸ hb⟩))
        | cons d l =>
            have := (List.isChain_cons_cons.mp hl.chain).1
            exact Finset.notMem_empty _ this

theorem menger_aux [DecidableEq α] (n : ℕ) : ∀ (E : Finset (α × α)), E.card = n → ∀ (A B : Finset α) (q : ℕ),
    (∀ X : Finset α, Separates E X A B → q ≤ X.card) →
      ∃ ps : Fin q → List α, (∀ j, Walk E A B ∅ (ps j)) ∧ PairwiseDisjoint ps := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE A B q hsep
  rcases Finset.eq_empty_or_nonempty E with rfl | ⟨e, he⟩
  · -- no edges: `q` trivial walks in `A ∩ B`
    have hq : q ≤ (A ∩ B).card := hsep (A ∩ B) ((separates_empty_iff A B _).mpr (Finset.Subset.refl _))
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hq
    have hlen : t.toList.length = q := by rw [Finset.length_toList, htc]
    refine ⟨fun j => [t.toList[j.1]'(by rw [hlen]; exact j.2)], ?_, ?_⟩
    · intro j
      have hm : t.toList[j.1]'(by rw [hlen]; exact j.2) ∈ A ∩ B :=
        ht (Finset.mem_toList.mp (List.getElem_mem _))
      rw [Finset.mem_inter] at hm
      exact ⟨List.isChain_singleton _, ⟨_, hm.1, rfl⟩, ⟨_, hm.2, rfl⟩,
        fun _ _ => Finset.notMem_empty _⟩
    · intro i j hij v hvi hvj
      rw [List.mem_singleton] at hvi hvj
      rw [hvi] at hvj
      exact hij (Fin.ext ((Finset.nodup_toList t).getElem_inj_iff.mp hvj))
  · -- delete the edge `e`
    have hcard : (E.erase e).card < n := hE ▸ Finset.card_erase_lt_of_mem he
    by_cases hcase : ∀ X : Finset α, Separates (E.erase e) X A B → q ≤ X.card
    · obtain ⟨ps, hps, hd⟩ := ih _ hcard (E.erase e) rfl A B q hcase
      exact ⟨ps, fun j => (hps j).mono_edges (Finset.erase_subset _ _), hd⟩
    · push_neg at hcase
      obtain ⟨S, hS, hSq⟩ := hcase
      -- `S ∪ {e.1}` and `S ∪ {e.2}` separate in `E`
      have hsep1 : Separates E (insert e.1 S) A B := by
        intro l hl
        rcases isChain_erase_or_mem E e l hl.chain with hc | ⟨h1, _⟩
        · exact hS l ⟨hc, hl.head, hl.last, fun v hv hvS => hl.avoid v hv (Finset.mem_insert_of_mem hvS)⟩
        · exact hl.avoid e.1 h1 (Finset.mem_insert_self _ _)
      have hsep2 : Separates E (insert e.2 S) A B := by
        intro l hl
        rcases isChain_erase_or_mem E e l hl.chain with hc | ⟨_, h2⟩
        · exact hS l ⟨hc, hl.head, hl.last, fun v hv hvS => hl.avoid v hv (Finset.mem_insert_of_mem hvS)⟩
        · exact hl.avoid e.2 h2 (Finset.mem_insert_self _ _)
      have hu : e.1 ∉ S := by
        intro hu
        have := hsep _ hsep1
        rw [Finset.insert_eq_of_mem hu] at this
        omega
      have hv : e.2 ∉ S := by
        intro hv
        have := hsep _ hsep2
        rw [Finset.insert_eq_of_mem hv] at this
        omega
      have hScard : S.card + 1 = q := by
        have := hsep _ hsep1
        rw [Finset.card_insert_of_notMem hu] at this
        omega
      -- the two half families
      obtain ⟨P, hP, hPd⟩ := ih _ hcard (E.erase e) rfl A (insert e.1 S) q
        (fun T hT => hsep T (separates_left E e A B S hS T hT))
      obtain ⟨Q, hQ, hQd⟩ := ih _ hcard (E.erase e) rfl (insert e.2 S) B q
        (fun T hT => hsep T (separates_right E e A B S hS T hT))
      exact combine E e he A B S q hS hv hScard P hP hPd Q hQ hQd

/-- **Menger's theorem** (vertex version with terminal sets, endpoints allowed as
separator vertices): if every set separating `A` from `B` has at least `q`
vertices, there are `q` pairwise vertex-disjoint walks from `A` to `B`. -/
theorem menger [DecidableEq α] (E : Finset (α × α)) (A B : Finset α) (q : ℕ)
    (hsep : ∀ X : Finset α, Separates E X A B → q ≤ X.card) :
    ∃ ps : Fin q → List α, (∀ j, Walk E A B ∅ (ps j)) ∧ PairwiseDisjoint ps :=
  menger_aux E.card E rfl A B q hsep

end Menger
end DisequalityDispersion
