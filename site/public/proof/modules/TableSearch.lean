import GeneralEncoded

/-! # List-based exhaustive table search (R6)

An explicit enumerator of all shared tables on the alphabet `{0, …, n-1}`
for an encoded instance, with a list-based evaluator, gives an executable
computation `dispersionExecG g n` of the shared-table maximum
`dispersionTuple` of the decoded general instance (`dispersionExecG_eq`).
Every object is a list of naturals, so the procedure is primitive recursive
(`TableSearchComputable.lean`).  This is the computability certificate for the
finite search; it is exponential and not the polynomial algorithm. -/

namespace DisequalityDispersion.Encoded

/-! ### Enumerators -/

/-- All lists of length `L` with entries below `n`. -/
def allLists (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | L + 1 => (allLists n L).flatMap (fun l => (List.range n).map (fun v => v :: l))

theorem mem_allLists (n : ℕ) : ∀ (L : ℕ) (l : List ℕ),
    l ∈ allLists n L ↔ l.length = L ∧ ∀ v ∈ l, v < n
  | 0, l => by
      simp only [allLists, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, _⟩; exact List.length_eq_zero_iff.mp h
  | L + 1, l => by
      simp only [allLists, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨l', hl', v, hv, rfl⟩
        obtain ⟨hlen, hall⟩ := (mem_allLists n L l').mp hl'
        refine ⟨by simp [hlen], ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hall w hw
      · rintro ⟨hlen, hall⟩
        cases l with
        | nil => simp at hlen
        | cons v l' =>
            refine ⟨l', (mem_allLists n L l').mpr ⟨by simpa using hlen, fun w hw =>
              hall w (List.mem_cons_of_mem _ hw)⟩, v, hall v List.mem_cons_self, rfl⟩

/-- All choices of one element from each list. -/
def cartesian {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap (fun x => (cartesian xss).map (fun l => x :: l))

theorem mem_cartesian {α : Type} : ∀ (xss : List (List α)) (l : List α),
    l ∈ cartesian xss ↔ List.Forall₂ (fun x xs => x ∈ xs) l xss
  | [], l => by
      simp only [cartesian, List.mem_singleton, List.forall₂_nil_right_iff]
  | xs :: xss, l => by
      simp only [cartesian, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨x, hx, l', hl', rfl⟩
        exact List.forall₂_cons.mpr ⟨hx, (mem_cartesian xss l').mp hl'⟩
      · intro h
        cases l with
        | nil => simp at h
        | cons x l' =>
            obtain ⟨hx, hl'⟩ := List.forall₂_cons.mp h
            exact ⟨x, hx, l', (mem_cartesian xss l').mpr hl', rfl⟩

/-- Little-endian base-`n` index of an argument list. -/
def idxL (n : ℕ) (l : List ℕ) : ℕ := l.foldr (fun a acc => a + n * acc) 0

theorem idxL_ofFn (n : ℕ) : ∀ (r : ℕ) (args : Fin r → Fin n),
    idxL n ((List.ofFn args).map Fin.val) = ∑ i, (args i).1 * n ^ (i : ℕ)
  | 0, _ => by simp [idxL]
  | r + 1, args => by
      rw [List.ofFn_succ, List.map_cons]
      simp only [idxL, List.foldr_cons] at *
      rw [Fin.sum_univ_succ]
      have := idxL_ofFn n r (fun i => args i.succ)
      simp only [idxL] at this
      rw [this, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Tables of an instance on the alphabet `n`: one list of length `n ^ arity` per symbol. -/
def allTables (n : ℕ) (γ : Instance) : List (List (List ℕ)) :=
  cartesian ((List.range γ.m).map (fun f => allLists n (n ^ γ.arityOf f)))

theorem mem_allTables (n : ℕ) (γ : Instance) (tabs : List (List ℕ)) :
    tabs ∈ allTables n γ ↔ tabs.length = γ.m ∧
      ∀ f (hf : f < tabs.length), tabs[f].length = n ^ γ.arityOf f ∧ ∀ v ∈ tabs[f], v < n := by
  unfold allTables
  rw [mem_cartesian, List.forall₂_iff_get]
  simp only [List.length_map, List.length_range, List.get_eq_getElem, List.getElem_map,
    List.getElem_range]
  constructor
  · rintro ⟨hlen, h⟩
    refine ⟨hlen, fun f hf => ?_⟩
    exact (mem_allLists n _ _).mp (h f hf (by omega))
  · rintro ⟨hlen, h⟩
    refine ⟨hlen, fun f hf _ => ?_⟩
    exact (mem_allLists n _ _).mpr (h f hf)

/-! ### Tables as interpretations -/

section interp
variable (γ : Instance) (n : ℕ) [NeZero n]

/-- The interpretation read off a list of tables (values reduced modulo `n`). -/
def tabInterp (tabs : List (List ℕ)) : Interpretation (Fin γ.m) γ.arity (Fin n) :=
  fun f args => ⟨((tabs.getD f.1 []).getD (idxL n ((List.ofFn args).map Fin.val)) 0) % n,
    Nat.mod_lt _ (NeZero.pos n)⟩

/-- Base-`n` digits of an index, as an argument tuple. -/
def digits (r e : ℕ) : Fin r → Fin n := fun i => ⟨e / n ^ (i : ℕ) % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem digits_idx (r : ℕ) (args : Fin r → Fin n) :
    digits n r (finFunctionFinEquiv args).1 = args := by
  funext i
  apply Fin.ext
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv args) i
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

/-- The table list of an interpretation. -/
def interpTabs (I : Interpretation (Fin γ.m) γ.arity (Fin n)) : List (List ℕ) :=
  List.ofFn (fun f : Fin γ.m =>
    (List.range (n ^ γ.arity f)).map (fun e => (I f (digits n _ e)).1))

theorem interpTabs_getElem (I : Interpretation (Fin γ.m) γ.arity (Fin n)) (f : Fin γ.m) :
    (interpTabs γ n I)[f.1]'(by simp [interpTabs]) =
      (List.range (n ^ γ.arity f)).map (fun e => (I f (digits n _ e)).1) := by
  simp only [interpTabs, List.getElem_ofFn]

theorem interpTabs_mem (I : Interpretation (Fin γ.m) γ.arity (Fin n)) :
    interpTabs γ n I ∈ allTables n γ := by
  rw [mem_allTables]
  refine ⟨by simp [interpTabs], ?_⟩
  intro f hf
  have hf' : f < γ.m := by simpa [interpTabs] using hf
  rw [interpTabs_getElem γ n I ⟨f, hf'⟩]
  simp only [List.length_map, List.length_range, List.mem_map, List.mem_range]
  refine ⟨rfl, ?_⟩
  rintro v ⟨e, _, rfl⟩
  exact Fin.is_lt _

/-- `tabInterp` inverts `interpTabs`. -/
theorem tabInterp_interpTabs (I : Interpretation (Fin γ.m) γ.arity (Fin n)) :
    tabInterp γ n (interpTabs γ n I) = I := by
  funext f args
  apply Fin.ext
  have hget : (interpTabs γ n I).getD f.1 [] =
      (List.range (n ^ γ.arity f)).map (fun e => (I f (digits n _ e)).1) := by
    rw [List.getD_eq_getElem _ _ (by simp [interpTabs])]
    exact interpTabs_getElem γ n I f
  have hidx : (∑ i, (args i).1 * n ^ (i : ℕ)) = (finFunctionFinEquiv args).1 := by
    rw [finFunctionFinEquiv_apply_val]
  show ((interpTabs γ n I).getD f.1 []).getD (idxL n ((List.ofFn args).map Fin.val)) 0 % n =
    (I f args).1
  rw [hget, idxL_ofFn, hidx]
  rw [List.getD_eq_getElem _ _ (by simpa using (finFunctionFinEquiv args).2)]
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.mod_eq_of_lt (Fin.is_lt _), digits_idx]

end interp

theorem getD_map_val {n : ℕ} (h : 0 < n) (l : List (Fin n)) (j : ℕ) :
    (l.map Fin.val).getD j 0 = (l.getD j ⟨0, h⟩).1 :=
  List.getD_map l ⟨0, h⟩ Fin.val

/-! ### The list-based evaluator -/

section evalL
variable (γ : Instance) (n : ℕ)

/-- One evaluation step on natural-number values. -/
def Instance.evalStepL (tabs : List (List ℕ)) (a : List ℕ) (vals : List ℕ) (j : ℕ) : ℕ :=
  match γ.nodes.getD j (.src 0) with
  | .src i => a.getD i 0
  | .app f args => (tabs.getD f []).getD (idxL n (args.map (fun p => vals.getD p 0))) 0

/-- Evaluation of all nodes on natural-number values. -/
def Instance.evalNodesL (tabs : List (List ℕ)) (a : List ℕ) : List ℕ :=
  buildList (γ.evalStepL n tabs a) γ.nodes.length

/-- The source assignment read off a list. -/
def Instance.listAssign [NeZero n] (a : List ℕ) : Fin γ.k → Fin n :=
  fun i => ⟨a.getD i.1 0 % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem Instance.listAssign_val [NeZero n] (a : List ℕ) (ha : ∀ v ∈ a, v < n) (i : Fin γ.k) :
    (γ.listAssign n a i).1 = a.getD i.1 0 := by
  simp only [Instance.listAssign]
  apply Nat.mod_eq_of_lt
  rw [List.getD_eq_getElem?_getD]
  cases h : a[i.1]? with
  | none => exact NeZero.pos n
  | some v => exact ha v (List.mem_of_getElem? h)

theorem buildList_map {α β : Type} (g : α → β) (s₁ : List β → ℕ → β) (s₂ : List α → ℕ → α)
    (N : ℕ) (h : ∀ j, j < N → ∀ l : List α, l.length = j → s₁ (l.map g) j = g (s₂ l j)) :
    buildList s₁ N = (buildList s₂ N).map g := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [buildList_succ, buildList_succ, List.map_append, List.map_singleton]
      rw [ih (fun j hj => h j (by omega))]
      congr 2
      exact h N (by omega) _ (buildList_length _ _)

/-- Agreement of the list evaluator with the typed evaluator. -/
theorem Instance.evalNodesL_eq [NeZero n] (hv : γ.Valid) (tabs : List (List ℕ))
    (htabs : ∀ t ∈ tabs, ∀ v ∈ t, v < n) (a : List ℕ) (ha : ∀ v ∈ a, v < n) :
    γ.evalNodesL n tabs a =
      (γ.evalNodes (tabInterp γ n tabs) (γ.listAssign n a) ⟨0, NeZero.pos n⟩).map Fin.val := by
  unfold Instance.evalNodesL Instance.evalNodes
  apply buildList_map
  intro j hj vals _
  have hok := (γ.valid_iff.mp hv).2.2.2.2.2.2.1 j hj
  unfold Instance.evalStepL Instance.evalStep
  rw [List.getD_eq_getElem _ _ hj]
  cases hnd : γ.nodes[j] with
  | src i =>
      rw [hnd] at hok
      have hi := (γ.nodeOk_src j i).mp hok
      dsimp only
      rw [dif_pos hi]
      exact (γ.listAssign_val n a ha ⟨i, hi⟩).symm
  | app f args =>
      rw [hnd] at hok
      obtain ⟨hf, hlen, _⟩ := (γ.nodeOk_app j f args).mp hok
      dsimp only
      rw [dif_pos hf]
      simp only [tabInterp]
      -- the argument lists agree
      have hargs : (List.ofFn fun i : Fin (γ.arity ⟨f, hf⟩) =>
          vals.getD (args.getD i.1 0) ⟨0, NeZero.pos n⟩).map Fin.val =
          args.map (fun p => (vals.map Fin.val).getD p 0) := by
        apply List.ext_getElem
        · simp only [List.length_map, List.length_ofFn]
          exact hlen.symm
        · intro i h1 h2
          simp only [List.length_map, List.length_ofFn] at h1
          simp only [List.length_map] at h2
          simp only [List.getElem_map, List.getElem_ofFn]
          rw [List.getD_eq_getElem _ _ h2]
          exact (getD_map_val (NeZero.pos n) vals args[i]).symm
      rw [hargs]
      symm
      apply Nat.mod_eq_of_lt
      rw [List.getD_eq_getElem?_getD]
      cases h : (tabs.getD f [])[idxL n (args.map fun p => (vals.map Fin.val).getD p 0)]? with
      | none => exact NeZero.pos n
      | some v =>
          have hmem := List.mem_of_getElem? h
          rw [List.getD_eq_getElem?_getD] at hmem
          cases h' : tabs[f]? with
          | none => rw [h'] at hmem; simp at hmem
          | some t =>
              rw [h'] at hmem
              exact htabs t (List.mem_of_getElem? h') v hmem

end evalL

/-! ### Passing tests, output tuples and the image count -/

section count
variable (g : GInstance) (n : ℕ)

/-- Executable test check on natural-number values. -/
def GInstance.passesL (tabs : List (List ℕ)) (a : List ℕ) : Bool :=
  let vals := g.base.evalNodesL n tabs a
  g.base.tests.all (fun ij => decide (vals.getD ij.1 0 ≠ vals.getD ij.2 0))

/-- The output tuple on natural-number values. -/
def GInstance.outTupleL (tabs : List (List ℕ)) (a : List ℕ) : List ℕ :=
  let vals := g.base.evalNodesL n tabs a
  [a.getD g.base.x 0, a.getD g.base.y 0] ++ g.outs.map (fun j => vals.getD j 0)

/-- Remove duplicates (keeping the last occurrence). -/
def dedupList {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: l => let d := dedupList l; if x ∈ d then d else x :: d

theorem dedupList_toFinset {α : Type} [DecidableEq α] (l : List α) :
    (dedupList l).toFinset = l.toFinset := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [dedupList]
      split_ifs with h
      · rw [ih, List.toFinset_cons, Finset.insert_eq_of_mem]
        rw [← ih]; exact List.mem_toFinset.mpr h
      · rw [List.toFinset_cons, List.toFinset_cons, ih]

theorem dedupList_nodup {α : Type} [DecidableEq α] (l : List α) : (dedupList l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x l ih =>
      simp only [dedupList]
      split_ifs with h
      · exact ih
      · exact List.nodup_cons.mpr ⟨h, ih⟩

theorem dedupList_length {α : Type} [DecidableEq α] (l : List α) :
    (dedupList l).length = l.toFinset.card := by
  rw [← dedupList_toFinset, List.toFinset_card_of_nodup (dedupList_nodup l)]

/-- Nodup as a length test on the executable dedup. -/
theorem nodup_iff_dedupList_length {α : Type} [DecidableEq α] (l : List α) :
    l.Nodup ↔ (dedupList l).length = l.length := by
  rw [dedupList_length, List.card_toFinset]
  constructor
  · intro h; rw [List.dedup_eq_self.mpr h]
  · intro h
    rw [← List.dedup_eq_self]
    exact (List.dedup_sublist l).eq_of_length h

/-- The number of distinct output tuples reached by passing assignments. -/
def GInstance.imageCountL (tabs : List (List ℕ)) : ℕ :=
  (dedupList (((allLists n g.base.k).filter (g.passesL n tabs)).map (g.outTupleL n tabs))).length

/-- The executable maximum over all tables. -/
def GInstance.dispersionExecG : ℕ :=
  (allTables n g.base).foldr (fun tabs acc => max (g.imageCountL n tabs) acc) 0

theorem foldr_max_le (l : List (List (List ℕ))) (c : List (List ℕ) → ℕ) (N : ℕ)
    (h : ∀ t ∈ l, c t ≤ N) : l.foldr (fun t acc => max (c t) acc) 0 ≤ N := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons t l ih =>
      simp only [List.foldr_cons]
      exact max_le (h t List.mem_cons_self) (ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')))

theorem le_foldr_max (l : List (List (List ℕ))) (c : List (List ℕ) → ℕ) (t : List (List ℕ))
    (ht : t ∈ l) : c t ≤ l.foldr (fun t acc => max (c t) acc) 0 := by
  induction l with
  | nil => simp at ht
  | cons t' l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp ht with rfl | ht
      · exact le_max_left _ _
      · exact le_trans (ih ht) (le_max_right _ _)

end count

/-! ### Correctness of the image count -/

section correct
variable (g : GInstance) (n : ℕ) [NeZero n] (hv : g.Valid)

theorem GInstance.passesL_iff (tabs : List (List ℕ)) (htabs : ∀ t ∈ tabs, ∀ v ∈ t, v < n)
    (a : List ℕ) (ha : ∀ v ∈ a, v < n) :
    g.passesL n tabs a = true ↔
      DisequalityDispersion.Valid (g.tests hv) (tabInterp g.base n tabs) (g.base.listAssign n a) := by
  unfold GInstance.tests
  rw [← g.base.passesTests_iff (g.baseValid hv) _ _ ⟨0, NeZero.pos n⟩]
  unfold GInstance.passesL Instance.passesTests
  rw [g.base.evalNodesL_eq n (g.baseValid hv) tabs htabs a ha]
  simp only [List.all_eq_true, decide_eq_true_eq]
  simp only [getD_map_val (NeZero.pos n)]
  constructor
  · intro h ij hij he
    exact h ij hij (by rw [he])
  · intro h ij hij he
    exact h ij hij (Fin.ext he)

theorem GInstance.outTupleL_eq (tabs : List (List ℕ)) (htabs : ∀ t ∈ tabs, ∀ v ∈ t, v < n)
    (a : List ℕ) (ha : ∀ v ∈ a, v < n) :
    g.outTupleL n tabs a =
      (tupleEval (g.outputs hv) (tabInterp g.base n tabs) (g.base.listAssign n a)).map Fin.val := by
  have hb := (g.valid_iff.mp hv).2
  unfold GInstance.outTupleL tupleEval GInstance.outputs
  rw [g.base.evalNodesL_eq n (g.baseValid hv) tabs htabs a ha]
  simp only [List.map_cons, List.map_map, Term.eval, List.cons.injEq, List.cons_append,
    List.nil_append]
  refine ⟨(g.base.listAssign_val n a ha (g.base.xv (g.baseValid hv))).symm,
    (g.base.listAssign_val n a ha (g.base.yv (g.baseValid hv))).symm, ?_⟩
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp]
  rw [← g.base.evalNodes_getD (g.baseValid hv) _ _ ⟨0, NeZero.pos n⟩ j (hb j hj)]
  exact getD_map_val (NeZero.pos n) _ j

/-- The list of assignments enumerates all source assignments. -/
theorem GInstance.listAssign_surj (a' : Fin g.base.k → Fin n) :
    ∃ a ∈ allLists n g.base.k, g.base.listAssign n a = a' := by
  refine ⟨(List.ofFn a').map Fin.val, ?_, ?_⟩
  · rw [mem_allLists]
    refine ⟨by simp, ?_⟩
    intro v hv'
    simp only [List.mem_map, List.mem_ofFn] at hv'
    obtain ⟨w, _, rfl⟩ := hv'
    exact w.2
  · funext i
    apply Fin.ext
    rw [g.base.listAssign_val n _ (by
      intro v hv'
      simp only [List.mem_map, List.mem_ofFn] at hv'
      obtain ⟨w, _, rfl⟩ := hv'
      exact w.2)]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

theorem GInstance.imageCountL_eq (tabs : List (List ℕ)) (htabs : ∀ t ∈ tabs, ∀ v ∈ t, v < n) :
    g.imageCountL n tabs = (filteredImage (g.outputs hv) (g.tests hv) (tabInterp g.base n tabs)).card := by
  unfold GInstance.imageCountL
  rw [dedupList_length]
  have : (((allLists n g.base.k).filter (g.passesL n tabs)).map (g.outTupleL n tabs)).toFinset =
      (filteredImage (g.outputs hv) (g.tests hv) (tabInterp g.base n tabs)).image (List.map Fin.val) := by
    ext o
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, filteredImage, validAssignments,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
      have ha' := ((mem_allLists n _ a).mp ha).2
      refine ⟨_, ⟨g.base.listAssign n a, (g.passesL_iff n hv tabs htabs a ha').mp hp, rfl⟩, ?_⟩
      exact (g.outTupleL_eq n hv tabs htabs a ha').symm
    · rintro ⟨_, ⟨a', hval, rfl⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := g.listAssign_surj n a'
      have ha' := ((mem_allLists n _ a).mp ha).2
      refine ⟨a, ⟨ha, (g.passesL_iff n hv tabs htabs a ha').mpr hval⟩, ?_⟩
      exact g.outTupleL_eq n hv tabs htabs a ha'
  rw [this, Finset.card_image_of_injective]
  intro l₁ l₂ h
  exact List.map_injective_iff.mpr Fin.val_injective h

/-- **Correctness of the exhaustive search**: the executable maximum is the
shared-table maximum of the decoded instance. -/
theorem GInstance.dispersionExecG_eq : g.dispersionExecG n = g.dispersion hv n := by
  unfold GInstance.dispersionExecG GInstance.dispersion
  apply le_antisymm
  · apply foldr_max_le
    intro tabs htabs
    have h := (mem_allTables n g.base tabs).mp htabs
    have htabs' : ∀ t ∈ tabs, ∀ v ∈ t, v < n := by
      intro t ht v hv'
      obtain ⟨f, hf, rfl⟩ := List.mem_iff_getElem.mp ht
      exact (h.2 f (by omega)).2 v hv'
    rw [g.imageCountL_eq n hv tabs htabs']
    exact image_le_dispersionTuple _ _ _
  · apply dispersionTuple_le_of_forall
    intro I
    have hmem := interpTabs_mem g.base n I
    have h := (mem_allTables n g.base _).mp hmem
    have htabs' : ∀ t ∈ interpTabs g.base n I, ∀ v ∈ t, v < n := by
      intro t ht v hv'
      obtain ⟨f, hf, rfl⟩ := List.mem_iff_getElem.mp ht
      exact (h.2 f (by omega)).2 v hv'
    have := le_foldr_max (allTables n g.base) (g.imageCountL n) _ hmem
    rw [g.imageCountL_eq n hv _ htabs', tabInterp_interpTabs] at this
    exact this

end correct

/-! ### Threshold tests at one alphabet size -/

/-- Boolean finite decision of the degree-`k` lower threshold at alphabet size `n`. -/
def lowerAtG (k : ℕ) (g : GInstance) (n : ℕ) : Bool :=
  g.isValid && decide (2 ≤ n) && decide (threshold k n ≤ g.dispersionExecG n)

theorem lowerAtG_iff (k : ℕ) (g : GInstance) (n : ℕ) :
    lowerAtG k g n = true ↔ ∃ hv : g.Valid, 2 ≤ n ∧ threshold k n ≤ g.dispersion hv n := by
  unfold lowerAtG
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hv, hn⟩, h⟩
    haveI : NeZero n := ⟨by omega⟩
    exact ⟨hv, hn, by rwa [g.dispersionExecG_eq n hv] at h⟩
  · rintro ⟨hv, hn, h⟩
    haveI : NeZero n := ⟨by omega⟩
    exact ⟨⟨hv, hn⟩, by rwa [g.dispersionExecG_eq n hv]⟩

theorem Lower_iff_exists_lowerAtG (k : ℕ) (g : GInstance) :
    g.Lower k ↔ ∃ n, lowerAtG k g n = true := by
  unfold GInstance.Lower
  constructor
  · rintro ⟨hv, n, hn, h⟩
    exact ⟨n, (lowerAtG_iff k g n).mpr ⟨hv, hn, h⟩⟩
  · rintro ⟨n, h⟩
    obtain ⟨hv, hn, h⟩ := (lowerAtG_iff k g n).mp h
    exact ⟨hv, n, hn, h⟩

/-- Boolean finite decision of the degree-`k` strict threshold at alphabet size `n`. -/
def strictAtG (k : ℕ) (g : GInstance) (n : ℕ) : Bool :=
  g.isValid && decide (2 ≤ n) && decide (threshold k n + 1 ≤ g.dispersionExecG n)

theorem strictAtG_iff (k : ℕ) (g : GInstance) (n : ℕ) :
    strictAtG k g n = true ↔ ∃ hv : g.Valid, 2 ≤ n ∧ threshold k n + 1 ≤ g.dispersion hv n := by
  unfold strictAtG
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hv, hn⟩, h⟩
    haveI : NeZero n := ⟨by omega⟩
    exact ⟨hv, hn, by rwa [g.dispersionExecG_eq n hv] at h⟩
  · rintro ⟨hv, hn, h⟩
    haveI : NeZero n := ⟨by omega⟩
    exact ⟨⟨hv, hn⟩, by rwa [g.dispersionExecG_eq n hv]⟩

theorem Strict_iff_exists_strictAtG (k : ℕ) (g : GInstance) :
    g.Strict k ↔ ∃ n, strictAtG k g n = true := by
  unfold GInstance.Strict
  constructor
  · rintro ⟨hv, n, hn, h⟩
    exact ⟨n, (strictAtG_iff k g n).mpr ⟨hv, hn, h⟩⟩
  · rintro ⟨n, h⟩
    obtain ⟨hv, hn, h⟩ := (strictAtG_iff k g n).mp h
    exact ⟨hv, n, hn, h⟩

end DisequalityDispersion.Encoded
