import StrictAlgorithm
import Transport

/-! # Acyclic flattening and unique extension (T8)

Every node `j` of an encoded instance becomes a computed variable `b j` with
the defining equation "`b j` is the value of node `j`'s symbol table on the
source values and the earlier computed values" (`Defines`).  Tests become
disequalities between named variables (`FlatTests`).

* `defines_iff`: for every shared interpretation and source assignment there
  is exactly one computed extension satisfying all defining equations, namely
  `extend I a d` (the executable node evaluation);
* `flatTests_iff`: the extension satisfies the variable tests iff the source
  assignment satisfies the original term tests;
* `flatImage_eq`, `flatMax_eq`: the flattened filtered image equals the
  original filtered image for every interpretation and alphabet, hence the
  maxima agree.

The defining equations only evaluate terms with the shared table of each
symbol; no extra equality filter, Boolean sort or prescribed table is used.
Two nodes decoding to the same term (duplicate DAG nodes) get two computed
variables with the same defining shape, which is harmless because both
equations are enforced; `canonIds` identifies such duplicates. -/

namespace DisequalityDispersion.Encoded
namespace Instance

variable (γ : Instance) {A : Type}

/-- `evalStep` at `j` only reads earlier node values. -/
theorem evalStep_congr (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) (j : ℕ) (hj : j < γ.nodes.length) (vals vals' : List A)
    (h : ∀ i, i < j → vals.getD i d = vals'.getD i d) :
    γ.evalStep I a d vals j = γ.evalStep I a d vals' j := by
  unfold evalStep
  rw [List.getD_eq_getElem _ _ hj]
  cases hnd : γ.nodes[j] with
  | src i => rfl
  | app f args =>
      obtain ⟨hf, hlen, hargs, _⟩ := γ.decode_app hv j f args hj hnd
      dsimp only
      simp only [dif_pos hf]
      congr 1
      funext i
      have hi : i.1 < args.length := by
        have : i.1 < γ.arityOf f := i.2
        omega
      rw [List.getD_eq_getElem _ _ hi]
      exact h _ (hargs _ (List.getElem_mem hi))

/-- Value of a named computed variable (default outside range). -/
def bval (d : A) (b : Fin γ.nodes.length → A) (i : ℕ) : A :=
  if h : i < γ.nodes.length then b ⟨i, h⟩ else d

/-- The defining equations of the flattened form. -/
def Defines (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A)
    (b : Fin γ.nodes.length → A) : Prop :=
  ∀ j : Fin γ.nodes.length, b j = γ.evalStep I a d (List.ofFn b) j.1

/-- Flattened tests: disequalities between named computed variables. -/
def FlatTests (d : A) (b : Fin γ.nodes.length → A) : Prop :=
  ∀ ij ∈ γ.tests, γ.bval d b ij.1 ≠ γ.bval d b ij.2

/-- The computed extension of a source assignment. -/
def extend (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A) :
    Fin γ.nodes.length → A :=
  fun j => (γ.evalNodes I a d).getD j.1 d

theorem ofFn_extend_getD (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A)
    (i : ℕ) : (List.ofFn (γ.extend I a d)).getD i d = (γ.evalNodes I a d).getD i d := by
  rcases Nat.lt_or_ge i γ.nodes.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    rfl
  · rw [List.getD_eq_default _ _ (by simpa using h),
      List.getD_eq_default _ _ (by rw [evalNodes_length]; exact h)]

theorem extend_defines (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) : γ.Defines I a d (γ.extend I a d) := by
  intro j
  show (γ.evalNodes I a d).getD j.1 d = _
  unfold evalNodes
  rw [buildList_getD _ _ _ j.2]
  apply γ.evalStep_congr hv I a d j.1 j.2
  intro i hi
  rw [ofFn_extend_getD]
  unfold evalNodes
  rw [buildList_getD _ _ _ (lt_trans hi j.2), buildList_getD _ _ _ hi]

theorem defines_unique (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) (b : Fin γ.nodes.length → A) (hb : γ.Defines I a d b) :
    b = γ.extend I a d := by
  have key : ∀ j (hj : j < γ.nodes.length), b ⟨j, hj⟩ = γ.extend I a d ⟨j, hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
        intro hj
        rw [hb ⟨j, hj⟩, γ.extend_defines hv I a d ⟨j, hj⟩]
        apply γ.evalStep_congr hv I a d j hj
        intro i hi
        have hil : i < γ.nodes.length := lt_trans hi hj
        rw [List.getD_eq_getElem _ _ (by simpa using hil),
          List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_ofFn, List.getElem_ofFn]
        exact ih i hi hil
  funext j
  exact key j.1 j.2

/-- **Unique extension**: the defining equations have exactly one solution. -/
theorem defines_iff (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) (b : Fin γ.nodes.length → A) :
    γ.Defines I a d b ↔ b = γ.extend I a d :=
  ⟨γ.defines_unique hv I a d b, fun h => h ▸ γ.extend_defines hv I a d⟩

theorem bval_extend (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) (i : ℕ) (hi : i < γ.nodes.length) :
    γ.bval d (γ.extend I a d) i = (γ.termD hv i).eval I a := by
  unfold bval
  rw [dif_pos hi]
  exact γ.evalNodes_getD hv I a d i hi

/-- The variable tests on the extension are the original term tests. -/
theorem flatTests_iff (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) :
    γ.FlatTests d (γ.extend I a d) ↔ DisequalityDispersion.Valid (γ.testTerms hv) I a := by
  have htests := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  unfold FlatTests DisequalityDispersion.Valid testTerms
  simp only [List.forall_mem_map]
  constructor
  · intro h ij hij
    have := h ij hij
    rwa [γ.bval_extend hv I a d _ (htests ij hij).1, γ.bval_extend hv I a d _ (htests ij hij).2]
      at this
  · intro h ij hij
    rw [γ.bval_extend hv I a d _ (htests ij hij).1, γ.bval_extend hv I a d _ (htests ij hij).2]
    exact h ij hij

/-- The flattened filtered image: outputs of all pairs (source assignment,
computed assignment) satisfying the defining equations and the variable tests. -/
noncomputable def flatImage (hv : γ.Valid) [Fintype A] (I : Interpretation (Fin γ.m) γ.arity A)
    (d : A) : Finset (A × A × A) := by
  classical
  exact (Finset.univ.filter (fun ab : (Fin γ.k → A) × (Fin γ.nodes.length → A) =>
      γ.Defines I ab.1 d ab.2 ∧ γ.FlatTests d ab.2)).image
    (fun ab => (ab.1 (γ.xv hv), ab.1 (γ.yv hv), γ.bval d ab.2 γ.t))

/-- **Image preservation** for every interpretation. -/
theorem flatImage_eq (hv : γ.Valid) [Fintype A] (I : Interpretation (Fin γ.m) γ.arity A)
    (d : A) :
    γ.flatImage hv I d = filteredTriples (γ.xv hv) (γ.yv hv) (γ.outTerm hv) (γ.testTerms hv) I := by
  classical
  have ht := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.1
  ext o
  simp only [flatImage, filteredTriples, validAssignments, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hdef, htest⟩, rfl⟩
    have hb := γ.defines_unique hv I a d b hdef
    subst hb
    refine ⟨a, (γ.flatTests_iff hv I a d).mp htest, ?_⟩
    simp only
    rw [γ.bval_extend hv I a d γ.t ht]
    rfl
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, γ.extend I a d⟩, ⟨γ.extend_defines hv I a d, (γ.flatTests_iff hv I a d).mpr ha⟩, ?_⟩
    simp only
    rw [γ.bval_extend hv I a d γ.t ht]
    rfl

/-- The flattened maximum on `Fin n`. -/
noncomputable def flatMax (hv : γ.Valid) (n : ℕ) : ℕ :=
  if hn : 0 < n then
    (Finset.univ : Finset (Interpretation (Fin γ.m) γ.arity (Fin n))).sup
      (fun I => (γ.flatImage hv I ⟨0, hn⟩).card)
  else 0

attribute [local irreducible] flatImage in
/-- The flattened maximum is the original dispersion for every alphabet size. -/
theorem flatMax_eq (hv : γ.Valid) (n : ℕ) : γ.flatMax hv n = γ.dispersion hv n := by
  unfold flatMax Instance.dispersion
  split
  · rename_i hn
    apply le_antisymm
    · apply Finset.sup_le
      intro I _
      rw [γ.flatImage_eq]
      exact image_le_dispersion _ _ _ _ I
    · apply SigEquiv.dispersionOn_le_of_forall
      intro I
      rw [← γ.flatImage_eq hv I ⟨0, hn⟩]
      exact Finset.le_sup (f := fun J => (γ.flatImage hv J ⟨0, hn⟩).card) (Finset.mem_univ I)
  · rename_i hn
    have h0 : n = 0 := by omega
    subst h0
    symm
    apply Nat.le_zero.mp
    apply SigEquiv.dispersionOn_le_of_forall
    intro I
    exact (Finset.card_le_univ _).trans (by simp)

end Instance
end DisequalityDispersion.Encoded
