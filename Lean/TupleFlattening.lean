import Flattening
import GeneralEncoded

/-! # Acyclic flattening for arbitrary output tuples (R7)

The flattened form of a general encoded instance (computed variables with
the defining equations `Defines`, variable tests `FlatTests`) has the same
filtered output image as the decoded term instance, for every interpretation
and alphabet (`flatImageG_eq`), hence the same shared-table maximum
(`flatMaxG_eq`). -/

namespace DisequalityDispersion.Encoded
namespace GInstance

variable (g : GInstance) {A : Type}

/-- The flattened filtered image of the output tuple `(x, y, t₃, …)`. -/
noncomputable def flatImageG (hv : g.Valid) [Fintype A]
    (I : Interpretation (Fin g.base.m) g.base.arity A) (d : A) : Finset (List A) := by
  classical
  exact (Finset.univ.filter (fun ab : (Fin g.base.k → A) × (Fin g.base.nodes.length → A) =>
      g.base.Defines I ab.1 d ab.2 ∧ g.base.FlatTests d ab.2)).image
    (fun ab => [ab.1 (g.base.xv (g.baseValid hv)), ab.1 (g.base.yv (g.baseValid hv))] ++
      g.outs.map (g.base.bval d ab.2))

theorem tupleEval_outputs (hv : g.Valid) (I : Interpretation (Fin g.base.m) g.base.arity A)
    (a : Fin g.base.k → A) (d : A) :
    tupleEval (g.outputs hv) I a =
      [a (g.base.xv (g.baseValid hv)), a (g.base.yv (g.baseValid hv))] ++
        g.outs.map (g.base.bval d (g.base.extend I a d)) := by
  have hb := (g.valid_iff.mp hv).2
  unfold tupleEval GInstance.outputs
  simp only [List.map_cons, List.map_map, Term.eval, List.cons_append, List.nil_append]
  congr 2
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp]
  rw [g.base.bval_extend (g.baseValid hv) I a d j (hb j hj)]

/-- **Image preservation** for every interpretation and every output tuple. -/
theorem flatImageG_eq (hv : g.Valid) [Fintype A] (I : Interpretation (Fin g.base.m) g.base.arity A)
    (d : A) : g.flatImageG hv I d = filteredImage (g.outputs hv) (g.tests hv) I := by
  classical
  ext o
  simp only [flatImageG, filteredImage, validAssignments, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hdef, htest⟩, rfl⟩
    have hb := g.base.defines_unique (g.baseValid hv) I a d b hdef
    subst hb
    refine ⟨a, (g.base.flatTests_iff (g.baseValid hv) I a d).mp htest, ?_⟩
    rw [g.tupleEval_outputs hv I a d]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, g.base.extend I a d⟩, ⟨g.base.extend_defines (g.baseValid hv) I a d,
      (g.base.flatTests_iff (g.baseValid hv) I a d).mpr ha⟩, ?_⟩
    rw [g.tupleEval_outputs hv I a d]

/-- The flattened maximum on `Fin n`. -/
noncomputable def flatMaxG (hv : g.Valid) (n : ℕ) : ℕ :=
  if hn : 0 < n then
    (Finset.univ : Finset (Interpretation (Fin g.base.m) g.base.arity (Fin n))).sup
      (fun I => (g.flatImageG hv I ⟨0, hn⟩).card)
  else 0

attribute [local irreducible] flatImageG in
/-- The flattened maximum is the general dispersion for every alphabet size. -/
theorem flatMaxG_eq (hv : g.Valid) (n : ℕ) : g.flatMaxG hv n = g.dispersion hv n := by
  unfold flatMaxG GInstance.dispersion
  split
  · rename_i hn
    apply le_antisymm
    · apply Finset.sup_le
      intro I _
      rw [g.flatImageG_eq]
      exact image_le_dispersionTuple _ _ _
    · apply dispersionTuple_le_of_forall
      intro I
      rw [← g.flatImageG_eq hv I ⟨0, hn⟩]
      exact Finset.le_sup (f := fun J => (g.flatImageG hv J ⟨0, hn⟩).card) (Finset.mem_univ I)
  · rename_i hn
    have h0 : n = 0 := by omega
    subst h0
    symm
    apply Nat.le_zero.mp
    apply dispersionTuple_le_of_forall
    intro I
    have hk := g.base.k_pos (g.baseValid hv)
    haveI : IsEmpty (Fin g.base.k → Fin 0) := ⟨fun f => Fin.elim0 (f ⟨0, hk⟩)⟩
    simp [filteredImage, validAssignments]

end GInstance
end DisequalityDispersion.Encoded
