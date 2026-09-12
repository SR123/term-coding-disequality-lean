import EncodedSyntax
import Padding

/-! # The general encoded class (R4/R5 input type)

A general encoded instance is an encoded C3 structure (`Instance`: sources,
symbols, topologically ordered DAG nodes, the two retained sources `x ≠ y`,
tests as node pairs, with the guard `x ≠ y` among the tests) together with a
list `outs` of further output node indices.  The decoded output tuple is
`(x, y, t₃, …, t_r)` with `t₃, …` the decoded nodes of `outs`; the decoded
tests are those of the base instance.  The retained field `t` of the base
structure is ignored, so the C3 class embeds through `ofInstance γ := ⟨γ, [γ.t]⟩`.

For every degree `k`, `Lower k g` (resp. `Strict k g`) says that some alphabet
`n ≥ 2` reaches `n^k - n^(k-1)` (resp. one more) for the actual shared-table
maximum `dispersionTuple` of the decoded instance.

The section on `Instance.extendBy` shows that appending fresh sources and nodes
to a valid instance keeps the decoded terms of the old nodes (up to the source
inclusion); this is the tool for the degree compiler. -/

namespace DisequalityDispersion
namespace Encoded

/-! ### Extending an instance by fresh sources and nodes -/

/-- Append fresh source names and further nodes; everything else unchanged. -/
def Instance.extendBy (γ : Instance) (es : List ℕ) (ns : List Node) : Instance :=
  { γ with sources := γ.sources ++ es, nodes := γ.nodes ++ ns }

namespace Instance
variable (γ : Instance) (es : List ℕ) (ns : List Node)

theorem extendBy_k : (γ.extendBy es ns).k = γ.k + es.length := by
  simp [extendBy, k]

theorem extendBy_m : (γ.extendBy es ns).m = γ.m := rfl

theorem extendBy_nodes_length : (γ.extendBy es ns).nodes.length = γ.nodes.length + ns.length := by
  simp [extendBy]

theorem k_le_extendBy : γ.k ≤ (γ.extendBy es ns).k := by
  rw [extendBy_k]; omega

theorem extendBy_nodes_getElem? (j : ℕ) (hj : j < γ.nodes.length) :
    (γ.extendBy es ns).nodes[j]? = γ.nodes[j]? := by
  simp only [extendBy]
  exact List.getElem?_append_left hj

theorem extendBy_nodes_getElem_right (p : ℕ) (hp : p < ns.length) :
    (γ.extendBy es ns).nodes[γ.nodes.length + p]'(by rw [extendBy_nodes_length]; omega) = ns[p] := by
  simp only [extendBy]
  rw [List.getElem_append_right (by omega)]
  congr 1
  omega

/-- The decoded terms of the old instance, viewed in the extended source type. -/
def castTm : γ.Tm → (γ.extendBy es ns).Tm :=
  Term.mapVar (Fin.castLE (γ.k_le_extendBy es ns))

theorem decodeFuel_extendBy (fuel j : ℕ) (u : γ.Tm) (h : γ.decodeFuel fuel j = some u) :
    (γ.extendBy es ns).decodeFuel fuel j = some (γ.castTm es ns u) := by
  induction fuel generalizing j u with
  | zero => simp [decodeFuel_zero] at h
  | succ fuel ih =>
      rw [decodeFuel_succ] at h ⊢
      cases hn : γ.nodes[j]? with
      | none => rw [hn] at h; exact absurd h (by simp)
      | some nd =>
          have hj : j < γ.nodes.length := (List.getElem?_eq_some_iff.mp hn).1
          rw [hn] at h
          rw [γ.extendBy_nodes_getElem? es ns j hj, hn]
          cases nd with
          | src i =>
              dsimp only at h ⊢
              by_cases hi : i < γ.k
              · rw [dif_pos hi] at h
                rw [dif_pos (lt_of_lt_of_le hi (γ.k_le_extendBy es ns))]
                rw [← Option.some.inj h]
                rfl
              · rw [dif_neg hi] at h; exact absurd h (by simp)
          | app f args =>
              dsimp only at h ⊢
              by_cases hf : f < γ.m
              · rw [dif_pos hf] at h
                rw [dif_pos (show f < (γ.extendBy es ns).m from hf)]
                obtain ⟨ts, hts, rfl⟩ := (γ.appNode_eq_some_iff f hf _ u).mp h
                exact ((γ.extendBy es ns).appNode_eq_some_iff f hf _ _).mpr
                  ⟨fun i => γ.castTm es ns (ts i), fun i => ih _ _ (hts i), rfl⟩
              · rw [dif_neg hf] at h; exact absurd h (by simp)

/-- Old nodes decode to the cast of their old terms. -/
theorem termD_extendBy (hv : γ.Valid) (hv' : (γ.extendBy es ns).Valid) (j : ℕ)
    (hj : j < γ.nodes.length) :
    (γ.extendBy es ns).termD hv' j = γ.castTm es ns (γ.termD hv j) := by
  have h := γ.decode_eq_termD hv j hj
  unfold decode at h
  have h' := γ.decodeFuel_extendBy es ns _ j _ h
  have h'' : (γ.extendBy es ns).decode j = some (γ.castTm es ns (γ.termD hv j)) :=
    (γ.extendBy es ns).decodeFuel_le _ _ _ (by rw [extendBy_nodes_length]; omega) _ h'
  simp [termD, h'']

/-- The tests of the extended instance are the old tests, cast. -/
theorem testTerms_extendBy (hv : γ.Valid) (hv' : (γ.extendBy es ns).Valid) :
    (γ.extendBy es ns).testTerms hv' =
      mapVarTests (Fin.castLE (γ.k_le_extendBy es ns)) (γ.testTerms hv) := by
  have hb := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  unfold testTerms mapVarTests
  show (γ.tests.map _) = (γ.tests.map _).map _
  rw [List.map_map]
  apply List.map_congr_left
  intro ij hij
  simp only [Function.comp]
  rw [γ.termD_extendBy es ns hv hv' _ (hb ij hij).1, γ.termD_extendBy es ns hv hv' _ (hb ij hij).2]
  rfl

/-- A fresh source node appended at position `γ.nodes.length + p`. -/
theorem termD_extendBy_src (hv' : (γ.extendBy es ns).Valid) (p i : ℕ) (hp : p < ns.length)
    (hnd : ns[p] = .src i) :
    ∃ hi : i < (γ.extendBy es ns).k,
      (γ.extendBy es ns).termD hv' (γ.nodes.length + p) = .var ⟨i, hi⟩ :=
  (γ.extendBy es ns).decode_src hv' (γ.nodes.length + p) i (by rw [extendBy_nodes_length]; omega)
    (by rw [γ.extendBy_nodes_getElem_right es ns p hp, hnd])

theorem extendBy_xv (hv : γ.Valid) (hv' : (γ.extendBy es ns).Valid) :
    (γ.extendBy es ns).xv hv' = Fin.castLE (γ.k_le_extendBy es ns) (γ.xv hv) := Fin.ext rfl

theorem extendBy_yv (hv : γ.Valid) (hv' : (γ.extendBy es ns).Valid) :
    (γ.extendBy es ns).yv hv' = Fin.castLE (γ.k_le_extendBy es ns) (γ.yv hv) := Fin.ext rfl

end Instance

/-! ### The general encoded instance -/

/-- A general encoded instance: a base C3 structure plus further output node indices. -/
structure GInstance where
  base : Instance
  outs : List ℕ
deriving DecidableEq, Repr

namespace GInstance
variable (g : GInstance)

/-- Executable validity: the base is valid and every extra output index is a node. -/
def isValid : Bool :=
  g.base.isValid && g.outs.all (fun j => decide (j < g.base.nodes.length))

def Valid : Prop := g.isValid = true

instance : DecidablePred GInstance.Valid := fun g => by unfold Valid; infer_instance

theorem valid_iff : g.Valid ↔ g.base.Valid ∧ ∀ j ∈ g.outs, j < g.base.nodes.length := by
  unfold Valid isValid Instance.Valid
  simp [List.all_eq_true]

theorem baseValid (hv : g.Valid) : g.base.Valid := (g.valid_iff.mp hv).1

/-- The decoded output tuple `(x, y, t₃, …)`. -/
def outputs (hv : g.Valid) : List g.base.Tm :=
  [.var (g.base.xv (g.baseValid hv)), .var (g.base.yv (g.baseValid hv))] ++
    g.outs.map (g.base.termD (g.baseValid hv))

/-- The decoded tests. -/
def tests (hv : g.Valid) : List (g.base.Tm × g.base.Tm) := g.base.testTerms (g.baseValid hv)

/-- The actual shared-table maximum image size of the decoded instance on `Fin n`. -/
noncomputable def dispersion (hv : g.Valid) (n : ℕ) : ℕ :=
  dispersionTuple (A := Fin n) (g.outputs hv) (g.tests hv)

/-- The degree-`k` lower language: some alphabet `n ≥ 2` reaches `n^k - n^(k-1)`. -/
def Lower (k : ℕ) (g : GInstance) : Prop :=
  ∃ hv : g.Valid, ∃ n : ℕ, 2 ≤ n ∧ threshold k n ≤ g.dispersion hv n

/-- The degree-`k` strict language: some alphabet `n ≥ 2` reaches `n^k - n^(k-1) + 1`. -/
def Strict (k : ℕ) (g : GInstance) : Prop :=
  ∃ hv : g.Valid, ∃ n : ℕ, 2 ≤ n ∧ threshold k n + 1 ≤ g.dispersion hv n

theorem Lower_of_Strict (k : ℕ) (h : g.Strict k) : g.Lower k := by
  obtain ⟨hv, n, hn, h⟩ := h
  exact ⟨hv, n, hn, by omega⟩

theorem var_x_mem_outputs (hv : g.Valid) : Term.var (g.base.xv (g.baseValid hv)) ∈ g.outputs hv := by
  simp [outputs]

theorem var_y_mem_outputs (hv : g.Valid) : Term.var (g.base.yv (g.baseValid hv)) ∈ g.outputs hv := by
  simp [outputs]

theorem guard_mem_tests (hv : g.Valid) :
    (Term.var (g.base.xv (g.baseValid hv)), Term.var (g.base.yv (g.baseValid hv))) ∈ g.tests hv :=
  g.base.guard_mem_testTerms (g.baseValid hv)

/-- The decoded instance lies in class `C`: the sharp cut bound applies. -/
theorem dispersion_le_threshold (hv : g.Valid) (n : ℕ) :
    g.dispersion hv n ≤ threshold (cutSize (g.outputs hv) (g.tests hv)) n :=
  dispersionTuple_le_threshold _ _ (g.base.xv_ne_yv (g.baseValid hv)) _ _
    (g.var_x_mem_outputs hv) (g.var_y_mem_outputs hv) (g.guard_mem_tests hv) n

/-- The cut size of a decoded instance is at least two. -/
theorem two_le_cutSize (hv : g.Valid) : 2 ≤ cutSize (g.outputs hv) (g.tests hv) :=
  DisequalityDispersion.two_le_cutSize _ _ _ _ (g.base.xv_ne_yv (g.baseValid hv))
    (g.var_x_mem_outputs hv) (g.var_y_mem_outputs hv)

/-! ### The C3 class as the case `outs = [t]` -/

/-- A C3 instance as a general instance with the single extra output `t`. -/
def ofInstance (γ : Instance) : GInstance := ⟨γ, [γ.t]⟩

theorem ofInstance_valid_iff (γ : Instance) : (ofInstance γ).Valid ↔ γ.Valid := by
  rw [valid_iff]
  constructor
  · exact fun h => h.1
  · intro hv
    refine ⟨hv, ?_⟩
    intro j hj
    simp only [ofInstance, List.mem_singleton] at hj
    rw [hj]
    exact (γ.valid_iff.mp hv).2.2.2.2.2.2.2.1

theorem ofInstance_dispersion (γ : Instance) (hv : (ofInstance γ).Valid) (n : ℕ) :
    (ofInstance γ).dispersion hv n = γ.dispersion ((ofInstance γ).baseValid hv) n := by
  unfold dispersion outputs tests Instance.dispersion
  simp only [ofInstance, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact dispersionTuple_triple _ _ _ _

/-- Degree two on the C3 embedding is the baseline lower language. -/
theorem Lower_two_ofInstance (γ : Instance) : (ofInstance γ).Lower 2 ↔ γ.Lower := by
  unfold Lower Instance.Lower
  constructor
  · rintro ⟨hv, n, hn, h⟩
    rw [ofInstance_dispersion, threshold_two] at h
    exact ⟨_, n, hn, h⟩
  · rintro ⟨hv, n, hn, h⟩
    refine ⟨(ofInstance_valid_iff γ).mpr hv, n, hn, ?_⟩
    rw [ofInstance_dispersion, threshold_two]
    exact h

/-- Degree two on the C3 embedding is the baseline strict language. -/
theorem Strict_two_ofInstance (γ : Instance) : (ofInstance γ).Strict 2 ↔ γ.Strict := by
  unfold Strict Instance.Strict
  constructor
  · rintro ⟨hv, n, hn, h⟩
    rw [ofInstance_dispersion, threshold_two] at h
    exact ⟨_, n, hn, h⟩
  · rintro ⟨hv, n, hn, h⟩
    refine ⟨(ofInstance_valid_iff γ).mpr hv, n, hn, ?_⟩
    rw [ofInstance_dispersion, threshold_two]
    exact h

end GInstance
end Encoded
end DisequalityDispersion
