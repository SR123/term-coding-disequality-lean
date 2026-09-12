import EncodedComputable
import GeneralEncoded

/-! # The degree-`k` compiler (R4)

For every fixed degree `k ≥ 2` the two-source hard instance `compileWord d rels w`
is padded by `k - 2` fresh free sources, retained as further output
coordinates.  The padded instance lies in the same general encoded class, has
cut size exactly `k`, and its shared-table maximum on `Fin n` is
`n^(k-2)` times that of the two-source instance (`compileDegree_dispersion`).
Cancelling `n^(k-2)` at `n ≥ 2` gives

    Lower k (compileDegree k d rels w) ↔ HardThreshold d rels w ↔ HasFiniteQuotient rels w,

so the degree-`k` lower language is not computable under the explicit
classical hypothesis (`not_computablePred_Lower_degree`).  The compiled
instances never reach the strict threshold (`compileDegree_not_Strict`). -/

namespace DisequalityDispersion
namespace Encoded

/-! ### Validity of extensions -/

namespace Instance
variable (γ : Instance) (es : List ℕ) (ns : List Node)

theorem nodeOk_extendBy (j : ℕ) (nd : Node) (h : γ.nodeOk j nd = true) :
    (γ.extendBy es ns).nodeOk j nd = true := by
  cases nd with
  | src i =>
      rw [nodeOk_src] at h ⊢
      exact lt_of_lt_of_le h (γ.k_le_extendBy es ns)
  | app f args =>
      rw [nodeOk_app] at h ⊢
      exact h

theorem guardOk_extendBy (hv : γ.Valid) : (γ.extendBy es ns).guardOk = true := by
  have hg := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.2
  have htests := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  unfold guardOk at hg ⊢
  rw [List.any_eq_true] at hg ⊢
  obtain ⟨ij, hij, h⟩ := hg
  refine ⟨ij, hij, ?_⟩
  have hb := htests ij hij
  have e1 : (γ.extendBy es ns).nodes.getD ij.1 (.app 0 []) = γ.nodes.getD ij.1 (.app 0 []) := by
    rw [List.getD_eq_getElem _ _ hb.1, List.getD_eq_getElem _ _ (by rw [extendBy_nodes_length]; omega)]
    simp only [extendBy]
    exact List.getElem_append_left hb.1
  have e2 : (γ.extendBy es ns).nodes.getD ij.2 (.app 0 []) = γ.nodes.getD ij.2 (.app 0 []) := by
    rw [List.getD_eq_getElem _ _ hb.2, List.getD_eq_getElem _ _ (by rw [extendBy_nodes_length]; omega)]
    simp only [extendBy]
    exact List.getElem_append_left hb.2
  rw [e1, e2]
  exact h

/-- Extending a valid instance by fresh names and well-formed nodes keeps validity. -/
theorem extendBy_valid (hv : γ.Valid) (hes : es.Nodup) (hdisj : ∀ a ∈ γ.sources, ∀ b ∈ es, a ≠ b)
    (hns : ∀ p (hp : p < ns.length), (γ.extendBy es ns).nodeOk (γ.nodes.length + p) ns[p] = true) :
    (γ.extendBy es ns).Valid := by
  obtain ⟨h2, hnd, hsym, hx, hy, hxy, hnodes, ht, htests, _⟩ := γ.valid_iff.mp hv
  rw [valid_iff]
  refine ⟨?_, ?_, hsym, ?_, ?_, hxy, ?_, ?_, ?_, γ.guardOk_extendBy es ns hv⟩
  · rw [extendBy_k]; omega
  · simp only [extendBy]
    exact List.nodup_append.mpr ⟨hnd, hes, hdisj⟩
  · exact lt_of_lt_of_le hx (γ.k_le_extendBy es ns)
  · exact lt_of_lt_of_le hy (γ.k_le_extendBy es ns)
  · intro j hj
    rw [extendBy_nodes_length] at hj
    rcases Nat.lt_or_ge j γ.nodes.length with hlt | hge
    · have e : (γ.extendBy es ns).nodes[j] = γ.nodes[j] := by
        simp only [extendBy]
        exact List.getElem_append_left hlt
      rw [e]
      exact γ.nodeOk_extendBy es ns j _ (hnodes j hlt)
    · obtain ⟨p, rfl⟩ : ∃ p, j = γ.nodes.length + p := ⟨j - γ.nodes.length, by omega⟩
      rw [γ.extendBy_nodes_getElem_right es ns p (by omega)]
      exact hns p (by omega)
  · show γ.t < _
    rw [extendBy_nodes_length]; omega
  · intro ij hij
    have := htests ij hij
    rw [extendBy_nodes_length]
    constructor <;> omega

end Instance

/-! ### The degree compiler -/

section compiler
variable (k : ℕ) (d : ℕ) (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))

/-- Fresh source names `2, …, k - 1`. -/
def padSources : List ℕ := (List.range (k - 2)).map (· + 2)

/-- Source nodes for the fresh sources. -/
def padNodes : List Node := (List.range (k - 2)).map (fun i => .src (i + 2))

/-- The padded base structure. -/
def compileBase : Instance := (compileWord d rels w).extendBy (padSources k) (padNodes k)

/-- The degree-`k` hard instance: the two-source instance padded by `k - 2`
free sources, each retained as an output coordinate. -/
def compileDegree : GInstance :=
  ⟨compileBase k d rels w,
    (List.range (k - 2)).map (fun i => (compileWord d rels w).nodes.length + i)⟩

theorem padSources_length : (padSources k).length = k - 2 := by simp [padSources]
theorem padNodes_length : (padNodes k).length = k - 2 := by simp [padNodes]

theorem compileBase_k : (compileBase k d rels w).k = 2 + (k - 2) := by
  unfold compileBase
  rw [Instance.extendBy_k, compileWord_k, padSources_length]

theorem compileBase_k' (hk : 2 ≤ k) : (compileBase k d rels w).k = k := by
  rw [compileBase_k]; omega

theorem compileBase_valid : (compileBase k d rels w).Valid := by
  unfold compileBase
  apply Instance.extendBy_valid _ _ _ (compileWord_valid d rels w)
  · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
  · intro a ha b hb
    rw [compileWord_sources] at ha
    simp only [padSources, List.mem_map, List.mem_range] at hb
    obtain ⟨i, _, rfl⟩ := hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  · intro p hp
    rw [padNodes_length] at hp
    have e : (padNodes k)[p]'(by rw [padNodes_length]; exact hp) = .src (p + 2) := by
      simp [padNodes]
    rw [e, Instance.nodeOk_src, Instance.extendBy_k, compileWord_k, padSources_length]
    omega

theorem compileDegree_valid : (compileDegree k d rels w).Valid := by
  rw [GInstance.valid_iff]
  refine ⟨compileBase_valid k d rels w, ?_⟩
  intro j hj
  simp only [compileDegree, List.mem_map, List.mem_range] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  show _ < (compileBase k d rels w).nodes.length
  unfold compileBase
  rw [Instance.extendBy_nodes_length, padNodes_length]
  omega

/-! ### The decoded padded instance -/

/-- The decoded outputs are all `k` sources in order. -/
theorem compileDegree_outputs (hv : (compileDegree k d rels w).Valid) :
    (compileDegree k d rels w).outputs hv = identityOutputs (compileBase k d rels w).k := by
  have hkk := compileBase_k k d rels w
  have hbv := (compileDegree k d rels w).baseValid hv
  apply List.ext_getElem
  · simp only [GInstance.outputs, identityOutputs, compileDegree, List.length_append,
      List.length_map, List.length_finRange, List.length_range]
    show 2 + (k - 2) = (compileBase k d rels w).k
    omega
  · intro i h1 h2
    simp only [identityOutputs, List.getElem_map, List.getElem_finRange]
    simp only [GInstance.outputs, compileDegree, List.length_append, List.length_map,
      List.length_range, List.length_cons, List.length_nil] at h1
    rcases Nat.lt_or_ge i 2 with hi | hi
    · simp only [GInstance.outputs]
      rw [List.getElem_append_left (by simp; omega)]
      interval_cases i
      · show Term.var ((compileBase k d rels w).xv hbv) = _
        exact congrArg Term.var (Fin.ext rfl)
      · show Term.var ((compileBase k d rels w).yv hbv) = _
        exact congrArg Term.var (Fin.ext rfl)
    · simp only [GInstance.outputs]
      rw [List.getElem_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, List.getElem_map]
      obtain ⟨p, rfl⟩ : ∃ p, i = 2 + p := ⟨i - 2, by omega⟩
      simp only [compileDegree, List.getElem_map, List.getElem_range, Nat.add_sub_cancel_left]
      have hp : p < (padNodes k).length := by rw [padNodes_length]; omega
      have hnd : (padNodes k)[p] = .src (p + 2) := by simp [padNodes]
      obtain ⟨hi', he⟩ := (compileWord d rels w).termD_extendBy_src (padSources k) (padNodes k) hbv p
        (p + 2) hp hnd
      show (compileBase k d rels w).termD hbv ((compileWord d rels w).nodes.length + p) = _
      unfold compileBase
      rw [he]
      exact congrArg Term.var (Fin.ext (by simp; omega))

/-- The decoded tests are the padded two-source tests. -/
theorem compileDegree_tests (hv : (compileDegree k d rels w).Valid) :
    (compileDegree k d rels w).tests hv =
      padTests (compileBase k d rels w).k
        (by rw [compileBase_k]; omega)
        ((compileWord d rels w).testTerms (compileWord_valid d rels w)) := by
  unfold GInstance.tests padTests padMap
  exact (compileWord d rels w).testTerms_extendBy (padSources k) (padNodes k)
    (compileWord_valid d rels w) _

theorem compileWord_xv_zero (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).xv hv = (0 : Fin 2) := Fin.ext rfl

theorem compileWord_yv_one (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).yv hv = (1 : Fin 2) := Fin.ext rfl

/-- The two-source instance as a pair maximum. -/
theorem compileWord_pair_dispersion (hv : (compileWord d rels w).Valid) (n : ℕ) :
    dispersionTuple (A := Fin n) [Term.var (0 : Fin 2), Term.var (1 : Fin 2)]
        ((compileWord d rels w).testTerms hv) =
      (compileWord d rels w).dispersion hv n := by
  unfold Instance.dispersion
  rw [compileWord_xv_zero, compileWord_yv_one, compileWord_outTerm]
  have : (compileSig d rels w).rename (Term.var false) = Term.var (0 : Fin 2) :=
    congrArg Term.var (Fin.ext rfl)
  rw [this]
  exact dispersionTuple_pair_eq_dispersionOn (0 : Fin 2) (1 : Fin 2) _

/-- **Padding identity** on the compiled instance:
`D_padded(k, w, n) = D_pair(w, n) * n^(k-2)`. -/
theorem compileDegree_dispersion (hk : 2 ≤ k) (hv : (compileDegree k d rels w).Valid) (n : ℕ) :
    (compileDegree k d rels w).dispersion hv n =
      dispersionOn (A := Fin n) false true (.var false) (compilerTests d rels w) * n ^ (k - 2) := by
  unfold GInstance.dispersion
  rw [compileDegree_outputs, compileDegree_tests k d rels w, padding_dispersion,
    compileWord_pair_dispersion, compileWord_dispersion, compileBase_k]
  congr 2
  omega

/-- The decoded padded instance has cut size exactly `k`. -/
theorem compileDegree_cutSize (hk : 2 ≤ k) (hv : (compileDegree k d rels w).Valid) :
    cutSize ((compileDegree k d rels w).outputs hv) ((compileDegree k d rels w).tests hv) = k := by
  rw [compileDegree_outputs, compileDegree_tests k d rels w, padded_cutSize, compileBase_k]
  omega

/-- The degree-`k` lower language on the compiled instance is the hard threshold. -/
theorem Lower_compileDegree_iff (hk : 2 ≤ k) :
    (compileDegree k d rels w).Lower k ↔ HardThreshold d rels w := by
  unfold GInstance.Lower HardThreshold
  constructor
  · rintro ⟨hv, n, hn, h⟩
    rw [compileDegree_dispersion k d rels w hk, ← guard_count_eq_threshold k n hk] at h
    exact ⟨n, hn, Nat.le_of_mul_le_mul_right h (Nat.pow_pos (by omega))⟩
  · rintro ⟨n, hn, h⟩
    refine ⟨compileDegree_valid k d rels w, n, hn, ?_⟩
    rw [compileDegree_dispersion k d rels w hk, ← guard_count_eq_threshold k n hk]
    exact Nat.mul_le_mul_right _ h

theorem Lower_compileDegree_iff_quotient (hk : 2 ≤ k) :
    (compileDegree k d rels w).Lower k ↔ HasFiniteQuotient rels w :=
  (Lower_compileDegree_iff k d rels w hk).trans (hard_threshold_iff_quotient d rels w)

/-- The compiled instances never reach the strict threshold. -/
theorem compileDegree_not_Strict (hk : 2 ≤ k) : ¬ (compileDegree k d rels w).Strict k := by
  rintro ⟨hv, n, hn, h⟩
  have := (compileDegree k d rels w).dispersion_le_threshold hv n
  rw [compileDegree_cutSize k d rels w hk hv] at this
  omega

end compiler

/-! ### Computability of the degree compiler -/

section computable

/-- General instances as pairs. -/
def GInstance.equiv : GInstance ≃ Instance × List ℕ where
  toFun g := (g.base, g.outs)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro g; rfl
  right_inv := by intro p; rfl

instance : Primcodable GInstance := Primcodable.ofEquiv _ GInstance.equiv

theorem primrec_instance_nodes : Primrec Instance.nodes := by
  have : Primrec fun γ : Instance => (Instance.equiv γ).2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv))
  exact this.of_eq (fun γ => rfl)

theorem primrec_extend (es : List ℕ) (ns : List Node) :
    Primrec fun γ : Instance => γ.extendBy es ns := by
  have he : Primrec (Instance.equiv : Instance → _) := Primrec.of_equiv
  have h1 : Primrec fun γ : Instance => γ.sources ++ es :=
    Primrec.list_append.comp (Primrec.fst.comp he) (Primrec.const es)
  have h2 : Primrec fun γ : Instance => γ.symbols := Primrec.fst.comp (Primrec.snd.comp he)
  have h3 : Primrec fun γ : Instance => γ.nodes ++ ns :=
    Primrec.list_append.comp primrec_instance_nodes (Primrec.const ns)
  have h4 : Primrec fun γ : Instance => γ.x :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp he)))
  have h5 : Primrec fun γ : Instance => γ.y :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp he))))
  have h6 : Primrec fun γ : Instance => γ.t :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp he)))))
  have h7 : Primrec fun γ : Instance => γ.tests :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp he)))))
  have : Primrec fun γ : Instance => Instance.equiv.symm
      (γ.sources ++ es, γ.symbols, γ.nodes ++ ns, γ.x, γ.y, γ.t, γ.tests) :=
    Primrec.of_equiv_symm.comp (Primrec.pair h1 (Primrec.pair h2 (Primrec.pair h3
      (Primrec.pair h4 (Primrec.pair h5 (Primrec.pair h6 h7))))))
  exact this.of_eq (fun γ => rfl)

variable (k d : ℕ) (rels : List (List (Letter (Fin d))))

theorem primrec_compileDegree : Primrec (compileDegree k d rels) := by
  have hcw := primrec_compileWord d rels
  have hbase : Primrec (compileBase k d rels) := (primrec_extend _ _).comp hcw
  have hlen : Primrec fun w : List (Letter (Fin d)) => (compileWord d rels w).nodes.length :=
    Primrec.list_length.comp (primrec_instance_nodes.comp hcw)
  have houts : Primrec fun w : List (Letter (Fin d)) =>
      (List.range (k - 2)).map (fun i => (compileWord d rels w).nodes.length + i) :=
    Primrec.list_map (Primrec.const (List.range (k - 2)))
      (Primrec.nat_add.comp₂ (hlen.comp Primrec.fst) Primrec.snd)
  have : Primrec fun w : List (Letter (Fin d)) =>
      GInstance.equiv.symm (compileBase k d rels w,
        (List.range (k - 2)).map (fun i => (compileWord d rels w).nodes.length + i)) :=
    Primrec.of_equiv_symm.comp (Primrec.pair hbase houts)
  exact this.of_eq (fun w => rfl)

theorem computable_compileDegree : Computable (compileDegree k d rels) :=
  (primrec_compileDegree k d rels).to_comp

/-- **Noncomputability for each fixed degree.**  Under the explicit classical
hypothesis for one fixed finite presentation, the degree-`k` lower language is
not computable on general encoded inputs, for every `k ≥ 2`. -/
theorem not_computablePred_Lower_degree (hk : 2 ≤ k)
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    ¬ ComputablePred (GInstance.Lower k) := by
  intro hL
  apply undecidable_hard_threshold d rels slobodskoiBridsonWilton
  obtain ⟨f, hf, hpf⟩ := ComputablePred.computable_iff.mp hL
  refine ComputablePred.computable_iff.mpr
    ⟨fun w => f (compileDegree k d rels w), hf.comp (computable_compileDegree k d rels), ?_⟩
  funext w
  rw [← Lower_compileDegree_iff k d rels w hk]
  exact congrFun hpf _

end computable

end Encoded
end DisequalityDispersion
