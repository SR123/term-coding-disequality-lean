import TableSearchComputable
import Semidecision

/-! # Semidecidability at every degree, with no search assumption (R6)

`Lower k` is recursively enumerable for every degree `k` (the finite search
`lowerAtG k` is primitive recursive and `Lower k g ↔ ∃ n, lowerAtG k g n`);
under the explicit classical hypothesis its complement is not r.e. for `k ≥ 2`,
and no total computable alphabet bound exists.  The old
`Semidecision.SearchComputable` hypothesis is discharged. -/

namespace DisequalityDispersion.Encoded

/-- `Lower k` is recursively enumerable, for every degree `k`. -/
theorem rePred_Lower_degree (k : ℕ) : REPred (GInstance.Lower k) := by
  have hp : Partrec₂ (fun (g : GInstance) (n : ℕ) => (Part.some (lowerAtG k g n) : Part Bool)) :=
    (computable_lowerAtG k).partrec₂
  have := (Partrec.rfind hp).dom_re
  refine this.of_eq (fun g => ?_)
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, -⟩
    exact (Lower_iff_exists_lowerAtG k g).mpr ⟨n, (Part.mem_some_iff.mp hn).symm⟩
  · intro h
    obtain ⟨n, hn⟩ := (Lower_iff_exists_lowerAtG k g).mp h
    exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun _ => trivial⟩

/-- `Strict k` is recursively enumerable, for every degree `k`. -/
theorem rePred_Strict_degree (k : ℕ) : REPred (GInstance.Strict k) := by
  have hp : Partrec₂ (fun (g : GInstance) (n : ℕ) => (Part.some (strictAtG k g n) : Part Bool)) :=
    (computable_strictAtG k).partrec₂
  have := (Partrec.rfind hp).dom_re
  refine this.of_eq (fun g => ?_)
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, -⟩
    exact (Strict_iff_exists_strictAtG k g).mpr ⟨n, (Part.mem_some_iff.mp hn).symm⟩
  · intro h
    obtain ⟨n, hn⟩ := (Strict_iff_exists_strictAtG k g).mp h
    exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun _ => trivial⟩

/-- Under the classical input, the complement of `Lower k` is not r.e. (`k ≥ 2`). -/
theorem not_rePred_not_Lower_degree (k : ℕ) (hk : 2 ≤ k) (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    ¬ REPred (fun g : GInstance => ¬ g.Lower k) := by
  intro h
  apply not_computablePred_Lower_degree k d rels hk slobodskoiBridsonWilton
  exact ComputablePred.computable_iff_re_compl_re'.mpr ⟨rePred_Lower_degree k, h⟩

/-- Bounded search: some `n < b` passes the finite threshold test. -/
def boundedAnyG (k : ℕ) (g : GInstance) (b : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun y IH => IH || lowerAtG k g y) b

theorem boundedAnyG_iff (k : ℕ) (g : GInstance) (b : ℕ) :
    boundedAnyG k g b = true ↔ ∃ n, n < b ∧ lowerAtG k g n = true := by
  induction b with
  | zero => simp [boundedAnyG]
  | succ b ih =>
      simp only [boundedAnyG, Bool.or_eq_true] at ih ⊢
      rw [ih]
      constructor
      · rintro (⟨n, hn, h⟩ | h)
        · exact ⟨n, by omega, h⟩
        · exact ⟨b, by omega, h⟩
      · rintro ⟨n, hn, h⟩
        rcases Nat.lt_or_ge n b with h' | h'
        · exact Or.inl ⟨n, h', h⟩
        · have : n = b := by omega
          subst this
          exact Or.inr h

theorem computable_boundedAnyG (k : ℕ) {f : GInstance → ℕ} (hf : Computable f) :
    Computable (fun g => boundedAnyG k g (f g)) := by
  have hh : Computable₂ (fun (g : GInstance) (p : ℕ × Bool) => p.2 || lowerAtG k g p.1) := by
    have := Computable.cond (c := fun q : GInstance × (ℕ × Bool) => q.2.2)
      (f := fun _ => true) (g := fun q : GInstance × (ℕ × Bool) => lowerAtG k q.1 q.2.1)
      (Computable.snd.comp Computable.snd) (Computable.const true)
      ((computable_lowerAtG k).comp Computable.fst (Computable.fst.comp Computable.snd))
    refine this.of_eq (fun q => ?_)
    rcases q with ⟨g, n, b⟩
    cases b <;> rfl
  exact Computable.nat_rec hf (Computable.const false) hh

/-- **No computable witness bound at any fixed degree `k ≥ 2`.**  For any computable
size function `sz`, no total computable `B` satisfies: every degree-`k` yes-instance
has a witnessing alphabet `2 ≤ n ≤ B (sz g)` passing the finite threshold test. -/
theorem no_computable_witness_bound_degree (k : ℕ) (hk : 2 ≤ k) (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels))
    (sz : GInstance → ℕ) (hsz : Computable sz) (B : ℕ → ℕ) (hB : Computable B)
    (hbound : ∀ g : GInstance, g.Lower k →
      ∃ n, 2 ≤ n ∧ n ≤ B (sz g) ∧ lowerAtG k g n = true) : False := by
  apply not_computablePred_Lower_degree k d rels hk slobodskoiBridsonWilton
  refine ComputablePred.computable_iff.mpr
    ⟨fun g => boundedAnyG k g (B (sz g) + 1),
      computable_boundedAnyG k (Computable.succ.comp (hB.comp hsz)), ?_⟩
  funext g
  apply propext
  rw [boundedAnyG_iff]
  constructor
  · intro h
    obtain ⟨n, _, hn, hpass⟩ := hbound g h
    exact ⟨n, by omega, hpass⟩
  · rintro ⟨n, _, hpass⟩
    exact (Lower_iff_exists_lowerAtG k g).mpr ⟨n, hpass⟩

/-! ### The old C3 search hypothesis is discharged -/

/-- The three-output finite search (`Instance.lowerThresholdAt`) agrees with the
degree-two general search on the embedded instance. -/
theorem lowerThresholdAt_eq_lowerAtG (γ : Instance) (n : ℕ) :
    γ.lowerThresholdAt n = lowerAtG 2 (GInstance.ofInstance γ) n := by
  apply Bool.eq_iff_iff.mpr
  rw [γ.lowerThresholdAt_iff, lowerAtG_iff]
  constructor
  · rintro ⟨hv, hn, h⟩
    refine ⟨(GInstance.ofInstance_valid_iff γ).mpr hv, hn, ?_⟩
    rw [GInstance.ofInstance_dispersion, threshold_two]
    exact h
  · rintro ⟨hv, hn, h⟩
    rw [GInstance.ofInstance_dispersion, threshold_two] at h
    exact ⟨_, hn, h⟩

theorem primrec_ofInstance : Primrec GInstance.ofInstance := by
  have : Primrec fun γ : Instance => GInstance.equiv.symm (γ, [γ.t]) :=
    Primrec.of_equiv_symm.comp (Primrec.pair Primrec.id
      (Primrec.list_cons.comp primrec_instance_t (Primrec.const [])))
  exact this.of_eq (fun γ => rfl)

/-- `Semidecision.SearchComputable` holds: the old finite search is computable. -/
theorem searchComputable : SearchComputable := by
  unfold SearchComputable
  have := (computable_lowerAtG 2).comp (primrec_ofInstance.to_comp.comp Computable.fst) Computable.snd
  exact this.of_eq (fun p => (lowerThresholdAt_eq_lowerAtG p.1 p.2).symm)

end DisequalityDispersion.Encoded
