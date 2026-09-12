import FiniteSearch
import EncodedComputable

/-! # Recursive enumerability and the absence of a computable witness bound (T4)

Everything in this module is relative to the explicit hypothesis
`SearchComputable`: that the executable finite search `lowerThresholdAt`
(which enumerates all tables on `Fin n`) is computable in mathlib's sense.
The executable definition and its agreement with the specification are
proved in `FiniteSearch.lean`; a `Primrec`/`Computable` proof for it in
mathlib's framework is not supplied here, so the statements below are
conditional and are reported as such.

* `rePred_Lower`: `Lower` is recursively enumerable (dovetailing over `n` via `Nat.rfind`).
* `not_rePred_not_Lower`: under the classical input, the complement is not r.e.
* `no_computable_witness_bound`: no total computable `B` bounds, in terms of any
  computable size function of the input, a witnessing alphabet for every
  `Lower` yes-instance. -/

namespace DisequalityDispersion.Encoded
open Instance

/-- Mathlib computability of the finite search at one alphabet size. -/
def SearchComputable : Prop :=
  Computable₂ (fun (γ : Instance) (n : ℕ) => γ.lowerThresholdAt n)

/-- `Lower` is recursively enumerable, given the computable finite search. -/
theorem rePred_Lower (hs : SearchComputable) : REPred Instance.Lower := by
  have hp : Partrec₂ (fun (γ : Instance) (n : ℕ) =>
      (Part.some (γ.lowerThresholdAt n) : Part Bool)) := hs.partrec₂
  have := (Partrec.rfind hp).dom_re
  refine this.of_eq (fun γ => ?_)
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, -⟩
    exact γ.Lower_iff_exists_lowerThresholdAt.mpr ⟨n, (Part.mem_some_iff.mp hn).symm⟩
  · intro h
    obtain ⟨n, hn⟩ := γ.Lower_iff_exists_lowerThresholdAt.mp h
    exact ⟨n, Part.mem_some_iff.mpr hn.symm, fun _ => trivial⟩

/-- Under the classical input, the complement of `Lower` is not r.e. -/
theorem not_rePred_not_Lower (hs : SearchComputable) (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    ¬ REPred (fun γ : Instance => ¬ γ.Lower) := by
  intro h
  apply not_computablePred_Lower d rels slobodskoiBridsonWilton
  exact ComputablePred.computable_iff_re_compl_re'.mpr ⟨rePred_Lower hs, h⟩

/-- Bounded search: some `n < b` passes the finite threshold test. -/
def boundedAny (γ : Instance) (b : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun y IH => IH || γ.lowerThresholdAt y) b

theorem boundedAny_iff (γ : Instance) (b : ℕ) :
    boundedAny γ b = true ↔ ∃ n, n < b ∧ γ.lowerThresholdAt n = true := by
  induction b with
  | zero => simp [boundedAny]
  | succ b ih =>
      simp only [boundedAny, Bool.or_eq_true] at ih ⊢
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

theorem computable_boundedAny (hs : SearchComputable) {f : Instance → ℕ} (hf : Computable f) :
    Computable (fun γ => boundedAny γ (f γ)) := by
  have hh : Computable₂ (fun (γ : Instance) (p : ℕ × Bool) => p.2 || γ.lowerThresholdAt p.1) := by
    apply Computable₂.mk
    have := Computable.cond (c := fun q : Instance × (ℕ × Bool) => q.2.2)
      (f := fun _ => true) (g := fun q : Instance × (ℕ × Bool) => q.1.lowerThresholdAt q.2.1)
      (Computable.snd.comp Computable.snd) (Computable.const true)
      (hs.comp Computable.fst (Computable.fst.comp Computable.snd))
    refine this.of_eq (fun q => ?_)
    rcases q with ⟨γ, n, b⟩
    cases b <;> rfl
  exact Computable.nat_rec hf (Computable.const false) hh

/-- **No computable witness bound.**  For any computable size function `sz`,
no total computable `B` satisfies: every `Lower` yes-instance has a witnessing
alphabet `2 ≤ n ≤ B (sz γ)` passing the finite threshold test. -/
theorem no_computable_witness_bound (hs : SearchComputable) (d : ℕ)
    (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels))
    (sz : Instance → ℕ) (hsz : Computable sz) (B : ℕ → ℕ) (hB : Computable B)
    (hbound : ∀ γ : Instance, γ.Lower →
      ∃ n, 2 ≤ n ∧ n ≤ B (sz γ) ∧ γ.lowerThresholdAt n = true) : False := by
  apply not_computablePred_Lower d rels slobodskoiBridsonWilton
  refine ComputablePred.computable_iff.mpr
    ⟨fun γ => boundedAny γ (B (sz γ) + 1),
      computable_boundedAny hs (Computable.succ.comp (hB.comp hsz)), ?_⟩
  funext γ
  apply propext
  rw [boundedAny_iff]
  constructor
  · intro h
    obtain ⟨n, _, hn, hpass⟩ := hbound γ h
    exact ⟨n, by omega, hpass⟩
  · rintro ⟨n, _, hpass⟩
    exact (γ.Lower_iff_exists_lowerThresholdAt).mpr ⟨n, hpass⟩

end DisequalityDispersion.Encoded
