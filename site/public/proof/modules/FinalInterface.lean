import StrictAlgorithm
import EncodedExamples
import EncodingCost
import EncodedCompiler
import EncodedComputable
import CompilerExamples
import FiniteSearch
import Semidecision
import Asymptotics
import Density
import ToyExample
import Flattening
import ReducedWords

/-! # Final theorem interface for the encoded C3 class (T9)

All statements refer to the actual shared-table maximum `dispersionOn`
through `Instance.dispersion`, `Instance.Lower` and `Instance.Strict`
(defined in `EncodedSyntax.lean`), on the single encoded input type
`Instance`.  Nothing here bundles assumed conclusions: every conjunct is a
previously proved theorem, and the only external input is the explicit
classical hypothesis on one fixed finite presentation. -/

namespace DisequalityDispersion.Encoded
open Instance

/-- The paper's `s`: the number of distinct subterms of the outputs and tests
together with all declared sources. -/
noncomputable def supportSize (γ : Instance) (hv : γ.Valid) : ℕ :=
  (instanceSupport (γ.outTerm hv) (γ.testTerms hv)).card

theorem supportSize_le (γ : Instance) (hv : γ.Valid) :
    supportSize γ hv ≤ γ.k + γ.nodes.length :=
  γ.instanceSupport_card_le hv

theorem k_add_nodes_le_size (γ : Instance) : γ.k + γ.nodes.length ≤ sizeInstance γ := by
  have h1 := length_le_listC natC γ.sources (fun x _ => one_le_natC x)
  have h2 := length_le_listC nodeC γ.nodes (fun x _ => one_le_nodeC x)
  unfold sizeInstance
  show γ.sources.length + γ.nodes.length ≤ _
  omega

/-- Size lemma: `s ≤ N` (the input bit length). -/
theorem supportSize_le_size (γ : Instance) (hv : γ.Valid) : supportSize γ hv ≤ sizeInstance γ :=
  (supportSize_le γ hv).trans (k_add_nodes_le_size γ)

/-- The `n = s³` witness recovered through the existing tagged construction. -/
theorem strict_witness_cube (γ : Instance) (hv : γ.Valid) (h : γ.strictDecide = true) :
    2 ≤ supportSize γ hv ^ 3 ∧
      supportSize γ hv ^ 3 * (supportSize γ hv ^ 3 - 1) + 1 ≤
        γ.dispersion hv (supportSize γ hv ^ 3) := by
  have hS := (γ.strictDecide_iff).mp h
  obtain ⟨hv', n, hn, hD⟩ := hS
  have hcrit := (strict_threshold_iff (γ.xv hv) (γ.yv hv) (γ.xv_ne_yv hv) (γ.outTerm hv)
    (γ.testTerms hv) (γ.guard_mem_testTerms hv)).mp ⟨n, hn, hD⟩
  set s := supportSize γ hv with hs
  have hs2 : 2 ≤ s := instanceSupport_card_two _ _ (γ.xv_ne_yv hv) _ _
  have hsn : s ≤ s ^ 3 := Nat.le_self_pow (by norm_num) s
  refine ⟨le_trans hs2 hsn, ?_⟩
  unfold Instance.dispersion
  exact (cubic_witness_arithmetic s hs2).trans
    (cubic_lower_of_criterion (γ.xv hv) (γ.yv hv) (γ.xv_ne_yv hv) (γ.outTerm hv)
      (γ.testTerms hv) hcrit (s ^ 3) hsn)

/-- **Headline interface.**  Relative to the explicit classical input for one
fixed finite presentation `rels` over `Fin d`:
1. `Lower` is not computable on encoded C3 inputs;
2. `strictDecide` decides `Strict` exactly;
3. its charged cost is at most `20 N³` bits steps for input bit length `N`;
4. the three-source examples are a positive and a negative strict instance;
5. every positive strict instance has the witness `n = s³` with `s ≤ N`. -/
theorem headline (d : ℕ) (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    (¬ ComputablePred Instance.Lower) ∧
    (∀ γ : Instance, γ.strictDecide = true ↔ γ.Strict) ∧
    (∀ γ : Instance, γ.strictDecideC ≤ 20 * sizeInstance γ ^ 3) ∧
    (exPos3.Strict ∧ ¬ exNeg3.Strict) ∧
    (∀ (γ : Instance) (hv : γ.Valid), γ.strictDecide = true →
      supportSize γ hv ≤ sizeInstance γ ∧ 2 ≤ supportSize γ hv ^ 3 ∧
        supportSize γ hv ^ 3 * (supportSize γ hv ^ 3 - 1) + 1 ≤
          γ.dispersion hv (supportSize γ hv ^ 3)) :=
  ⟨not_computablePred_Lower d rels slobodskoiBridsonWilton,
    fun γ => γ.strictDecide_iff,
    fun γ => γ.strictDecideC_le,
    ⟨exPos3_Strict, exNeg3_not_Strict⟩,
    fun γ hv h => ⟨supportSize_le_size γ hv, (strict_witness_cube γ hv h).1,
      (strict_witness_cube γ hv h).2⟩⟩

/-- The hard family is the same encoded class: `Lower` on `compileWord` is
the finite-quotient problem, `compileWord` is primitive recursive, and the
classical input may equivalently be stated on freely reduced words. -/
theorem hard_family_interface (d : ℕ) (rels : List (List (Letter (Fin d)))) :
    (∀ w, (compileWord d rels w).Valid) ∧
    (∀ w, (compileWord d rels w).Lower ↔ HasFiniteQuotient rels w) ∧
    (∀ w, (compileWord d rels w).tests.length = 2 * d + rels.length + 2) ∧
    Primrec (compileWord d rels) ∧
    (¬ ComputablePred (fun w : {w : List (Letter (Fin d)) // Reduced w} =>
        HasFiniteQuotient rels w.1) ↔ ¬ ComputablePred (HasFiniteQuotient rels)) :=
  ⟨compileWord_valid d rels, Lower_compileWord_iff_quotient d rels,
    compileWord_tests_length d rels, primrec_compileWord d rels,
    not_computable_iff_reduced rels⟩

end DisequalityDispersion.Encoded
