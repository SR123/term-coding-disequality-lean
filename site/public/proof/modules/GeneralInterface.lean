import GeneralComputable
import GeneralSemidecision
import GeneralAsymptotics
import GeneralExamples
import WitnessSize
import ParsingExec
import FlowCutExec
import FinalInterface

/-! # Final theorem interface for the all-degree manuscript (R8)

Every conjunct is a previously proved theorem.  The only external input is the
explicit classical hypothesis on one fixed finite presentation
(`slobodskoiBridsonWilton`); the finite-graph Menger input of the earlier
routing module is now a theorem (`mengerInput`), and the earlier search
hypothesis is discharged (`searchComputable`).  All statements refer to the
actual shared-table maximum `dispersionTuple` of the decoded general instance
through `GInstance.dispersion`, `GInstance.Lower k`, `GInstance.Strict k`. -/

namespace DisequalityDispersion.Encoded

/-- **All-degree headline interface.**  Relative to the explicit classical input,
for every fixed degree `k ≥ 2` on the single general encoded class `GInstance`:
1. `Lower k` (attainment of `n^k - n^(k-1)`) is not computable;
2. `Lower k` is recursively enumerable and its complement is not;
3. `Strict k` (attainment of `n^k - n^(k-1) + 1`) is computable, decided exactly by
   the executable procedure `strictDecideG k`, which rejects malformed inputs;
4. the compiled degree-`k` instances are yes-instances of `Lower k` exactly when the
   presented element has a finite quotient in which it is nontrivial, and they are never
   strict;
5. no total computable alphabet bound exists for `Lower k`. -/
theorem all_degree_headline (d : ℕ) (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) (k : ℕ) (hk : 2 ≤ k) :
    (¬ ComputablePred (GInstance.Lower k)) ∧
    (REPred (GInstance.Lower k) ∧ ¬ REPred (fun g : GInstance => ¬ g.Lower k)) ∧
    (ComputablePred (GInstance.Strict k) ∧
      (∀ g : GInstance, g.strictDecideG k = true ↔ g.Strict k) ∧
      (∀ g : GInstance, ¬ g.Valid → g.strictDecideG k = false)) ∧
    (∀ w : List (Letter (Fin d)),
      ((compileDegree k d rels w).Lower k ↔ HasFiniteQuotient rels w) ∧
        ¬ (compileDegree k d rels w).Strict k) ∧
    (∀ (sz : GInstance → ℕ), Computable sz → ∀ (B : ℕ → ℕ), Computable B →
      ¬ ∀ g : GInstance, g.Lower k → ∃ n, 2 ≤ n ∧ n ≤ B (sz g) ∧ lowerAtG k g n = true) := by
  refine ⟨not_computablePred_Lower_degree k d rels hk slobodskoiBridsonWilton,
    ⟨rePred_Lower_degree k, not_rePred_not_Lower_degree k hk d rels slobodskoiBridsonWilton⟩,
    ⟨computablePred_Strict_degree k hk, fun g => g.strictDecideG_iff k hk,
      fun g h => g.strictDecideG_of_invalid k h⟩,
    fun w => ⟨Lower_compileDegree_iff_quotient k d rels w hk, compileDegree_not_Strict k d rels w hk⟩,
    ?_⟩
  intro sz hsz B hB hbound
  exact no_computable_witness_bound_degree k hk d rels slobodskoiBridsonWilton sz hsz B hB hbound

/-- **Polynomial-time headline — exactly what is proved, claim by claim** (for every degree
`k ≥ 2`, unconditional, standard axioms only):

1. *Correctness*: the maximum-flow procedure `strictDecideP k` is exactly correct against
   `Strict k`, its cut computation `rhoFlow` equals `ρ` of the decoded instance, invalid records
   are rejected; and on *every* bit string `bs` the parse-then-decide procedure `decideBits`
   accepts exactly the canonical language `StrictBits` (`decodeInput` accepts exactly the
   canonical encodings).
2. *Computability*: `Strict k` is a computable predicate and `strictDecideP` is primitive
   recursive.
3. *Polynomial bound on the named charged cost*: `strictDecidePC k g ≤ 91000·S⁶ + 3·natC k`
   with `S = sizeG g` the instance bit length and `natC k + S` the input length; and on every
   bit string `decideBitsC bs ≤ 92000·(|bs|+1)⁶`.  The charged cost follows the executable
   definitions operation by operation under the evaluation rules stated in `FlowCost.lean`.
4. *Execution link to a concrete program*: the charged costs are the exact step counts of
   instrumented programs in the step-counting monad `Costed` (`CostMonad.lean`) whose values
   are the executable definitions: the parser `decodeInputM` (`ParsingExec.lean`), the
   decision procedure `strictDecidePM` (`FlowCutExec.lean`, built on the instrumented
   augmenting-path algorithm of `UnitFlowExec.lean`) and the whole-language program
   `decideBitsM`, with the Phase-A procedures `isValid`, `canonIds` (`PhaseAExec.lean`)
   and `testsDistinct` instrumented as well, so no black box remains.  The embedding is
   shallow: the step count is the sum of the declared `tick`s, and the correspondence
   between each `tick` and the primitive operation it charges is fixed by the program
   text.
5. *Standard-machine polynomial time*: **not** part of this theorem.  The remaining
   obligation is the simulation of the declared primitives (list cells, table accesses,
   binary arithmetic on labels, the Phase-A black boxes) on a fixed machine model within
   polynomial time in the charged steps; see the return report.

The last conjunct is the uniform witness-length bound: on yes-instances the witness alphabet
`s^(k+1)` has bit length at most `M · size M` for `M = k_sources + |nodes|`. -/
theorem polynomial_time_headline (k : ℕ) (hk : 2 ≤ k) :
    -- (1) correctness
    (∀ g : GInstance, (g.strictDecideP k = true ↔ g.Strict k) ∧
      (∀ hv : g.Valid, g.rhoFlow = cutSize (g.outputs hv) (g.tests hv)) ∧
      (¬ g.Valid → g.strictDecideP k = false)) ∧
    (∀ bs : List Bool, (decideBits bs = true ↔ StrictBits bs) ∧
      ∀ (k' : ℕ) (g : GInstance), decodeInput bs = some (k', g) ↔ bs = encodeInput k' g) ∧
    -- (2) computability
    (ComputablePred (GInstance.Strict k) ∧
      Primrec (fun p : ℕ × GInstance => p.2.strictDecideP p.1)) ∧
    -- (3) polynomial charged cost
    (∀ g : GInstance, g.strictDecidePC k ≤ 91000 * sizeG g ^ 6 + 3 * natC k ∧
      (encodeInput k g).length = natC k + sizeG g) ∧
    (∀ bs : List Bool, decideBitsC bs ≤ 92000 * (bs.length + 1) ^ 6) ∧
    -- (4) execution link: instrumented parser, decision procedure and whole-language program
    (∀ bs : List Bool, (decodeInputM bs).val = decodeInput bs ∧
      (decodeInputM bs).cost = decodeInputC bs) ∧
    (∀ g : GInstance, (g.strictDecidePM k).val = g.strictDecideP k ∧
      (g.strictDecidePM k).cost = g.strictDecidePC k) ∧
    (∀ bs : List Bool, (decideBitsM bs).val = decideBits bs ∧
      (decideBitsM bs).cost = decideBitsC bs) ∧
    -- uniform witness length
    (∀ g : GInstance, ∀ hv : g.Valid, g.Strict k →
      (((tupleSupport (g.outputs hv) (g.tests hv)).card ^ (k + 1)).size ≤
        (g.base.k + g.base.nodes.length) * (g.base.k + g.base.nodes.length).size)) :=
  ⟨fun g => ⟨g.strictDecideP_iff k hk, fun hv => g.rhoFlow_eq hv, g.strictDecideP_of_invalid k⟩,
    fun bs => ⟨decideBits_iff_StrictBits bs, fun k' g => decodeInput_eq_some_iff bs k' g⟩,
    ⟨computablePred_Strict_degree k hk, GInstance.primrec_strictDecideP⟩,
    fun g => ⟨g.strictDecidePC_le k, encodeInput_length k g⟩,
    decideBitsC_le_all,
    decodeInputM_spec,
    fun g => g.strictDecidePM_spec k,
    decideBitsM_spec,
    fun g hv h => (g.witness_size_uniform hv k hk h).2.2.2⟩

end Encoded

/-- **Semantic interface** (`thm:cut`, `prop:sharp-cut`, `thm:main` strict part,
`cor:eventual`), unconditional, for every class-`C` term instance:
`(n/s)^ρ ≤ D(n) ≤ b_ρ(n) ≤ n^ρ`; `b_ρ` is attained by identity outputs; for `k ≥ 2`,
`b_k + 1` is reached for one alphabet iff for all large alphabets iff no test has identical
sides and `k + 1 ≤ ρ`; and `log D(n) / log n → ρ`. -/
theorem semantic_interface {V F : Type} [Fintype V] [Fintype F] {arity : F → ℕ} {x y : V}
    {outputs : List (Term V F arity)} {tests : List (Term V F arity × Term V F arity)}
    (hC : InClassC x y outputs tests) (distinct : ∀ uv ∈ tests, uv.1 ≠ uv.2) :
    (∀ n, (tupleSupport outputs tests).card ≤ n →
      (n / (tupleSupport outputs tests).card) ^ cutSize outputs tests ≤
        dispersionTuple (A := Fin n) outputs tests ∧
      dispersionTuple (A := Fin n) outputs tests ≤ threshold (cutSize outputs tests) n ∧
      threshold (cutSize outputs tests) n ≤ n ^ cutSize outputs tests) ∧
    (∀ j (hj : 2 ≤ j) (n : ℕ), dispersionTuple (A := Fin n)
      (identityOutputs (F := F) (arity := arity) j) (firstGuard j hj) = threshold j n) ∧
    (∀ k, 2 ≤ k → (StrictT k outputs tests ↔ EventualStrictT k outputs tests) ∧
      (StrictT k outputs tests ↔ (∀ uv ∈ tests, uv.1 ≠ uv.2) ∧ k + 1 ≤ cutSize outputs tests)) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (dispersionTuple (A := Fin n) outputs tests) / Real.log n)
      Filter.atTop (nhds (cutSize outputs tests)) := by
  refine ⟨fun n hn => ⟨routing_lower_bound outputs tests distinct x n hn,
      dispersionTuple_le_threshold x y hC.hxy outputs tests hC.hx hC.hy hC.hguard n,
      threshold_le_pow _ _⟩,
    fun j hj n => sharp_example_dispersion j hj n,
    fun k hk => strictT_iff_eventual hC k hk,
    log_ratio_tendsto hC distinct⟩

end DisequalityDispersion
