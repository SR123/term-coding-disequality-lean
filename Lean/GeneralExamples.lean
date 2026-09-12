import TermMenger
import DegreeCompiler
import GeneralAsymptotics
import GeneralAlgorithm

/-! # Required general examples and regressions (R7)

* `dispersionTuple_mapVar_inj`: unused or renamed sources do not change `D`.
* `cutSize_tests_irrelevant`: `ρ` depends only on the outputs (sources that
  appear only in tests, and tests themselves, create no output paths).
* `identity_example`: identity outputs on `k+1` sources give `D = b_(k+1)`;
  `repeat_example`: outputs `(x₁, …, x_k, x₁)` on `k+1` sources give `D = b_k`.
* `identical_test_not_lower`: an identical-side test is a `Lower` no-instance.
* `threshold_interleave` (re-exported): `b_k(n) < b_k(n)+1 < b_(k+1)(n)`.
* `bottleneck_cutSize`: `(x, y, f(z), g(f(z)))` has `ρ = 3`, not `4`.
* `nullary_cutSize`, `repeatedArg_cutSize`: nullaries and repeated arguments
  create no extra paths.
* `outsideC_dispersion`: outputs `(z, w)` with guard `x ≠ y` have `ρ = 2` and `D = n²`,
  violating `D ≤ b_ρ`; the retained-pair hypothesis is necessary.
* `dupInstance_dispersion_zero`: duplicate computations in a test canonicalise
  to identical sides (encoded example).
* `bottleneckG_rho`, `bottleneckG_strict2`, `bottleneckG_strict3`: the encoded
  bottleneck instance run through the executable decision (`decide`). -/

namespace DisequalityDispersion
variable {V V' F A : Type} {arity : F → ℕ}

/-! ### Renaming and unused sources -/

theorem tupleEval_mapVar (g : V → V') (ts : List (Term V F arity)) (I : Interpretation F arity A)
    (a : V' → A) : tupleEval (ts.map (Term.mapVar g)) I a = tupleEval ts I (fun v => a (g v)) := by
  unfold tupleEval
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  exact Term.eval_mapVar g I a t

open Classical in
theorem filteredImage_mapVar [Fintype V] [Fintype V'] [Fintype A] [Nonempty V] (g : V → V')
    (hg : Function.Injective g) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (I : Interpretation F arity A) :
    filteredImage (outputs.map (Term.mapVar g)) (mapVarTests g tests) I =
      filteredImage outputs tests I := by
  ext o
  simp only [filteredImage, validAssignments, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Valid_mapVarTests, tupleEval_mapVar]
  constructor
  · rintro ⟨a', ha', rfl⟩
    exact ⟨fun v => a' (g v), ha', rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun v' => a (Function.invFun g v'), ?_, ?_⟩
    · have : (fun v => a (Function.invFun g (g v))) = a := by
        funext v
        rw [Function.leftInverse_invFun hg v]
      rw [this]; exact ha
    · congr 1
      funext v
      show a (Function.invFun g (g v)) = a v
      rw [Function.leftInverse_invFun hg v]

/-- Renaming sources injectively (in particular adding unused sources) preserves `D`. -/
theorem dispersionTuple_mapVar_inj [Fintype V] [Fintype V'] [Fintype F] [Fintype A] [Nonempty V]
    (g : V → V') (hg : Function.Injective g) (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) :
    dispersionTuple (A := A) (outputs.map (Term.mapVar g)) (mapVarTests g tests) =
      dispersionTuple (A := A) outputs tests := by
  classical
  apply le_antisymm
  · apply dispersionTuple_le_of_forall
    intro I
    rw [filteredImage_mapVar g hg]
    exact image_le_dispersionTuple _ _ _
  · apply dispersionTuple_le_of_forall
    intro I
    rw [← filteredImage_mapVar g hg outputs tests I]
    exact image_le_dispersionTuple _ _ _

/-! ### `ρ` depends only on the outputs -/

open Classical in
/-- All cuts can be shrunk to the sources and output subterms. -/
theorem cutSize_tests_irrelevant [Fintype V] (outputs : List (Term V F arity))
    (tests tests' : List (Term V F arity × Term V F arity)) :
    cutSize outputs tests = cutSize outputs tests' := by
  -- a minimum cut for `tests` is a cut, hence bounds `cutSize outputs tests'`, and symmetrically
  apply le_antisymm
  · obtain ⟨K, _, hK, hc⟩ := exists_min_cut outputs tests'
    rw [← hc]
    exact cutSize_le_card_of_isCut outputs tests K hK
  · obtain ⟨K, _, hK, hc⟩ := exists_min_cut outputs tests
    rw [← hc]
    exact cutSize_le_card_of_isCut outputs tests' K hK

/-! ### Exact computation of `ρ` from a cut and a lower bound -/

theorem cutSize_eq_of [Fintype V] (outputs : List (Term V F arity))
    (tests : List (Term V F arity × Term V F arity)) (m : ℕ) (K : Finset (Term V F arity))
    (hK : IsCut K outputs) (hcard : K.card = m) (hlow : ∀ K', IsCut K' outputs → m ≤ K'.card) :
    cutSize outputs tests = m := by
  apply le_antisymm
  · rw [← hcard]; exact cutSize_le_card_of_isCut outputs tests K hK
  · obtain ⟨K', _, hK', hc⟩ := exists_min_cut outputs tests
    rw [← hc]; exact hlow K' hK'

/-! ### Identity and repeated-coordinate outputs on `k + 1` sources -/

section identity
variable [Fintype F]

/-- Identity outputs on `k+1` sources with the guard: `D = b_(k+1)(n)`. -/
theorem identity_example (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    dispersionTuple (A := Fin n) (identityOutputs (F := F) (arity := arity) (k + 1))
      (firstGuard (k + 1) (by omega)) = threshold (k + 1) n :=
  sharp_example_dispersion (k + 1) (by omega) n

/-- Appending an output coordinate that already occurs does not change `D`. -/
theorem dispersionTuple_append_dup [Fintype V] [Fintype A] (outputs : List (Term V F arity))
    (u : Term V F arity) (hu : u ∈ outputs) (tests : List (Term V F arity × Term V F arity)) :
    dispersionTuple (A := A) (outputs ++ [u]) tests = dispersionTuple (A := A) outputs tests := by
  classical
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
  have key : ∀ I : Interpretation F arity A,
      (filteredImage (outputs ++ [outputs[i]]) tests I).card = (filteredImage outputs tests I).card := by
    intro I
    have himg : filteredImage (outputs ++ [outputs[i]]) tests I =
        (filteredImage outputs tests I).image (fun l => l ++ l[i]?.toList) := by
      ext o
      simp only [filteredImage, Finset.mem_image, validAssignments, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
        unfold tupleEval
        rw [List.map_append, List.map_singleton, List.getElem?_map,
          List.getElem?_eq_getElem hi]
        rfl
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨a, ha, ?_⟩
        unfold tupleEval
        rw [List.map_append, List.map_singleton, List.getElem?_map,
          List.getElem?_eq_getElem hi]
        rfl
    rw [himg]
    apply Finset.card_image_of_injOn
    intro l hl l' hl' h
    have hlen : l.length = outputs.length := by
      simp only [filteredImage, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hl
      obtain ⟨a, _, rfl⟩ := hl
      simp [tupleEval]
    have hlen' : l'.length = outputs.length := by
      simp only [filteredImage, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hl'
      obtain ⟨a, _, rfl⟩ := hl'
      simp [tupleEval]
    simp only at h
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h
    exact (List.append_inj h (by omega)).1
  unfold dispersionTuple
  apply Finset.sup_congr rfl
  intro I _
  exact key I

/-- Outputs `(x₁, …, x_k, x₁)` on `k+1` sources with the guard: `D = b_k(n)`
(the `(k+1)`-st source is unused and the repeated coordinate adds nothing). -/
theorem repeat_example (k : ℕ) (hk : 2 ≤ k) (n : ℕ) [NeZero n] :
    dispersionTuple (A := Fin n)
      (((identityOutputs (F := F) (arity := arity) k) ++
          [(Term.var ⟨0, by omega⟩ : Term (Fin k) F arity)]).map
        (Term.mapVar (Fin.castLE (Nat.le_succ k))))
      (mapVarTests (Fin.castLE (Nat.le_succ k)) (firstGuard k hk)) = threshold k n := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rw [dispersionTuple_mapVar_inj _ (Fin.castLE_injective _), dispersionTuple_append_dup,
    sharp_example_dispersion k hk n]
  simp [identityOutputs]

end identity

/-! ### Identical-side tests, interleaving -/

/-- An identical-side test makes every degree a `Lower` no-instance. -/
theorem identical_test_not_lower [Fintype V] [Fintype F] (k : ℕ) (hk : 1 ≤ k)
    (outputs : List (Term V F arity)) (u : Term V F arity)
    (tests : List (Term V F arity × Term V F arity)) (hu : (u, u) ∈ tests) :
    ¬ LowerT k outputs tests := by
  rintro ⟨n, hn, h⟩
  rw [identical_test_dispersionTuple_zero outputs u tests hu, threshold_eq k n hk] at h
  have : 0 < n ^ (k - 1) * (n - 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  omega

/-- `b_k(n) < b_k(n) + 1 < b_(k+1)(n)` for `n ≥ 2`, `k ≥ 2` (re-export). -/
theorem threshold_interleave' (k n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n) :
    threshold k n < threshold k n + 1 ∧ threshold k n + 1 < threshold (k + 1) n :=
  threshold_interleave k n hk hn

/-! ### Cut computations on small term instances -/

section small
open Classical

theorem three_le_card_of_mem (K : Finset (Term V F arity)) (a b c : Term V F arity)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    3 ≤ K.card := by
  have hsub : ({a, b, c} : Finset (Term V F arity)) ⊆ K := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset (Term V F arity)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hbc
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac⟩
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Two unary symbols `f = 0`, `g = 1`. -/
abbrev Unary2 := Fin 2
abbrev unaryArity : Unary2 → ℕ := fun _ => 1

/-- The shared-bottleneck outputs `(x, y, f(z), g(f(z)))` on sources `x = 0, y = 1, z = 2`. -/
def bottleneckOutputs : List (Term (Fin 3) Unary2 unaryArity) :=
  [.var 0, .var 1, .app 0 (fun _ => .var 2), .app 1 (fun _ => .app 0 (fun _ => .var 2))]

def bottleneckTests : List (Term (Fin 3) Unary2 unaryArity × Term (Fin 3) Unary2 unaryArity) :=
  [(.var 0, .var 1)]

/-- `(x, y, f(z), g(f(z)))` has `ρ = 3`: the two outputs through `f(z)` share one bottleneck. -/
theorem bottleneck_cutSize : cutSize bottleneckOutputs bottleneckTests = 3 := by
  apply cutSize_eq_of _ _ 3 {Term.var 0, Term.var 1, Term.app 0 (fun _ => Term.var 2)}
  · -- it is a cut
    intro t ht ha
    simp only [bottleneckOutputs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact (avoids_var_iff _ _).mp ha (by simp)
    · exact (avoids_var_iff _ _).mp ha (by simp)
    · cases ha with
      | app _ _ hn _ _ => exact hn (by simp)
    · cases ha with
      | app _ _ _ _ hi =>
          cases hi with
          | app _ _ hn _ _ => exact hn (by simp)
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp
    · simp
  · -- every cut has at least three vertices
    intro K hK
    obtain ⟨hx, hy⟩ := retained_pair_mem_cut K bottleneckOutputs hK 0 1 (by simp [bottleneckOutputs])
      (by simp [bottleneckOutputs])
    have hf : ¬ Avoids K (Term.app 0 (fun _ => Term.var 2) : Term (Fin 3) Unary2 unaryArity) :=
      hK _ (by simp [bottleneckOutputs])
    by_cases hfz : (Term.app 0 (fun _ => Term.var 2) : Term (Fin 3) Unary2 unaryArity) ∈ K
    · exact three_le_card_of_mem K _ _ _ (by simp) (by simp) (by simp) hx hy hfz
    · by_cases hz : (Term.var 2 : Term (Fin 3) Unary2 unaryArity) ∈ K
      · exact three_le_card_of_mem K _ _ _ (by simp) (by simp) (by simp) hx hy hz
      · exact absurd (Avoids.app 0 _ hfz 0 (Avoids.var 2 hz)) hf

/-- A nullary symbol. -/
abbrev nullaryArity : Fin 1 → ℕ := fun _ => 0

/-- `(x, y, c)` with `c` a constant: `ρ = 2`. -/
theorem nullary_cutSize :
    cutSize ([.var 0, .var 1, .app 0 (fun i => Fin.elim0 i)] : List (Term (Fin 2) (Fin 1) nullaryArity))
      [(.var 0, .var 1)] = 2 := by
  apply cutSize_eq_of _ _ 2 {Term.var 0, Term.var 1}
  · intro t ht ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact (avoids_var_iff _ _).mp ha (by simp)
    · exact (avoids_var_iff _ _).mp ha (by simp)
    · cases ha with
      | app _ _ _ i _ => exact Fin.elim0 i
  · rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp
  · intro K hK
    obtain ⟨hx, hy⟩ := retained_pair_mem_cut K _ hK 0 1 (by simp) (by simp)
    have : ({Term.var 0, Term.var 1} : Finset (Term (Fin 2) (Fin 1) nullaryArity)) ⊆ K := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have h2 : ({Term.var 0, Term.var 1} : Finset (Term (Fin 2) (Fin 1) nullaryArity)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]; simp
    have := Finset.card_le_card this
    rw [h2] at this
    exact this

/-- A binary symbol. -/
abbrev binaryArity : Fin 1 → ℕ := fun _ => 2

/-- `(x, y, f(x, x))` with a repeated argument: `ρ = 2`. -/
theorem repeatedArg_cutSize :
    cutSize ([.var 0, .var 1, .app 0 (fun _ => .var 0)] : List (Term (Fin 2) (Fin 1) binaryArity))
      [(.var 0, .var 1)] = 2 := by
  apply cutSize_eq_of _ _ 2 {Term.var 0, Term.var 1}
  · intro t ht ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact (avoids_var_iff _ _).mp ha (by simp)
    · exact (avoids_var_iff _ _).mp ha (by simp)
    · cases ha with
      | app _ _ _ _ hi => exact (avoids_var_iff _ _).mp hi (by simp)
  · rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp
  · intro K hK
    obtain ⟨hx, hy⟩ := retained_pair_mem_cut K _ hK 0 1 (by simp) (by simp)
    have : ({Term.var 0, Term.var 1} : Finset (Term (Fin 2) (Fin 1) binaryArity)) ⊆ K := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    have h2 : ({Term.var 0, Term.var 1} : Finset (Term (Fin 2) (Fin 1) binaryArity)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]; simp
    have := Finset.card_le_card this
    rw [h2] at this
    exact this

end small

/-! ### Outside class `C`: the retained pair is necessary -/

section outside

/-- No symbols. -/
abbrev noArity : Fin 0 → ℕ := Fin.elim0

/-- Outputs `(z, w)` on sources `x = 0, y = 1, z = 2, w = 3` with the guard `x ≠ y`. -/
def outsideOutputs : List (Term (Fin 4) (Fin 0) noArity) := [.var 2, .var 3]
def outsideTests : List (Term (Fin 4) (Fin 0) noArity × Term (Fin 4) (Fin 0) noArity) :=
  [(.var 0, .var 1)]

theorem outside_cutSize : cutSize outsideOutputs outsideTests = 2 := by
  rw [cutSize_of_all_vars]
  · simp [outsideOutputs]
  · intro t ht
    simp only [outsideOutputs, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩

open Classical in
/-- `D(n) = n²` for `n ≥ 2`: every pair of values is reached, so `D > b_ρ = n(n-1)`. -/
theorem outside_dispersion (n : ℕ) (hn : 2 ≤ n) :
    dispersionTuple (A := Fin n) outsideOutputs outsideTests = n ^ 2 := by
  haveI : NeZero n := ⟨by omega⟩
  apply le_antisymm
  · apply dispersionTuple_le_of_forall
    intro I
    -- the image injects into `Fin n × Fin n`
    have : (filteredImage outsideOutputs outsideTests I).card ≤
        (Finset.univ : Finset (Fin n × Fin n)).card := by
      apply Finset.card_le_card_of_injOn (fun l => (l.getD 0 0, l.getD 1 0))
      · intro _ _; exact Finset.mem_univ _
      · intro l hl l' hl' h
        simp only [filteredImage, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hl hl'
        obtain ⟨a, _, rfl⟩ := hl
        obtain ⟨a', _, rfl⟩ := hl'
        simp only [outsideOutputs, tupleEval, List.map_cons, List.map_nil, Term.eval,
          List.getD_cons_zero, List.getD_cons_succ, Prod.mk.injEq] at h
        simp [outsideOutputs, tupleEval, Term.eval, h.1, h.2]
    simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq] using this
  · have hI : ∃ I : Interpretation (Fin 0) noArity (Fin n), True := ⟨fun f => Fin.elim0 f, trivial⟩
    obtain ⟨I, _⟩ := hI
    refine le_trans ?_ (image_le_dispersionTuple outsideOutputs outsideTests I)
    -- every pair `(p, q)` is reached by an assignment with `a 0 = 0 ≠ 1 = a 1`
    have : (Finset.univ : Finset (Fin n × Fin n)).card ≤
        (filteredImage outsideOutputs outsideTests I).card := by
      apply Finset.card_le_card_of_injOn (fun pq : Fin n × Fin n => [pq.1, pq.2])
      · intro pq _
        simp only [filteredImage, validAssignments, Finset.coe_image, Set.mem_image,
          Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun i => if i.1 = 2 then pq.1 else if i.1 = 3 then pq.2 else
          if i.1 = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩, ?_, ?_⟩
        · unfold Valid outsideTests
          simp only [List.mem_singleton, forall_eq, Term.eval]
          simp [Fin.ext_iff]
        · simp [outsideOutputs, tupleEval, Term.eval]
      · intro pq _ pq' _ h
        simp only [List.cons.injEq, and_true] at h
        exact Prod.ext h.1 h.2
    simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq] using this

/-- Outside `C` the sharp bound `D ≤ b_ρ` fails: `n² > n(n-1) = b_2(n)`. -/
theorem outside_exceeds_threshold (n : ℕ) (hn : 2 ≤ n) :
    threshold (cutSize outsideOutputs outsideTests) n <
      dispersionTuple (A := Fin n) outsideOutputs outsideTests := by
  rw [outside_cutSize, outside_dispersion n hn, threshold_two]
  have : n * (n - 1) < n * n := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  rw [sq]; exact this

end outside

/-! ### Encoded regression: duplicate computations canonicalise -/

namespace Encoded

/-- Sources `x = 0`, `y = 1`; one unary symbol; nodes `x, y, f(x), f(x)` (the last two
compute the same term); tests `x ≠ y` and `f(x) ≠ f(x)` (node `2` against node `3`);
output `f(x)`. -/
def dupInstance : GInstance :=
  ⟨{ sources := [0, 1], symbols := [(0, 1)], nodes := [.src 0, .src 1, .app 0 [0], .app 0 [0]],
     x := 0, y := 1, t := 2, tests := [(0, 1), (2, 3)] }, [2]⟩

theorem dupInstance_valid : dupInstance.Valid := by decide

/-- The two duplicate nodes decode to the same term. -/
theorem dupInstance_dup :
    dupInstance.base.termD (dupInstance.baseValid dupInstance_valid) 3 =
      dupInstance.base.termD (dupInstance.baseValid dupInstance_valid) 2 := rfl

/-- The decoded instance has an identical-side test, so `D = 0` on every alphabet. -/
theorem dupInstance_dispersion_zero (n : ℕ) :
    dupInstance.dispersion dupInstance_valid n = 0 := by
  unfold GInstance.dispersion
  apply identical_test_dispersionTuple_zero _ (dupInstance.base.termD (dupInstance.baseValid dupInstance_valid) 2)
  unfold GInstance.tests Instance.testTerms
  simp only [List.mem_map]
  refine ⟨(2, 3), by simp [dupInstance], ?_⟩
  rw [dupInstance_dup]

theorem dupInstance_not_lower (k : ℕ) (hk : 1 ≤ k) : ¬ dupInstance.Lower k := by
  rintro ⟨hv, n, hn, h⟩
  rw [dupInstance_dispersion_zero, threshold_eq k n hk] at h
  have : 0 < n ^ (k - 1) * (n - 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  omega

/-! ### The executable decision on the encoded bottleneck instance -/

/-- Encoded bottleneck instance: sources `x = 0, y = 1, z = 2`; unary symbols `f = 0`, `g = 1`;
nodes `0: x, 1: y, 2: z, 3: f(z), 4: g(f(z))`; test `x ≠ y`; outputs `(x, y, f(z), g(f(z)))`. -/
def bottleneckG : GInstance :=
  ⟨{ sources := [0, 1, 2], symbols := [(0, 1), (1, 1)],
     nodes := [.src 0, .src 1, .src 2, .app 0 [2], .app 1 [3]],
     x := 0, y := 1, t := 3, tests := [(0, 1)] }, [3, 4]⟩

theorem bottleneckG_valid : bottleneckG.Valid := by decide

/-- The executable cut computation returns `ρ = 3` (kernel evaluation). -/
theorem bottleneckG_rho : bottleneckG.rhoExec = 3 := by decide

/-- Strict at degree `2` (`ρ ≥ 3`), hence a `Strict 2` yes-instance by `strictDecideG_iff`. -/
theorem bottleneckG_strict2 : bottleneckG.strictDecideG 2 = true := by decide

theorem bottleneckG_Strict2 : bottleneckG.Strict 2 :=
  (bottleneckG.strictDecideG_iff 2 le_rfl).mp bottleneckG_strict2

/-- Not strict at degree `3` (`ρ = 3 < 4`). -/
theorem bottleneckG_strict3 : bottleneckG.strictDecideG 3 = false := by decide

theorem bottleneckG_not_Strict3 : ¬ bottleneckG.Strict 3 := by
  intro h
  have := (bottleneckG.strictDecideG_iff 3 (by norm_num)).mpr h
  rw [bottleneckG_strict3] at this
  exact absurd this (by decide)

end Encoded

end DisequalityDispersion
