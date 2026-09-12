import Tagged
import BuildList

/-! # Executable encoded syntax for C3 instances (task T1)

A C3 instance is given as an explicit finite structure: a list of source
names, a list of symbol names with arities, a topologically ordered list of
DAG nodes (each a source reference or a symbol applied to earlier nodes),
the indices of the retained sources `x,y`, the node index of the output term
`t`, and the list of tests as pairs of node indices.  Everything is a natural
number or a list, so the representation is serialisable and its bit length is
the honest size measure (every declared source and every argument position is
written out).

`decodeFuel` translates nodes to the existing `Term` type; `evalNodes` is a
linear-time executable evaluator.  The main theorems connect both to the
shared-table semantics of `Semantics.lean`. -/

namespace DisequalityDispersion
namespace Encoded

/-- A DAG node: a source reference, or a symbol applied to earlier nodes. -/
inductive Node where
  | src (i : ℕ)
  | app (f : ℕ) (args : List ℕ)
deriving DecidableEq, Repr

/-- An explicitly encoded C3 instance. -/
structure Instance where
  sources : List ℕ
  symbols : List (ℕ × ℕ)
  nodes : List Node
  x : ℕ
  y : ℕ
  t : ℕ
  tests : List (ℕ × ℕ)
deriving DecidableEq, Repr

namespace Instance

variable (γ : Instance)

/-- Number of declared sources. -/
def k : ℕ := γ.sources.length
/-- Number of declared symbols. -/
def m : ℕ := γ.symbols.length
/-- Declared arity of symbol number `f` (junk value `0` out of range). -/
def arityOf (f : ℕ) : ℕ := (γ.symbols.getD f (0, 0)).2
/-- The arity function on the finite symbol type. -/
def arity : Fin γ.m → ℕ := fun f => γ.arityOf f.1

/-- The term type of the decoded instance. -/
abbrev Tm := Term (Fin γ.k) (Fin γ.m) γ.arity

/-- Well-formedness of the node at position `j`. -/
def nodeOk (j : ℕ) : Node → Bool
  | .src i => decide (i < γ.k)
  | .app f args =>
      decide (f < γ.m) && decide (args.length = γ.arityOf f) &&
        args.all (fun a => decide (a < j))

def nodesOk : Bool :=
  (List.range γ.nodes.length).all (fun j => γ.nodeOk j (γ.nodes.getD j (.src 0)))

/-- Some test is literally the guard `x ≠ y` on source nodes. -/
def guardOk : Bool :=
  γ.tests.any (fun ij =>
    decide (γ.nodes.getD ij.1 (.app 0 []) = .src γ.x) &&
      decide (γ.nodes.getD ij.2 (.app 0 []) = .src γ.y))

/-- Executable validity check. -/
def isValid : Bool :=
  decide (2 ≤ γ.k) && decide γ.sources.Nodup && decide (γ.symbols.map Prod.fst).Nodup &&
    decide (γ.x < γ.k) && decide (γ.y < γ.k) && decide (γ.x ≠ γ.y) &&
    γ.nodesOk && decide (γ.t < γ.nodes.length) &&
    γ.tests.all (fun ij => decide (ij.1 < γ.nodes.length) && decide (ij.2 < γ.nodes.length)) &&
    γ.guardOk

/-- Validity as a proposition. -/
def Valid : Prop := γ.isValid = true

instance : DecidablePred Instance.Valid := fun γ => by unfold Valid; infer_instance

/-- Assemble an application node from decoded children, or fail. -/
def appNode (f : ℕ) (hf : f < γ.m) (child : Fin (γ.arity ⟨f, hf⟩) → Option γ.Tm) :
    Option γ.Tm :=
  if hall : ∀ i, (child i).isSome then
    some (.app ⟨f, hf⟩ (fun i => (child i).get (hall i)))
  else none

theorem appNode_eq_some_iff (f : ℕ) (hf : f < γ.m)
    (child : Fin (γ.arity ⟨f, hf⟩) → Option γ.Tm) (u : γ.Tm) :
    γ.appNode f hf child = some u ↔
      ∃ ts : Fin (γ.arity ⟨f, hf⟩) → γ.Tm, (∀ i, child i = some (ts i)) ∧
        u = .app ⟨f, hf⟩ ts := by
  unfold appNode
  constructor
  · intro h
    split_ifs at h with hall
    · refine ⟨fun i => (child i).get (hall i), fun i => (Option.some_get (hall i)).symm, ?_⟩
      exact (Option.some.inj h).symm
  · rintro ⟨ts, hts, rfl⟩
    have hall : ∀ i, (child i).isSome := fun i => by rw [hts i]; rfl
    rw [dif_pos hall]
    congr 1
    congr 1
    funext i
    have := hts i
    exact Option.get_of_mem _ this

/-- Fuel-bounded decoding of node `j` into a term.  For a valid instance,
fuel `j + 1` suffices (`decodeFuel_succ_isSome`). -/
def decodeFuel : ℕ → ℕ → Option γ.Tm
  | 0, _ => none
  | fuel + 1, j =>
      match γ.nodes[j]? with
      | none => none
      | some (.src i) => if h : i < γ.k then some (.var ⟨i, h⟩) else none
      | some (.app f args) =>
          if hf : f < γ.m then
            γ.appNode f hf (fun i => decodeFuel fuel (args.getD i.1 0))
          else none

/-- Decoding with the canonical fuel. -/
def decode (j : ℕ) : Option γ.Tm := γ.decodeFuel γ.nodes.length j

theorem decodeFuel_zero (j : ℕ) : γ.decodeFuel 0 j = none := rfl

theorem decodeFuel_succ (fuel j : ℕ) :
    γ.decodeFuel (fuel + 1) j =
      match γ.nodes[j]? with
      | none => none
      | some (.src i) => if h : i < γ.k then some (.var ⟨i, h⟩) else none
      | some (.app f args) =>
          if hf : f < γ.m then
            γ.appNode f hf (fun i => γ.decodeFuel fuel (args.getD i.1 0))
          else none := rfl

/-- Decoding is monotone in the fuel. -/
theorem decodeFuel_mono (fuel j : ℕ) (u : γ.Tm)
    (h : γ.decodeFuel fuel j = some u) : γ.decodeFuel (fuel + 1) j = some u := by
  induction fuel generalizing j u with
  | zero => simp [decodeFuel_zero] at h
  | succ fuel ih =>
      rw [decodeFuel_succ] at h ⊢
      cases hn : γ.nodes[j]? with
      | none => rw [hn] at h; exact absurd h (by simp)
      | some nd =>
          rw [hn] at h
          cases nd with
          | src i => dsimp only at h ⊢; exact h
          | app f args =>
              dsimp only at h ⊢
              by_cases hf : f < γ.m
              · rw [dif_pos hf] at h ⊢
                obtain ⟨ts, hts, rfl⟩ := (γ.appNode_eq_some_iff f hf _ u).mp h
                exact (γ.appNode_eq_some_iff f hf _ _).mpr ⟨ts, fun i => ih _ _ (hts i), rfl⟩
              · rw [dif_neg hf] at h; exact absurd h (by simp)

theorem decodeFuel_le (fuel fuel' j : ℕ) (hle : fuel ≤ fuel') (u : γ.Tm)
    (h : γ.decodeFuel fuel j = some u) : γ.decodeFuel fuel' j = some u := by
  induction hle with
  | refl => exact h
  | step _ ih => exact γ.decodeFuel_mono _ _ _ ih

/-- The well-formedness of node `j` in terms of `nodeOk`. -/
theorem nodesOk_iff : γ.nodesOk = true ↔
    ∀ j (hj : j < γ.nodes.length), γ.nodeOk j (γ.nodes[j]'hj) = true := by
  unfold nodesOk
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    have := h j (List.mem_range.mpr hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro h j hj
    have hj' := List.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ hj']
    exact h j hj'

theorem nodeOk_src (j i : ℕ) : γ.nodeOk j (.src i) = true ↔ i < γ.k := by
  simp [nodeOk]

theorem nodeOk_app (j f : ℕ) (args : List ℕ) : γ.nodeOk j (.app f args) = true ↔
    f < γ.m ∧ args.length = γ.arityOf f ∧ ∀ a ∈ args, a < j := by
  simp [nodeOk, and_assoc]

/-- Validity unfolded into its conjuncts. -/
theorem valid_iff : γ.Valid ↔
    2 ≤ γ.k ∧ γ.sources.Nodup ∧ (γ.symbols.map Prod.fst).Nodup ∧
    γ.x < γ.k ∧ γ.y < γ.k ∧ γ.x ≠ γ.y ∧
    (∀ j (hj : j < γ.nodes.length), γ.nodeOk j (γ.nodes[j]'hj) = true) ∧
    γ.t < γ.nodes.length ∧
    (∀ ij ∈ γ.tests, ij.1 < γ.nodes.length ∧ ij.2 < γ.nodes.length) ∧
    γ.guardOk = true := by
  unfold Valid isValid
  rw [← nodesOk_iff]
  simp [List.all_eq_true, and_assoc]

/-- For a valid instance, fuel `j + 1` decodes node `j`. -/
theorem decodeFuel_succ_isSome (hv : γ.Valid) :
    ∀ j, j < γ.nodes.length → (γ.decodeFuel (j + 1) j).isSome := by
  have hnodes := (γ.valid_iff.mp hv).2.2.2.2.2.2.1
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      rw [decodeFuel_succ]
      have hok := hnodes j hj
      rw [List.getElem?_eq_getElem hj]
      cases hnd : γ.nodes[j] with
      | src i =>
          rw [hnd] at hok
          dsimp only
          rw [dif_pos ((γ.nodeOk_src j i).mp hok)]
          rfl
      | app f args =>
          rw [hnd] at hok
          obtain ⟨hf, hlen, hargs⟩ := (γ.nodeOk_app j f args).mp hok
          dsimp only
          rw [dif_pos hf]
          have hall : ∀ i : Fin (γ.arity ⟨f, hf⟩),
              (γ.decodeFuel j (args.getD i.1 0)).isSome := by
            intro i
            have hi : i.1 < args.length := by
              have : i.1 < γ.arityOf f := i.2
              omega
            rw [List.getD_eq_getElem _ _ hi]
            have ha : args[i.1] < j := hargs _ (List.getElem_mem hi)
            have hlt : args[i.1] < γ.nodes.length := lt_trans ha hj
            obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (ih _ ha hlt)
            rw [γ.decodeFuel_le _ _ _ (by omega) u hu]
            rfl
          unfold appNode
          rw [dif_pos hall]
          rfl

theorem decode_isSome (hv : γ.Valid) (j : ℕ) (hj : j < γ.nodes.length) :
    (γ.decode j).isSome := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (γ.decodeFuel_succ_isSome hv j hj)
  unfold decode
  rw [γ.decodeFuel_le _ _ _ (by omega) u hu]
  rfl

/-! ### Semantic objects of a valid instance -/

theorem k_pos (hv : γ.Valid) : 0 < γ.k := by
  have := (γ.valid_iff.mp hv).1
  omega

/-- The retained source `x` as an element of the source type. -/
def xv (hv : γ.Valid) : Fin γ.k := ⟨γ.x, (γ.valid_iff.mp hv).2.2.2.1⟩
/-- The retained source `y` as an element of the source type. -/
def yv (hv : γ.Valid) : Fin γ.k := ⟨γ.y, (γ.valid_iff.mp hv).2.2.2.2.1⟩

theorem xv_ne_yv (hv : γ.Valid) : γ.xv hv ≠ γ.yv hv := by
  intro h
  exact (γ.valid_iff.mp hv).2.2.2.2.2.1 (congrArg Fin.val h)

/-- A junk term used as the default of out-of-range decoding. -/
def junk (hv : γ.Valid) : γ.Tm := .var ⟨0, γ.k_pos hv⟩

/-- The term of node `j` (junk out of range or on failure). -/
def termD (hv : γ.Valid) (j : ℕ) : γ.Tm := (γ.decode j).getD (γ.junk hv)

theorem decode_eq_termD (hv : γ.Valid) (j : ℕ) (hj : j < γ.nodes.length) :
    γ.decode j = some (γ.termD hv j) := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (γ.decode_isSome hv j hj)
  simp [termD, hu]

/-- The output term `t`. -/
def outTerm (hv : γ.Valid) : γ.Tm := γ.termD hv γ.t
/-- The list of decoded tests. -/
def testTerms (hv : γ.Valid) : List (γ.Tm × γ.Tm) :=
  γ.tests.map (fun ij => (γ.termD hv ij.1, γ.termD hv ij.2))

/-- The actual shared-table maximum image size of the decoded instance on `Fin n`. -/
noncomputable def dispersion (hv : γ.Valid) (n : ℕ) : ℕ :=
  dispersionOn (A := Fin n) (γ.xv hv) (γ.yv hv) (γ.outTerm hv) (γ.testTerms hv)

/-- The first headline language: some alphabet reaches `n(n-1)`. -/
def Lower : Prop := ∃ hv : γ.Valid, ∃ n : ℕ, 2 ≤ n ∧ n * (n - 1) ≤ γ.dispersion hv n

/-- The second headline language: some alphabet reaches `n(n-1)+1`. -/
def Strict : Prop := ∃ hv : γ.Valid, ∃ n : ℕ, 2 ≤ n ∧ n * (n - 1) + 1 ≤ γ.dispersion hv n

/-! ### Decoding individual node shapes -/

theorem decode_src (hv : γ.Valid) (j i : ℕ) (hj : j < γ.nodes.length)
    (hnd : γ.nodes[j] = .src i) : ∃ hi : i < γ.k, γ.termD hv j = .var ⟨i, hi⟩ := by
  have hok := (γ.valid_iff.mp hv).2.2.2.2.2.2.1 j hj
  rw [hnd] at hok
  have hi := (γ.nodeOk_src j i).mp hok
  refine ⟨hi, ?_⟩
  have h1 : γ.decodeFuel (j + 1) j = some (.var ⟨i, hi⟩) := by
    rw [decodeFuel_succ, List.getElem?_eq_getElem hj, hnd]
    dsimp only
    rw [dif_pos hi]
  have h2 : γ.decode j = some (.var ⟨i, hi⟩) := γ.decodeFuel_le _ _ _ (by omega) _ h1
  simp [termD, h2]

theorem decode_app (hv : γ.Valid) (j f : ℕ) (args : List ℕ) (hj : j < γ.nodes.length)
    (hnd : γ.nodes[j] = .app f args) :
    ∃ hf : f < γ.m, args.length = γ.arity ⟨f, hf⟩ ∧ (∀ a ∈ args, a < j) ∧
      γ.termD hv j = .app ⟨f, hf⟩ (fun i => γ.termD hv (args.getD i.1 0)) := by
  have hok := (γ.valid_iff.mp hv).2.2.2.2.2.2.1 j hj
  rw [hnd] at hok
  obtain ⟨hf, hlen, hargs⟩ := (γ.nodeOk_app j f args).mp hok
  refine ⟨hf, hlen, hargs, ?_⟩
  have hchild : ∀ i : Fin (γ.arity ⟨f, hf⟩),
      γ.decodeFuel j (args.getD i.1 0) = some (γ.termD hv (args.getD i.1 0)) := by
    intro i
    have hi : i.1 < args.length := by
      have : i.1 < γ.arityOf f := i.2
      omega
    rw [List.getD_eq_getElem _ _ hi]
    have ha : args[i.1] < j := hargs _ (List.getElem_mem hi)
    have hlt : args[i.1] < γ.nodes.length := lt_trans ha hj
    have := γ.decode_eq_termD hv _ hlt
    unfold decode at this
    -- decode uses fuel nodes.length ≥ j; we need fuel j ≥ args[i]+1
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (γ.decodeFuel_succ_isSome hv _ hlt)
    have h1 : γ.decodeFuel j args[i.1] = some u := γ.decodeFuel_le _ _ _ (by omega) u hu
    have h2 : γ.decodeFuel γ.nodes.length args[i.1] = some u :=
      γ.decodeFuel_le _ _ _ (by omega) u hu
    rw [h2] at this
    rw [h1, Option.some.inj this]
  have h1 : γ.decodeFuel (j + 1) j =
      some (.app ⟨f, hf⟩ (fun i => γ.termD hv (args.getD i.1 0))) := by
    rw [decodeFuel_succ, List.getElem?_eq_getElem hj, hnd]
    dsimp only
    rw [dif_pos hf]
    exact (γ.appNode_eq_some_iff f hf _ _).mpr ⟨_, hchild, rfl⟩
  have h2 := γ.decodeFuel_le _ _ _ (by omega : j + 1 ≤ γ.nodes.length) _ h1
  simp [termD, decode, h2]

/-- The guard test `x ≠ y` is among the decoded tests. -/
theorem guard_mem_testTerms (hv : γ.Valid) :
    (.var (γ.xv hv), .var (γ.yv hv)) ∈ γ.testTerms hv := by
  have hg := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.2
  have htests := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  unfold guardOk at hg
  rw [List.any_eq_true] at hg
  obtain ⟨ij, hij, h⟩ := hg
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hb := htests ij hij
  rw [List.getD_eq_getElem _ _ hb.1] at h1
  rw [List.getD_eq_getElem _ _ hb.2] at h2
  obtain ⟨hx, hx'⟩ := γ.decode_src hv ij.1 γ.x hb.1 h1
  obtain ⟨hy, hy'⟩ := γ.decode_src hv ij.2 γ.y hb.2 h2
  unfold testTerms
  rw [List.mem_map]
  refine ⟨ij, hij, ?_⟩
  rw [hx', hy']
  rfl

/-! ### The executable evaluator -/

section Eval
variable {A : Type}

/-- One evaluation step: the value of node `j` from the values of earlier nodes. -/
def evalStep (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A)
    (vals : List A) (j : ℕ) : A :=
  match γ.nodes.getD j (.src 0) with
  | .src i => if h : i < γ.k then a ⟨i, h⟩ else d
  | .app f args =>
      if hf : f < γ.m then I ⟨f, hf⟩ (fun i => vals.getD (args.getD i.1 0) d) else d

/-- Linear-time evaluation of all nodes in topological order. -/
def evalNodes (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A) : List A :=
  buildList (γ.evalStep I a d) γ.nodes.length

theorem evalNodes_length (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A) :
    (γ.evalNodes I a d).length = γ.nodes.length := buildList_length _ _

theorem evalStep_eq_eval (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) :
    ∀ j, j < γ.nodes.length →
      γ.evalStep I a d (buildList (γ.evalStep I a d) j) j = (γ.termD hv j).eval I a := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      unfold evalStep
      rw [List.getD_eq_getElem _ _ hj]
      cases hnd : γ.nodes[j] with
      | src i =>
          obtain ⟨hi, ht⟩ := γ.decode_src hv j i hj hnd
          rw [ht]
          dsimp only
          rw [dif_pos hi]
          rfl
      | app f args =>
          obtain ⟨hf, hlen, hargs, ht⟩ := γ.decode_app hv j f args hj hnd
          rw [ht]
          dsimp only
          rw [dif_pos hf]
          simp only [Term.eval]
          congr 1
          funext i
          have hi : i.1 < args.length := by
            have : i.1 < γ.arityOf f := i.2
            omega
          rw [List.getD_eq_getElem _ _ hi]
          have ha : args[i.1] < j := hargs _ (List.getElem_mem hi)
          rw [buildList_getD _ _ _ ha]
          exact ih _ ha (lt_trans ha hj)

/-- The executable evaluator agrees with `Term.eval` on every node, for every
shared interpretation and every source assignment. -/
theorem evalNodes_getD (hv : γ.Valid) (I : Interpretation (Fin γ.m) γ.arity A)
    (a : Fin γ.k → A) (d : A) (j : ℕ) (hj : j < γ.nodes.length) :
    (γ.evalNodes I a d).getD j d = (γ.termD hv j).eval I a := by
  unfold evalNodes
  rw [buildList_getD _ _ _ hj]
  exact γ.evalStep_eq_eval hv I a d j hj

/-- Executable check that an assignment passes all tests. -/
def passesTests (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A)
    [DecidableEq A] : Bool :=
  let vals := γ.evalNodes I a d
  γ.tests.all (fun ij => decide (vals.getD ij.1 d ≠ vals.getD ij.2 d))

theorem passesTests_iff (hv : γ.Valid) [DecidableEq A]
    (I : Interpretation (Fin γ.m) γ.arity A) (a : Fin γ.k → A) (d : A) :
    γ.passesTests I a d = true ↔ DisequalityDispersion.Valid (γ.testTerms hv) I a := by
  have htests := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  unfold passesTests DisequalityDispersion.Valid testTerms
  simp only [List.all_eq_true, decide_eq_true_eq, List.forall_mem_map]
  constructor
  · intro h ij hij
    have hb := htests ij hij
    have := h ij hij
    rwa [γ.evalNodes_getD hv I a d _ hb.1, γ.evalNodes_getD hv I a d _ hb.2] at this
  · intro h ij hij
    have hb := htests ij hij
    rw [γ.evalNodes_getD hv I a d _ hb.1, γ.evalNodes_getD hv I a d _ hb.2]
    exact h ij hij

end Eval

/-! ### Occurrence flags: does a node use a source other than `x,y`? -/

def flagStep (flags : List Bool) (j : ℕ) : Bool :=
  match γ.nodes.getD j (.src 0) with
  | .src i => decide (i ≠ γ.x ∧ i ≠ γ.y)
  | .app _ args => args.any (fun a => flags.getD a false)

/-- `usesOther[j] = true` iff node `j` uses a source outside `{x,y}`. -/
def usesOther : List Bool := buildList γ.flagStep γ.nodes.length

theorem flagStep_iff (hv : γ.Valid) :
    ∀ j, j < γ.nodes.length →
      (γ.flagStep (buildList γ.flagStep j) j = true ↔
        ∃ z, (γ.termD hv j).Uses z ∧ z ≠ γ.xv hv ∧ z ≠ γ.yv hv) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      unfold flagStep
      rw [List.getD_eq_getElem _ _ hj]
      cases hnd : γ.nodes[j] with
      | src i =>
          obtain ⟨hi, ht⟩ := γ.decode_src hv j i hj hnd
          rw [ht]
          dsimp only
          simp only [decide_eq_true_eq, Term.Uses]
          constructor
          · rintro ⟨hx, hy⟩
            refine ⟨⟨i, hi⟩, rfl, ?_, ?_⟩
            · intro h; exact hx (congrArg Fin.val h)
            · intro h; exact hy (congrArg Fin.val h)
          · rintro ⟨z, rfl, hx, hy⟩
            exact ⟨fun h => hx (Fin.ext h), fun h => hy (Fin.ext h)⟩
      | app f args =>
          obtain ⟨hf, hlen, hargs, ht⟩ := γ.decode_app hv j f args hj hnd
          rw [ht]
          dsimp only
          simp only [List.any_eq_true, Term.Uses]
          constructor
          · rintro ⟨a, ha, hfl⟩
            obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp ha
            have hpj : args[p] < j := hargs _ ha
            rw [buildList_getD _ _ _ hpj] at hfl
            obtain ⟨z, hz, hx, hy⟩ := (ih _ hpj (lt_trans hpj hj)).mp hfl
            refine ⟨z, ⟨⟨p, by rw [← hlen]; exact hp⟩, ?_⟩, hx, hy⟩
            show (γ.termD hv (args.getD p 0)).Uses z
            rw [List.getD_eq_getElem _ _ hp]
            exact hz
          · rintro ⟨z, ⟨i, hz⟩, hx, hy⟩
            have hp : i.1 < args.length := by
              have : i.1 < γ.arityOf f := i.2
              omega
            refine ⟨args[i.1], List.getElem_mem hp, ?_⟩
            have hpj : args[i.1] < j := hargs _ (List.getElem_mem hp)
            rw [buildList_getD _ _ _ hpj]
            apply (ih _ hpj (lt_trans hpj hj)).mpr
            refine ⟨z, ?_, hx, hy⟩
            have hz' : (γ.termD hv (args.getD i.1 0)).Uses z := hz
            rwa [List.getD_eq_getElem _ _ hp] at hz'

theorem usesOther_getD (hv : γ.Valid) (j : ℕ) (hj : j < γ.nodes.length) :
    γ.usesOther.getD j false = true ↔
      ∃ z, (γ.termD hv j).Uses z ∧ z ≠ γ.xv hv ∧ z ≠ γ.yv hv := by
  unfold usesOther
  rw [buildList_getD _ _ _ hj]
  exact γ.flagStep_iff hv j hj

/-! ### Canonical identifiers -/

/-- Two application nodes decode to the same term iff they have the same symbol
and pointwise equal decoded children. -/
theorem app_term_eq_iff (hv : γ.Valid) (f g : ℕ) (hf : f < γ.m) (hg : g < γ.m)
    (args bs : List ℕ) (hlen : args.length = γ.arity ⟨f, hf⟩)
    (hlen' : bs.length = γ.arity ⟨g, hg⟩) :
    (Term.app (arity := γ.arity) ⟨f, hf⟩ (fun i => γ.termD hv (args.getD i.1 0)) =
        Term.app ⟨g, hg⟩ (fun i => γ.termD hv (bs.getD i.1 0))) ↔
      f = g ∧ args.map (γ.termD hv) = bs.map (γ.termD hv) := by
  constructor
  · intro h
    rw [Term.app.injEq] at h
    obtain ⟨hfg, hts⟩ := h
    have hfg' : f = g := congrArg Fin.val hfg
    subst hfg'
    refine ⟨rfl, ?_⟩
    have hts' := eq_of_heq hts
    apply List.ext_getElem
    · simp only [List.length_map]; rw [hlen, hlen']
    · intro p hp hp'
      have hp0 : p < args.length := by simpa using hp
      have hp0' : p < bs.length := by simpa using hp'
      have hp1 : p < γ.arity ⟨f, hf⟩ := by rw [← hlen]; exact hp0
      have := congrFun hts' ⟨p, hp1⟩
      simp only [List.getElem_map]
      dsimp only at this
      rw [List.getD_eq_getElem _ _ hp0, List.getD_eq_getElem _ _ hp0'] at this
      exact this
  · rintro ⟨rfl, hmap⟩
    congr 1
    funext i
    have hp : i.1 < args.length := by rw [hlen]; exact i.2
    have hp' : i.1 < bs.length := by rw [hlen']; exact i.2
    rw [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hp']
    have := congrArg (fun l => l[i.1]?) hmap
    simp only [List.getElem?_map, List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hp',
      Option.map_some] at this
    exact Option.some.inj this

open Classical in
/-- The canonical representative of node `j`: the least index carrying the same term. -/
noncomputable def rep (hv : γ.Valid) (j : ℕ) : ℕ :=
  Nat.find (⟨j, le_refl j, rfl⟩ : ∃ i, i ≤ j ∧ γ.termD hv i = γ.termD hv j)

open Classical in
theorem rep_spec (hv : γ.Valid) (j : ℕ) :
    γ.rep hv j ≤ j ∧ γ.termD hv (γ.rep hv j) = γ.termD hv j :=
  Nat.find_spec (⟨j, le_refl j, rfl⟩ : ∃ i, i ≤ j ∧ γ.termD hv i = γ.termD hv j)

open Classical in
theorem rep_min (hv : γ.Valid) (j i : ℕ) (hi : i ≤ j) (h : γ.termD hv i = γ.termD hv j) :
    γ.rep hv j ≤ i :=
  Nat.find_min' (⟨j, le_refl j, rfl⟩ : ∃ i, i ≤ j ∧ γ.termD hv i = γ.termD hv j) ⟨hi, h⟩

theorem rep_eq_iff (hv : γ.Valid) (i j : ℕ) :
    γ.rep hv i = γ.rep hv j ↔ γ.termD hv i = γ.termD hv j := by
  constructor
  · intro h
    rw [← (γ.rep_spec hv i).2, h, (γ.rep_spec hv j).2]
  · intro h
    rcases le_total i j with hij | hij
    · have h1 : γ.rep hv j ≤ i := γ.rep_min hv j i hij h
      have h2 : γ.rep hv i ≤ γ.rep hv j :=
        γ.rep_min hv i _ h1 ((γ.rep_spec hv j).2.trans h.symm)
      have h3 : γ.rep hv j ≤ γ.rep hv i :=
        γ.rep_min hv j _ (le_trans (γ.rep_spec hv i).1 hij) ((γ.rep_spec hv i).2.trans h)
      exact le_antisymm h2 h3
    · have h1 : γ.rep hv i ≤ j := γ.rep_min hv i j hij h.symm
      have h2 : γ.rep hv j ≤ γ.rep hv i :=
        γ.rep_min hv j _ h1 ((γ.rep_spec hv i).2.trans h)
      have h3 : γ.rep hv i ≤ γ.rep hv j :=
        γ.rep_min hv i _ (le_trans (γ.rep_spec hv j).1 hij) ((γ.rep_spec hv j).2.trans h.symm)
      exact le_antisymm h3 h2

theorem rep_le (hv : γ.Valid) (j : ℕ) : γ.rep hv j ≤ j := (γ.rep_spec hv j).1

theorem rep_rep (hv : γ.Valid) (j : ℕ) : γ.rep hv (γ.rep hv j) = γ.rep hv j :=
  (γ.rep_eq_iff hv _ _).mpr (γ.rep_spec hv j).2

theorem map_rep_eq_iff (hv : γ.Valid) (l l' : List ℕ) :
    l.map (γ.rep hv) = l'.map (γ.rep hv) ↔ l.map (γ.termD hv) = l'.map (γ.termD hv) := by
  constructor
  · intro h
    have h1 : l.map (γ.termD hv) = (l.map (γ.rep hv)).map (γ.termD hv) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a _
      exact ((γ.rep_spec hv a).2).symm
    have h2 : l'.map (γ.termD hv) = (l'.map (γ.rep hv)).map (γ.termD hv) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a _
      exact ((γ.rep_spec hv a).2).symm
    rw [h1, h2, h]
  · intro h
    have hlen : l.length = l'.length := by
      have := congrArg List.length h
      simpa using this
    apply List.ext_getElem
    · simp [hlen]
    · intro p hp hp'
      have hp0 : p < l.length := by simpa using hp
      have hp0' : p < l'.length := by simpa using hp'
      simp only [List.getElem_map]
      apply (γ.rep_eq_iff hv _ _).mpr
      have := congrArg (fun m => m[p]?) h
      simp only [List.getElem?_map, List.getElem?_eq_getElem hp0, List.getElem?_eq_getElem hp0',
        Option.map_some] at this
      exact Option.some.inj this

/-- Signature of a node with children replaced by their identifiers. -/
def sigWith (ids : List ℕ) : Node → Node
  | .src i => .src i
  | .app f args => .app f (args.map (fun a => ids.getD a 0))

/-- Signature equality is term equality, provided identifiers are correct below `j`. -/
theorem sig_eq_iff (hv : γ.Valid) (ids : List ℕ) (j : ℕ) (hj : j < γ.nodes.length)
    (hids : ∀ a, a < j → ids.getD a 0 = γ.rep hv a)
    (i i' : ℕ) (hi : i ≤ j) (hi' : i' ≤ j) :
    sigWith ids (γ.nodes[i]'(lt_of_le_of_lt hi hj)) =
        sigWith ids (γ.nodes[i']'(lt_of_le_of_lt hi' hj)) ↔
      γ.termD hv i = γ.termD hv i' := by
  have hil : i < γ.nodes.length := lt_of_le_of_lt hi hj
  have hil' : i' < γ.nodes.length := lt_of_le_of_lt hi' hj
  cases hnd : γ.nodes[i] with
  | src a =>
      obtain ⟨ha, hta⟩ := γ.decode_src hv i a hil hnd
      cases hnd' : γ.nodes[i'] with
      | src b =>
          obtain ⟨hb, htb⟩ := γ.decode_src hv i' b hil' hnd'
          rw [hta, htb]
          simp [sigWith, Fin.ext_iff]
      | app g bs =>
          obtain ⟨hg, _, _, htb⟩ := γ.decode_app hv i' g bs hil' hnd'
          rw [hta, htb]
          simp [sigWith]
  | app f args =>
      obtain ⟨hf, hlen, hargs, hta⟩ := γ.decode_app hv i f args hil hnd
      cases hnd' : γ.nodes[i'] with
      | src b =>
          obtain ⟨hb, htb⟩ := γ.decode_src hv i' b hil' hnd'
          rw [hta, htb]
          simp [sigWith]
      | app g bs =>
          obtain ⟨hg, hlen', hargs', htb⟩ := γ.decode_app hv i' g bs hil' hnd'
          rw [hta, htb, γ.app_term_eq_iff hv f g hf hg args bs hlen hlen']
          simp only [sigWith, Node.app.injEq]
          apply and_congr_right
          intro _
          have e1 : args.map (fun a => ids.getD a 0) = args.map (γ.rep hv) := by
            apply List.map_congr_left
            intro a ha
            exact hids a (lt_of_lt_of_le (hargs a ha) hi)
          have e2 : bs.map (fun a => ids.getD a 0) = bs.map (γ.rep hv) := by
            apply List.map_congr_left
            intro a ha
            exact hids a (lt_of_lt_of_le (hargs' a ha) hi')
          rw [e1, e2]
          exact γ.map_rep_eq_iff hv args bs

/-- The least `i < n` with `p i`, or `n` if there is none. -/
def firstIndex (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      let r := firstIndex p n
      if r < n then r else if p n then n else n + 1

theorem firstIndex_spec (p : ℕ → Bool) (n : ℕ) :
    (firstIndex p n < n ∧ p (firstIndex p n) = true ∧
        ∀ i, i < firstIndex p n → p i = false) ∨
      (firstIndex p n = n ∧ ∀ i, i < n → p i = false) := by
  induction n with
  | zero => right; exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
      simp only [firstIndex]
      rcases ih with ⟨hlt, hp, hmin⟩ | ⟨heq, hnone⟩
      · rw [if_pos hlt]
        left
        exact ⟨lt_trans hlt (Nat.lt_succ_self n), hp, hmin⟩
      · rw [heq, if_neg (lt_irrefl n)]
        by_cases hpn : p n = true
        · rw [if_pos hpn]
          left
          exact ⟨Nat.lt_succ_self n, hpn, hnone⟩
        · rw [if_neg hpn]
          right
          refine ⟨rfl, fun i hi => ?_⟩
          rcases Nat.lt_or_ge i n with h | h
          · exact hnone i h
          · have : i = n := by omega
            subst this
            exact Bool.eq_false_iff.mpr hpn

theorem firstIndex_le (p : ℕ → Bool) (n : ℕ) : firstIndex p n ≤ n := by
  rcases firstIndex_spec p n with ⟨h, _, _⟩ | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- Identifier assignment for node `j`, given the identifiers of earlier nodes. -/
def canonStep (ids : List ℕ) (j : ℕ) : ℕ :=
  let sg := sigWith ids (γ.nodes.getD j (.src 0))
  let r := firstIndex (fun i => decide (sigWith ids (γ.nodes.getD i (.src 0)) = sg)) j
  if r < j then ids.getD r 0 else j

/-- Canonical identifiers: two nodes get the same identifier iff they decode to
the same term (`canonIds_eq_iff`). -/
def canonIds : List ℕ := buildList γ.canonStep γ.nodes.length

theorem canonStep_eq_rep (hv : γ.Valid) (j : ℕ) (hj : j < γ.nodes.length) (ids : List ℕ)
    (hids : ∀ a, a < j → ids.getD a 0 = γ.rep hv a) :
    γ.canonStep ids j = γ.rep hv j := by
  unfold canonStep
  dsimp only
  set p : ℕ → Bool := fun i => decide (sigWith ids (γ.nodes.getD i (.src 0)) =
    sigWith ids (γ.nodes.getD j (.src 0))) with hp
  have hp_iff : ∀ i, i < j → (p i = true ↔ γ.termD hv i = γ.termD hv j) := by
    intro i hi
    rw [hp]
    simp only [decide_eq_true_eq]
    rw [List.getD_eq_getElem _ _ (lt_trans hi hj), List.getD_eq_getElem _ _ hj]
    exact γ.sig_eq_iff hv ids j hj hids i j (le_of_lt hi) (le_refl j)
  rcases firstIndex_spec p j with ⟨hlt, hpr, hmin⟩ | ⟨heq, hnone⟩
  · rw [if_pos hlt]
    have h1 : γ.termD hv (firstIndex p j) = γ.termD hv j := (hp_iff _ hlt).mp hpr
    have hrep : γ.rep hv j = firstIndex p j := by
      apply le_antisymm
      · exact γ.rep_min hv j _ (le_of_lt hlt) h1
      · by_contra hcon
        push_neg at hcon
        have hrj : γ.rep hv j < j := lt_trans hcon hlt
        have := hmin _ hcon
        have h2 := (hp_iff _ hrj).mpr (γ.rep_spec hv j).2
        rw [this] at h2
        exact Bool.false_ne_true h2
    rw [hids _ hlt, ← hrep, γ.rep_rep]
  · rw [heq, if_neg (lt_irrefl j)]
    symm
    apply le_antisymm (γ.rep_le hv j)
    by_contra hcon
    push_neg at hcon
    have := hnone _ hcon
    have h2 := (hp_iff _ hcon).mpr (γ.rep_spec hv j).2
    rw [this] at h2
    exact Bool.false_ne_true h2

theorem canonIds_getD (hv : γ.Valid) (j : ℕ) (hj : j < γ.nodes.length) :
    γ.canonIds.getD j 0 = γ.rep hv j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      have hstep : ∀ a, a < j → (buildList γ.canonStep j).getD a 0 = γ.rep hv a := by
        intro a ha
        rw [buildList_getD γ.canonStep j a ha,
          ← buildList_getD γ.canonStep γ.nodes.length a (lt_trans ha hj) 0]
        exact ih a ha (lt_trans ha hj)
      unfold canonIds
      rw [buildList_getD _ _ _ hj]
      exact γ.canonStep_eq_rep hv j hj _ hstep

/-- Canonical identifiers agree exactly when the decoded terms agree. -/
theorem canonIds_eq_iff (hv : γ.Valid) (i j : ℕ) (hi : i < γ.nodes.length)
    (hj : j < γ.nodes.length) :
    γ.canonIds.getD i 0 = γ.canonIds.getD j 0 ↔ γ.termD hv i = γ.termD hv j := by
  rw [γ.canonIds_getD hv i hi, γ.canonIds_getD hv j hj]
  exact γ.rep_eq_iff hv i j

theorem canonIds_length : γ.canonIds.length = γ.nodes.length := buildList_length _ _


/-! ### Support count -/

open Classical in
/-- Every subterm of a decoded node is itself a decoded node. -/
theorem support_termD_subset (hv : γ.Valid) (j : ℕ) (hj : j < γ.nodes.length) :
    (γ.termD hv j).support ⊆
      (List.range γ.nodes.length).toFinset.image (γ.termD hv) := by
  classical
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      have hself : γ.termD hv j ∈ (List.range γ.nodes.length).toFinset.image (γ.termD hv) :=
        Finset.mem_image.mpr ⟨j, by simp [hj], rfl⟩
      cases hnd : γ.nodes[j] with
      | src a =>
          obtain ⟨ha, hta⟩ := γ.decode_src hv j a hj hnd
          intro u hu
          rw [hta] at hu
          simp only [Term.support, Finset.mem_singleton] at hu
          rw [hu, ← hta]
          exact hself
      | app f args =>
          obtain ⟨hf, hlen, hargs, hta⟩ := γ.decode_app hv j f args hj hnd
          intro u hu
          rw [hta] at hu
          simp only [Term.support, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
            true_and] at hu
          rcases hu with hu | ⟨i, hi⟩
          · rw [hu, ← hta]
            exact hself
          · have hmem : args.getD i.1 0 ∈ args := by
              have hi' : i.1 < args.length := by
                have := i.2
                rw [hlen]
                exact this
              rw [List.getD_eq_getElem _ _ hi']
              exact List.getElem_mem hi'
            have hlt : args.getD i.1 0 < j := hargs _ hmem
            exact ih _ hlt (lt_trans hlt hj) hi

open Classical in
theorem instanceSupport_subset (hv : γ.Valid) :
    instanceSupport (γ.outTerm hv) (γ.testTerms hv) ⊆
      Finset.univ.image Term.var ∪
        (List.range γ.nodes.length).toFinset.image (γ.termD hv) := by
  classical
  have ht := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.1
  have htests := (γ.valid_iff.mp hv).2.2.2.2.2.2.2.2.1
  intro u hu
  unfold instanceSupport at hu
  simp only [Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset] at hu
  rcases hu with (hu | hu) | ⟨uv, huv, hu⟩
  · exact Finset.mem_union_left _ hu
  · exact Finset.mem_union_right _ (γ.support_termD_subset hv γ.t ht hu)
  · unfold testTerms at huv
    rw [List.mem_map] at huv
    obtain ⟨ij, hij, rfl⟩ := huv
    obtain ⟨h1, h2⟩ := htests ij hij
    rcases hu with hu | hu
    · exact Finset.mem_union_right _ (γ.support_termD_subset hv ij.1 h1 hu)
    · exact Finset.mem_union_right _ (γ.support_termD_subset hv ij.2 h2 hu)

open Classical in
/-- The support of a decoded instance has at most `k + |nodes|` terms. -/
theorem instanceSupport_card_le (hv : γ.Valid) :
    (instanceSupport (γ.outTerm hv) (γ.testTerms hv)).card ≤ γ.k + γ.nodes.length := by
  classical
  refine (Finset.card_le_card (γ.instanceSupport_subset hv)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  apply Nat.add_le_add
  · refine Finset.card_image_le.trans ?_
    simp [k]
  · refine Finset.card_image_le.trans ?_
    refine (List.toFinset_card_le _).trans ?_
    simp

end Instance
end Encoded
end DisequalityDispersion
