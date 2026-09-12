import FlowCost
import UnitFlowExec
import ParsingExec
import PhaseAExec

/-! # Execution-linked cost of the polynomial-time decision: an instrumented program

The executable definitions of `FlowCut.lean` (the split network, `rhoFlowL`, `strictDecideP`)
are re-implemented as instrumented programs in the step-counting monad `Costed`
(`CostMonad.lean`), with exactly the primitives and charges declared in `FlowCost.lean`:
`tick 1` per list cell examined, produced or copied (range, map, filter, flatten, append,
cons, measuring a length), `tick (accessC l j)` per table access `l.getD j _`,
`tick (natC v)` per label copied, shifted or compared, and the full-scan deduplication
`dedupM` (each entry is scanned for in the deduplicated remainder).  Closures re-evaluate
their bodies at every call (no sharing): `reps` is recomputed by `nodeArcs` and twice by
`netNodes`, `netS`/`netT` are re-formed inside every closure that mentions them, and the
identifier of node `j` is re-read for every argument of `j`.

The Phase-A procedures are instrumented as well: `isValid` (base instance) and `canonIds` in
`PhaseAExec.lean` (`isValidM`, `Instance.canonIdsM`, with step counts exactly the fully charged
costs `isValidC'`, `canonIdsC'` of `FlowCost.lean`), and the test scan `testsDistinct` here
(`testsDistinctM`).

For every definition `X` the theorems `XM_val` and `XM_cost` prove that the instrumented
program computes the executable definition and that its step count is the cost function;
`strictDecidePM_spec` combines them for the decision procedure and `strictDecidePM_steps`
bounds the step count by `91000·S⁶ + 3·natC k`.  `decideBitsM` composes the instrumented
parser (`ParsingExec.lean`) with the instrumented decision and `decideBitsM_steps` bounds its
step count on *every* bit string by `92000·(|bs|+1)⁶`. -/

namespace DisequalityDispersion.Encoded
namespace GInstance

open Flow DisequalityDispersion.Costed

variable (g : GInstance)

/-! ### Charged primitives -/

/-- Reading a table entry `l.getD j 0`, charged `accessC l j`. -/
def getDM (l : List ℕ) (j : ℕ) : Costed ℕ := do
  tick (accessC l j); Pure.pure (l.getD j 0)

@[simp] theorem getDM_val (l : List ℕ) (j : ℕ) : (getDM l j).val = l.getD j 0 := rfl
@[simp] theorem getDM_cost (l : List ℕ) (j : ℕ) : (getDM l j).cost = accessC l j := by
  simp [getDM]

/-- Reading node `j` (default `src 0`), charged `accessC nodes j`. -/
def getNodeM (j : ℕ) : Costed Node := do
  tick (accessC g.base.nodes j); Pure.pure (g.base.nodes.getD j (.src 0))

@[simp] theorem getNodeM_val (j : ℕ) : (g.getNodeM j).val = g.base.nodes.getD j (.src 0) := rfl
@[simp] theorem getNodeM_cost (j : ℕ) : (g.getNodeM j).cost = accessC g.base.nodes j := by
  simp [getNodeM]

/-- Forming `netS`: measure `nodes.length` and shift. -/
def netSM : Costed ℕ := do tick g.netSC; Pure.pure g.netS
/-- Forming `netT`. -/
def netTM : Costed ℕ := do tick g.netSC; Pure.pure g.netT

@[simp] theorem netSM_val : g.netSM.val = g.netS := rfl
@[simp] theorem netSM_cost : g.netSM.cost = g.netSC := by simp [netSM]
@[simp] theorem netTM_val : g.netTM.val = g.netT := rfl
@[simp] theorem netTM_cost : g.netTM.cost = g.netSC := by simp [netTM]

/-- Building `range nodes.length` (measure the length, produce the cells). -/
def rangeM : Costed (List ℕ) := do tick g.rangeC; Pure.pure (List.range g.base.nodes.length)

@[simp] theorem rangeM_val : g.rangeM.val = List.range g.base.nodes.length := rfl
@[simp] theorem rangeM_cost : g.rangeM.cost = g.rangeC := by simp [rangeM]

/-- The arguments of node `j`. -/
def argsOfM (j : ℕ) : Costed (List ℕ) := do
  let nd ← g.getNodeM j
  Pure.pure (match nd with | .src _ => [] | .app _ args => args)

@[simp] theorem argsOfM_val (j : ℕ) : (g.argsOfM j).val = g.argsOf j := rfl
@[simp] theorem argsOfM_cost (j : ℕ) : (g.argsOfM j).cost = accessC g.base.nodes j := by
  simp [argsOfM]

/-- The source test of node `j`. -/
def isSrcNodeM (j : ℕ) : Costed Bool := do
  let nd ← g.getNodeM j
  Pure.pure (match nd with | .src _ => true | .app _ _ => false)

@[simp] theorem isSrcNodeM_val (j : ℕ) : (g.isSrcNodeM j).val = g.isSrcNode j := rfl
@[simp] theorem isSrcNodeM_cost (j : ℕ) : (g.isSrcNodeM j).cost = accessC g.base.nodes j := by
  simp [isSrcNodeM]

/-- Full-scan deduplication: each entry is scanned for in the deduplicated remainder. -/
def dedupM : List (ℕ × ℕ) → Costed (List (ℕ × ℕ))
  | [] => Pure.pure []
  | x :: l => do
      tick 1
      let d ← dedupM l
      let b ← Network.memM natC d x
      Pure.pure (if b then d else x :: d)

theorem dedupM_val : ∀ (l : List (ℕ × ℕ)), (dedupM l).val = dedupList l
  | [] => rfl
  | x :: l => by
      simp only [dedupM, dedupList, bind_val, pure_val, Network.memM_val, dedupM_val l]
      by_cases h : x ∈ dedupList l <;> simp [h]

theorem dedupM_cost : ∀ (l : List (ℕ × ℕ)), (dedupM l).cost = dedupC l
  | [] => rfl
  | x :: l => by
      simp only [dedupM, dedupC, bind_cost, tick_cost, pure_cost, Network.memM_cost, dedupM_val,
        dedupM_cost l]
      omega

/-- Full-scan `nodes.idxOf nd` (every node is compared with `nd`). -/
def idxOfAuxM (nd : Node) : List Node → Costed ℕ
  | [] => Pure.pure 0
  | nd' :: l => do
      tick (1 + nodeC nd + nodeC nd')
      let r ← idxOfAuxM nd l
      Pure.pure (bif nd' == nd then 0 else r + 1)

theorem idxOfAuxM_val (nd : Node) : ∀ (l : List Node), (idxOfAuxM nd l).val = l.idxOf nd
  | [] => rfl
  | nd' :: l => by
      simp only [idxOfAuxM, bind_val, pure_val, List.idxOf_cons, idxOfAuxM_val nd l]

theorem idxOfAuxM_cost (nd : Node) : ∀ (l : List Node),
    (idxOfAuxM nd l).cost = (l.map (fun nd' => 1 + nodeC nd + nodeC nd')).sum
  | [] => rfl
  | nd' :: l => by
      simp only [idxOfAuxM, bind_cost, tick_cost, pure_cost, idxOfAuxM_cost nd l, List.map_cons,
        List.sum_cons, add_zero]

def idxOfM (nd : Node) : Costed ℕ := idxOfAuxM nd g.base.nodes

@[simp] theorem idxOfM_val (nd : Node) : (g.idxOfM nd).val = g.base.nodes.idxOf nd :=
  idxOfAuxM_val nd _
@[simp] theorem idxOfM_cost (nd : Node) : (g.idxOfM nd).cost = g.idxOfC nd :=
  idxOfAuxM_cost nd _

/-! ### Phase-A procedures (instrumented in `PhaseAExec.lean`) -/

/-- The instrumented validity check of the base instance (`PhaseAExec.isValidM`). -/
def isValidBaseM : Costed Bool := g.base.isValidM
/-- The instrumented identifier table (`PhaseAExec.canonIdsM`). -/
def canonIdsM : Costed (List ℕ) := g.base.canonIdsM

@[simp] theorem isValidBaseM_val : g.isValidBaseM.val = g.base.isValid := g.base.isValidM_val
@[simp] theorem isValidBaseM_cost : g.isValidBaseM.cost = g.base.isValidC' := g.base.isValidM_cost
@[simp] theorem canonIdsM_val : g.canonIdsM.val = g.base.canonIds := g.base.canonIdsM_val
@[simp] theorem canonIdsM_cost : g.canonIdsM.cost = g.base.canonIdsC' := g.base.canonIdsM_cost

/-- `testsDistinct ids`: every test is scanned, both identifiers looked up and compared. -/
def testsDistinctM (ids : List ℕ) : Costed Bool :=
  allM 1 (fun ij => do
    let a ← getDM ids ij.1
    let b ← getDM ids ij.2
    tick (natC a + natC b)
    Pure.pure (!(a == b))) g.base.tests

theorem testsDistinctM_val (ids : List ℕ) :
    (g.testsDistinctM ids).val = g.base.testsDistinct ids := by
  unfold testsDistinctM Instance.testsDistinct
  rw [allM_val 1 _ (fun ij => !(ids.getD ij.1 0 == ids.getD ij.2 0)) (fun ij => rfl)]

theorem testsDistinctM_cost (ids : List ℕ) :
    (g.testsDistinctM ids).cost = g.base.testsDistinctC ids := by
  unfold testsDistinctM Instance.testsDistinctC
  rw [allM_cost 1 _ (fun ij => accessC ids ij.1 + (accessC ids ij.2 +
    (natC (ids.getD ij.1 0) + natC (ids.getD ij.2 0)))) (fun ij => by simp)]
  simp only [Nat.add_assoc]

/-! ### The instrumented constructions -/

/-- `isValid`: the base check, then every extra output index compared with `nodes.length`
(measured again inside the closure); `&&` evaluates both operands. -/
def isValidGM : Costed Bool := do
  let b ← g.isValidBaseM
  let c ← allM 1 (fun o => do
      tick g.base.nodes.length
      tick (natC o + natC g.base.nodes.length)
      Pure.pure (decide (o < g.base.nodes.length))) g.outs
  Pure.pure (b && c)

theorem isValidGM_val : g.isValidGM.val = g.isValid := by
  simp only [isValidGM, isValid, bind_val, pure_val, isValidBaseM_val]
  rw [allM_val 1 _ (fun o => decide (o < g.base.nodes.length)) (fun o => rfl)]

theorem isValidGM_cost : g.isValidGM.cost = g.isValidGC := by
  simp only [isValidGM, isValidGC, bind_cost, pure_cost, isValidBaseM_cost]
  rw [allM_cost 1 _ (fun o => g.base.nodes.length + (natC o + natC g.base.nodes.length))
    (fun o => by simp)]
  simp only [Nat.add_assoc, add_zero]

/-- `repsL ids`: the range, then each index read, its identifier accessed and compared. -/
def repsM (ids : List ℕ) : Costed (List ℕ) := do
  let rg ← g.rangeM
  filterM 1 (fun j => do
      let i ← getDM ids j
      tick (natC i + natC j)
      Pure.pure (i == j)) rg

theorem repsM_val (ids : List ℕ) : (g.repsM ids).val = g.repsL ids := by
  simp only [repsM, repsL, bind_val, rangeM_val]
  rw [filterM_val 1 _ (fun j => ids.getD j 0 == j) (fun j => rfl)]

theorem repsM_cost (ids : List ℕ) : (g.repsM ids).cost = g.repsCL ids := by
  simp only [repsM, repsCL, bind_cost, rangeM_cost, rangeM_val]
  rw [filterM_cost 1 _ (fun j => accessC ids j + (natC (ids.getD j 0) + natC j)) (fun j => by simp)]
  simp only [Nat.add_assoc]

/-- `nodeArcsL ids`: `reps` recomputed, then a pair of shifted labels per representative. -/
def nodeArcsM (ids : List ℕ) : Costed (List (ℕ × ℕ)) := do
  let rs ← g.repsM ids
  mapM 1 (fun r => do tick (2 * natC r); Pure.pure (2 * r, 2 * r + 1)) rs

theorem nodeArcsM_val (ids : List ℕ) : (g.nodeArcsM ids).val = g.nodeArcsL ids := by
  simp only [nodeArcsM, nodeArcsL, bind_val, repsM_val]
  rw [mapM_val 1 _ (fun r => (2 * r, 2 * r + 1)) (fun r => rfl)]

theorem nodeArcsM_cost (ids : List ℕ) : (g.nodeArcsM ids).cost = g.nodeArcsCL ids := by
  simp only [nodeArcsM, nodeArcsCL, bind_cost, repsM_cost, repsM_val]
  rw [mapM_cost 1 _ (fun r => 2 * natC r) (fun r => by simp)]

/-- `netNodesL ids`: `reps` computed twice, each map shifts its labels, the two appends copy
their left operands, `netS`/`netT` are formed and consed. -/
def netNodesM (ids : List ℕ) : Costed (List ℕ) := do
  let rs₁ ← g.repsM ids
  let l₁ ← mapM 1 (fun r => do tick (natC r); Pure.pure (2 * r)) rs₁
  let rs₂ ← g.repsM ids
  let l₂ ← mapM 1 (fun r => do tick (natC r); Pure.pure (2 * r + 1)) rs₂
  tick l₁.length
  let l₁₂ := l₁ ++ l₂
  let s ← g.netSM
  let t ← g.netTM
  tick 2
  tick l₁₂.length
  Pure.pure (l₁₂ ++ [s, t])

theorem netNodesM_val (ids : List ℕ) : (g.netNodesM ids).val = g.netNodesL ids := by
  simp only [netNodesM, netNodesL, bind_val, pure_val, repsM_val, netSM_val, netTM_val]
  rw [mapM_val 1 _ (fun r => 2 * r) (fun r => rfl), mapM_val 1 _ (fun r => 2 * r + 1) (fun r => rfl)]

theorem netNodesM_cost (ids : List ℕ) : (g.netNodesM ids).cost = g.netNodesCL ids := by
  simp only [netNodesM, netNodesCL, bind_cost, pure_cost, tick_cost, repsM_cost, repsM_val,
    netSM_cost, netTM_cost, netSM_val, netTM_val]
  rw [mapM_val 1 _ (fun r => 2 * r) (fun r => rfl), mapM_val 1 _ (fun r => 2 * r + 1) (fun r => rfl),
    mapM_cost 1 _ (fun r => natC r) (fun r => by simp), mapM_cost 1 _ (fun r => natC r) (fun r => by simp)]
  simp only [List.length_append, List.length_map]
  omega

/-- `edgeArcsL ids`: the range; each node read; for each argument both identifiers looked up
(the node's own identifier re-read inside the inner closure) and shifted; the per-node lists
flattened; then deduplication. -/
def edgeArcsM (ids : List ℕ) : Costed (List (ℕ × ℕ)) := do
  let rg ← g.rangeM
  let ls ← mapM 1 (fun j => do
      let as ← g.argsOfM j
      mapM 1 (fun a => do
        let ia ← getDM ids a
        tick (natC ia)
        let ij ← getDM ids j
        tick (natC ij)
        Pure.pure (2 * ia + 1, 2 * ij)) as) rg
  tick (ls.flatten.length + ls.length)
  dedupM ls.flatten

theorem edgeArcsM_val (ids : List ℕ) : (g.edgeArcsM ids).val = g.edgeArcsL ids := by
  simp only [edgeArcsM, edgeArcsL, bind_val, rangeM_val, dedupM_val, List.flatMap_def]
  rw [mapM_val 1 _ (fun j => (g.argsOf j).map (fun a => (2 * ids.getD a 0 + 1, 2 * ids.getD j 0)))
    (fun j => by
      simp only [bind_val, argsOfM_val]
      rw [mapM_val 1 _ (fun a => (2 * ids.getD a 0 + 1, 2 * ids.getD j 0)) (fun a => rfl)])]

theorem edgeArcsM_cost (ids : List ℕ) : (g.edgeArcsM ids).cost = g.edgeArcsCL ids := by
  simp only [edgeArcsM, edgeArcsCL, edgeRawL, bind_cost, tick_cost,
    rangeM_cost, rangeM_val, dedupM_cost, List.flatMap_def]
  rw [mapM_val 1 _ (fun j => (g.argsOf j).map (fun a => (2 * ids.getD a 0 + 1, 2 * ids.getD j 0)))
    (fun j => by
      simp only [bind_val, argsOfM_val]
      rw [mapM_val 1 _ (fun a => (2 * ids.getD a 0 + 1, 2 * ids.getD j 0)) (fun a => rfl)])]
  rw [mapM_cost 1 _ (fun j => accessC g.base.nodes j +
      ((g.argsOf j).map (fun a => 1 + (accessC ids a + (natC (ids.getD a 0) +
        (accessC ids j + natC (ids.getD j 0)))))).sum)
    (fun j => by
      simp only [bind_cost, argsOfM_cost, argsOfM_val]
      rw [mapM_cost 1 _ (fun a => accessC ids a + (natC (ids.getD a 0) +
        (accessC ids j + natC (ids.getD j 0)))) (fun a => by simp)])]
  simp only [List.length_map, List.length_range, Nat.add_assoc]

/-- `srcArcsL ids`: the range; each node read for the source test; for each kept node `netS`
is formed inside the closure and the identifier looked up and shifted; then deduplication. -/
def srcArcsM (ids : List ℕ) : Costed (List (ℕ × ℕ)) := do
  let rg ← g.rangeM
  let kept ← filterM 1 (fun j => g.isSrcNodeM j) rg
  let raw ← mapM 1 (fun j => do
      let s ← g.netSM
      let ij ← getDM ids j
      tick (natC ij)
      Pure.pure (s, 2 * ij)) kept
  dedupM raw

theorem srcArcsM_val (ids : List ℕ) : (g.srcArcsM ids).val = g.srcArcsL ids := by
  simp only [srcArcsM, srcArcsL, bind_val, rangeM_val, dedupM_val]
  rw [filterM_val 1 _ g.isSrcNode (fun j => rfl),
    mapM_val 1 _ (fun j => (g.netS, 2 * ids.getD j 0)) (fun j => rfl)]

theorem srcArcsM_cost (ids : List ℕ) : (g.srcArcsM ids).cost = g.srcArcsCL ids := by
  simp only [srcArcsM, srcArcsCL, srcRawL, bind_cost, rangeM_cost,
    rangeM_val, dedupM_cost]
  rw [filterM_val 1 _ g.isSrcNode (fun j => rfl),
    mapM_val 1 _ (fun j => (g.netS, 2 * ids.getD j 0)) (fun j => rfl),
    filterM_cost 1 _ (fun j => accessC g.base.nodes j) (fun j => by simp),
    mapM_cost 1 _ (fun j => g.netSC + (accessC ids j + natC (ids.getD j 0))) (fun j => by simp)]
  simp only [Nat.add_assoc]

/-- `snkArcsL ids`: the two `idxOf` scans (each building a `src` node), the append, then per
output node the identifier lookup, the shift and `netT` inside the closure; then deduplication. -/
def snkArcsM (ids : List ℕ) : Costed (List (ℕ × ℕ)) := do
  tick (natC g.base.x)
  let xn ← g.idxOfM (.src g.base.x)
  tick (natC g.base.y)
  let yn ← g.idxOfM (.src g.base.y)
  tick 2
  let raw ← mapM 1 (fun j => do
      let ij ← getDM ids j
      tick (natC ij)
      let t ← g.netTM
      Pure.pure (2 * ij + 1, t)) ([xn, yn] ++ g.outs)
  dedupM raw

theorem snkArcsM_val (ids : List ℕ) : (g.snkArcsM ids).val = g.snkArcsL ids := by
  simp only [snkArcsM, snkArcsL, outNodes, xNode, yNode, bind_val, idxOfM_val, dedupM_val]
  rw [mapM_val 1 _ (fun j => (2 * ids.getD j 0 + 1, g.netT)) (fun j => rfl)]

theorem snkArcsM_cost (ids : List ℕ) : (g.snkArcsM ids).cost = g.snkArcsCL ids := by
  simp only [snkArcsM, snkArcsCL, snkRawL, outNodes, xNode, yNode, bind_cost,
    tick_cost, idxOfM_val, idxOfM_cost, dedupM_cost]
  rw [mapM_val 1 _ (fun j => (2 * ids.getD j 0 + 1, g.netT)) (fun j => rfl),
    mapM_cost 1 _ (fun j => accessC ids j + (natC (ids.getD j 0) + g.netSC)) (fun j => by simp)]
  simp only [Nat.add_assoc]

/-- `networkL ids`: the node list, the four arc lists, the three appends, the terminals. -/
def networkM (ids : List ℕ) : Costed (Network ℕ) := do
  let nn ← g.netNodesM ids
  let a₁ ← g.nodeArcsM ids
  let a₂ ← g.edgeArcsM ids
  let a₃ ← g.srcArcsM ids
  let a₄ ← g.snkArcsM ids
  tick a₁.length
  let b₁ := a₁ ++ a₂
  tick b₁.length
  let b₂ := b₁ ++ a₃
  tick b₂.length
  let s ← g.netSM
  let t ← g.netTM
  Pure.pure ⟨nn, b₂ ++ a₄, s, t⟩

theorem networkM_val (ids : List ℕ) : (g.networkM ids).val = g.networkL ids := by
  simp only [networkM, networkL, bind_val, pure_val, netNodesM_val, nodeArcsM_val, edgeArcsM_val,
    srcArcsM_val, snkArcsM_val, netSM_val, netTM_val]

theorem networkM_cost (ids : List ℕ) : (g.networkM ids).cost = g.networkCL ids := by
  simp only [networkM, networkCL, appendsCL, bind_cost, pure_cost, tick_cost,
    netNodesM_val, nodeArcsM_val, edgeArcsM_val, srcArcsM_val, snkArcsM_val, netSM_val, netTM_val,
    netNodesM_cost, nodeArcsM_cost, edgeArcsM_cost, srcArcsM_cost, snkArcsM_cost, netSM_cost,
    netTM_cost]
  omega

/-- `rhoFlowL ids`: the network, the maximum flow (`UnitFlowExec.lean`), the filter of the flow
arcs leaving the source (`netS` re-formed inside the closure at every arc), the final length. -/
def rhoFlowM (ids : List ℕ) : Costed ℕ := do
  let N ← g.networkM ids
  let F ← N.maxflowM natC
  let kept ← filterM 1 (fun a => do
      let s ← g.netSM
      tick (natC a.1 + natC s)
      Pure.pure (a.1 == s)) F
  tick (kept.length + 1)
  Pure.pure kept.length

theorem rhoFlowM_val (ids : List ℕ) : (g.rhoFlowM ids).val = g.rhoFlowL ids := by
  simp only [rhoFlowM, rhoFlowL, bind_val, pure_val, networkM_val, Network.maxflowM_val]
  rw [filterM_val 1 _ (fun a => a.1 == g.netS) (fun a => rfl)]

theorem rhoFlowM_cost (ids : List ℕ) : (g.rhoFlowM ids).cost = g.rhoFlowCL ids := by
  simp only [rhoFlowM, rhoFlowCL, bind_cost, pure_cost, tick_cost, networkM_val,
    networkM_cost, Network.maxflowM_val, Network.maxflowM_cost]
  rw [filterM_val 1 _ (fun a => a.1 == g.netS) (fun a => rfl),
    filterM_cost 1 _ (fun a => g.netSC + (natC a.1 + natC g.netS)) (fun a => by simp)]
  simp only [Nat.add_assoc]

/-- **The instrumented decision procedure**, following the `if` structure of `strictDecideP`:
the degree comparison, then (if `2 ≤ k`) the validity check, then (if valid) the identifier
table (computed once, `let`-shared) and the test scan, then (if distinct) the flow value and
the final comparison. -/
def strictDecidePM (k : ℕ) : Costed Bool := do
  tick (natC 2 + natC k)
  if 2 ≤ k then
    let v ← g.isValidGM
    if v then
      let ids ← g.canonIdsM
      let d ← g.testsDistinctM ids
      if d then
        let r ← g.rhoFlowM ids
        tick (natC k + natC (k + 1) + natC r)
        Pure.pure (decide (k + 1 ≤ r))
      else Pure.pure false
    else Pure.pure false
  else Pure.pure false

theorem strictDecidePM_val (k : ℕ) : (g.strictDecidePM k).val = g.strictDecideP k := by
  unfold strictDecidePM strictDecideP
  by_cases hk : 2 ≤ k
  · cases hv : g.isValid
    · simp [hk, hv, isValidGM_val]
    · cases ht : g.base.testsDistinct g.base.canonIds <;>
        simp [hk, hv, ht, isValidGM_val, canonIdsM_val, testsDistinctM_val, rhoFlowM_val]
  · simp [hk]

theorem strictDecidePM_cost (k : ℕ) : (g.strictDecidePM k).cost = g.strictDecidePC k := by
  unfold strictDecidePM strictDecidePC
  by_cases hk : 2 ≤ k
  · cases hv : g.isValid
    · simp [hk, hv, isValidGM_val, isValidGM_cost]
    · cases ht : g.base.testsDistinct g.base.canonIds
      · simp [hk, hv, ht, isValidGM_val, isValidGM_cost, canonIdsM_val, canonIdsM_cost,
          testsDistinctM_val, testsDistinctM_cost]
      · simp [hk, hv, ht, isValidGM_val, isValidGM_cost, canonIdsM_val, canonIdsM_cost,
          testsDistinctM_val, testsDistinctM_cost, rhoFlowM_val, rhoFlowM_cost]
        omega
  · simp [hk]

/-- **Execution link for the decision procedure**: the instrumented program computes
`strictDecideP k g` and executes exactly `strictDecidePC k g` primitive steps. -/
theorem strictDecidePM_spec (k : ℕ) :
    (g.strictDecidePM k).val = g.strictDecideP k ∧ (g.strictDecidePM k).cost = g.strictDecidePC k :=
  ⟨g.strictDecidePM_val k, g.strictDecidePM_cost k⟩

/-- The instrumented decision executes at most `91000·S⁶ + 3·natC k` primitive steps. -/
theorem strictDecidePM_steps (k : ℕ) :
    (g.strictDecidePM k).cost ≤ 91000 * sizeG g ^ 6 + 3 * natC k := by
  rw [strictDecidePM_cost]; exact g.strictDecidePC_le k

end GInstance

/-! ### The whole-language program -/

open DisequalityDispersion.Costed

/-- **The instrumented whole-language decision**: parse (`ParsingExec.lean`), then decide. -/
def decideBitsM (l : List Bool) : Costed Bool := do
  let r ← decodeInputM l
  match r with
  | none => Pure.pure false
  | some (k, g) => g.strictDecidePM k

theorem decideBitsM_val (l : List Bool) : (decideBitsM l).val = decideBits l := by
  simp only [decideBitsM, decideBits, bind_val, decodeInputM_val]
  cases decodeInput l with
  | none => rfl
  | some p => obtain ⟨k, g⟩ := p; exact g.strictDecidePM_val k

theorem decideBitsM_cost (l : List Bool) : (decideBitsM l).cost = decideBitsC l := by
  simp only [decideBitsM, decideBitsC, bind_cost, decodeInputM_val, decodeInputM_cost]
  cases decodeInput l with
  | none => rfl
  | some p => obtain ⟨k, g⟩ := p; simp only [g.strictDecidePM_cost k]

/-- **Execution link for the whole language**: on every bit string the instrumented program
computes `decideBits` (hence decides `StrictBits`, `decideBits_iff_StrictBits`) and executes
exactly `decideBitsC` primitive steps. -/
theorem decideBitsM_spec (l : List Bool) :
    (decideBitsM l).val = decideBits l ∧ (decideBitsM l).cost = decideBitsC l :=
  ⟨decideBitsM_val l, decideBitsM_cost l⟩

/-- On every bit string the instrumented whole-language program executes at most
`92000·(|l|+1)⁶` primitive steps. -/
theorem decideBitsM_steps (l : List Bool) : (decideBitsM l).cost ≤ 92000 * (l.length + 1) ^ 6 := by
  rw [decideBitsM_cost]; exact decideBitsC_le_all l

end DisequalityDispersion.Encoded
