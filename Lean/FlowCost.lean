import FlowCut
import UnitFlowCost

/-! # Charged bit cost of the polynomial-time decision (R5, item 3)

The input is the pair `(k, g)` written in binary: `encodeNat k ++ encodeBitsG g`,
of length `natC k + sizeG g`.  The cost functions below mirror the executable
definitions of `FlowCut.lean` in the model of `EncodingCost.lean`, one cost
function per definition with the same recursion shape.

**Charged primitive operations** (naturals are binary numbers, lists are linked lists):
reading, copying, comparing or shifting a natural `v` costs `natC v` (its code length);
a sequential access `l.getD i d` costs `accessC l i`; measuring a length costs the length;
every list cell visited by a scan, map, filter, append or flatten costs `1` plus the work
done at that cell; deduplication is charged per entry as a scan of the current result.

**Operational rules charged** (no compiler optimisation is assumed): call-by-value with
`let` bound once; `if`/`match` evaluate only the selected branch (`strictDecideP` is
written with `if`, not `&&`); a closure re-evaluates its whole body at every call, so a
subexpression written inside a `fun` is charged once per call — `nodes.length` in the
validity checks, the representative table `repsL ids` in the three places it is used,
`netS`/`netT` inside the arc constructors, `ids.getD j 0` inside the inner argument map,
`steps p` inside the augmentation filter, and the recomputation of the layers by `augPath`
after `ffAux` has computed `seen U`.  The Phase-A cost functions `isValidC`/`canonIdsC`
did not charge some of these recomputations; the surcharges `isValidSurcharge` and
`canonSurcharge` add them here, leaving the Phase-A files untouched.

`strictDecidePC_le` bounds the charged cost of `strictDecideP k g` by
`91000 · sizeG g ^ 6 + 3 · natC k`: polynomial in the input length, and the degree `k`
enters only through the length of its binary code (compared with `2`, incremented once and
compared with `ρ`; never unfolded).
This is a charged-cost statement about the executable Lean definitions under the rules
above; the bridge to a fixed machine model is stated separately (see the return report). -/

namespace DisequalityDispersion.Encoded

open DisequalityDispersion.Flow

/-! ### Input size of a general instance -/

/-- Bit length of the general instance: the base instance and the extra output indices. -/
def sizeG (g : GInstance) : ℕ := sizeInstance g.base + listC natC g.outs

/-- The concrete bit encoding of a general instance. -/
def encodeBitsG (g : GInstance) : List Bool := encodeBits g.base ++ encodeList encodeNat g.outs

theorem encodeBitsG_length (g : GInstance) : (encodeBitsG g).length = sizeG g := by
  unfold encodeBitsG sizeG
  rw [List.length_append, encodeBits_length, encodeList_length encodeNat natC encodeNat_length]

/-- The full input `(k, g)` in binary. -/
def encodeInput (k : ℕ) (g : GInstance) : List Bool := encodeNat k ++ encodeBitsG g

theorem encodeInput_length (k : ℕ) (g : GInstance) :
    (encodeInput k g).length = natC k + sizeG g := by
  unfold encodeInput
  rw [List.length_append, encodeNat_length, encodeBitsG_length]

theorem flowBound_mono' {n m L n' m' L' : ℕ} (hn : n ≤ n') (hm : m ≤ m') (hL : L ≤ L') :
    Network.flowBound n m L ≤ Network.flowBound n' m' L' := by
  unfold Network.flowBound Network.roundB Network.seenB Network.augPathB Network.augmentB
    Network.layersB Network.layerRoundB Network.frontB Network.resB
  gcongr

theorem flowBound_closed (S : ℕ) (hS : 7 ≤ S) :
    Network.flowBound (3 * S) (5 * S) (5 * S) ≤ 90000 * S ^ 6 := by
  unfold Network.flowBound Network.roundB Network.seenB Network.augPathB Network.augmentB
    Network.layersB Network.layerRoundB Network.frontB Network.resB
  have h1 : S ≤ S ^ 6 := by
    calc S = S ^ 1 := (pow_one S).symm
      _ ≤ S ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
  ring_nf
  nlinarith

/-! ### Phase-A surcharges (recomputations inside closures not charged by `EncodingCost`) -/

namespace Instance
variable (γ : Instance)

/-- Recomputations inside the closures of `isValid` that `isValidC` does not charge: the scans
`γ.k = sources.length` in `x < k`, `y < k` and at every `src` node; `γ.m = symbols.length` and
`args.length` at every `app` node (charged at every node); measuring `nodes.length` and
producing `range nodes.length` in `nodesOk`; and the two scans of `nodes.length` at every
test. -/
def isValidSurcharge : ℕ :=
  2 * γ.sources.length + 2 * γ.nodes.length +
    (γ.nodes.map (fun nd => γ.sources.length + γ.symbols.length + argsLen nd)).sum +
    γ.tests.length * (2 * γ.nodes.length)

/-- Fully charged cost of `isValid`. -/
def isValidC' : ℕ := γ.isValidC + γ.isValidSurcharge

theorem isValidSurcharge_le : γ.isValidSurcharge ≤ 5 * sizeInstance γ ^ 2 := by
  unfold isValidSurcharge
  have h7 := γ.seven_le_size
  have hs := γ.sources_length_le
  have hn := γ.nodes_length_le
  have hy := γ.symbols_length_le
  have ht := γ.tests_length_le
  have ha := γ.sum_argsLen_le
  have h1 : (γ.nodes.map (fun nd => γ.sources.length + γ.symbols.length + argsLen nd)).sum =
      γ.nodes.length * (γ.sources.length + γ.symbols.length) + (γ.nodes.map argsLen).sum := by
    have := sum_map_le_of_le γ.nodes (fun _ => 0) 0 (fun _ _ => le_rfl)
    clear this
    induction γ.nodes with
    | nil => simp
    | cons nd l ih => simp [List.map_cons, List.sum_cons, ih, List.length_cons]; ring
  rw [h1]
  have e1 : γ.nodes.length * (γ.sources.length + γ.symbols.length) ≤
      sizeInstance γ * (2 * sizeInstance γ) := Nat.mul_le_mul hn (by omega)
  have e2 : γ.tests.length * (2 * γ.nodes.length) ≤ sizeInstance γ * (2 * sizeInstance γ) :=
    Nat.mul_le_mul ht (by omega)
  nlinarith

theorem isValidC'_le : γ.isValidC' ≤ 35 * sizeInstance γ ^ 2 + 27 * sizeInstance γ + 1 := by
  unfold isValidC'
  have := γ.isValidC_le
  have := γ.isValidSurcharge_le
  omega

/-- Recomputations of `canonIds` not charged by `canonIdsC`: measuring `nodes.length` and
producing `range nodes.length`; at step `j` the accumulator copy `acc ++ [_]` of `buildList`
(`j` cells), the counter comparisons of `firstIndex` (`j` of them, `natC j + 1` each), and
the node copies made by `sigWith` for node `j` and for every `i < j` (`nodeC`). -/
def canonSurcharge : ℕ :=
  2 * γ.nodes.length + ((List.range γ.nodes.length).map (fun j =>
    j + j * (natC j + 1) + nodeC (γ.nodes.getD j (.src 0)) +
      ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum)).sum

/-- Fully charged cost of `canonIds`. -/
def canonIdsC' : ℕ := γ.canonIdsC + γ.canonSurcharge

theorem sum_range_nodeC_le (j : ℕ) (hj : j ≤ γ.nodes.length) :
    ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum ≤ sizeInstance γ := by
  refine (sum_range_mono _ hj).trans ?_
  rw [sum_range_getD]
  exact γ.sum_nodeC_le

theorem canonSurcharge_le : γ.canonSurcharge ≤ 4 * sizeInstance γ ^ 3 := by
  unfold canonSurcharge
  have h7 := γ.seven_le_size
  have hn := γ.nodes_length_le
  have hB : ∀ j, j < γ.nodes.length →
      j + j * (natC j + 1) + nodeC (γ.nodes.getD j (.src 0)) +
        ((List.range j).map (fun i => nodeC (γ.nodes.getD i (.src 0)))).sum ≤
      sizeInstance γ + sizeInstance γ * (3 * sizeInstance γ + 1) + 2 * sizeInstance γ := by
    intro j hj
    have h1 : j ≤ sizeInstance γ := by omega
    have h2 : natC j ≤ 3 * sizeInstance γ := γ.natC_le_three h1
    have h3 := γ.nodeC_getD_le j (.src 0) γ.nodeC_src_zero_le
    have h4 := γ.sum_range_nodeC_le j hj.le
    have h5 : j * (natC j + 1) ≤ sizeInstance γ * (3 * sizeInstance γ + 1) :=
      Nat.mul_le_mul h1 (by omega)
    omega
  have := sum_range_le_of_le γ.nodes.length _ _ hB
  have e : γ.nodes.length * (sizeInstance γ + sizeInstance γ * (3 * sizeInstance γ + 1) +
      2 * sizeInstance γ) ≤ sizeInstance γ * (sizeInstance γ + sizeInstance γ * (3 * sizeInstance γ + 1) +
      2 * sizeInstance γ) := Nat.mul_le_mul_right _ hn
  have e2 : sizeInstance γ * (sizeInstance γ + sizeInstance γ * (3 * sizeInstance γ + 1) +
      2 * sizeInstance γ) = 3 * sizeInstance γ ^ 3 + 4 * sizeInstance γ ^ 2 := by ring
  have e3 : 4 * sizeInstance γ ^ 2 + 2 * sizeInstance γ ≤ sizeInstance γ ^ 3 := by nlinarith
  omega

theorem canonIdsC'_le : γ.canonIdsC' ≤ 8 * sizeInstance γ ^ 3 + 13 * sizeInstance γ ^ 2 +
    5 * sizeInstance γ := by
  unfold canonIdsC'
  have := γ.canonIdsC_le
  have := γ.canonSurcharge_le
  omega

end Instance

namespace GInstance
variable (g : GInstance)

/-! ### Cost functions -/

/-- Cost of measuring `nodes.length` and forming `netS`/`netT` (a scan and a shift). -/
def netSC : ℕ := g.base.nodes.length + 1 + natC g.netT

/-- Cost of measuring `nodes.length` and building `range nodes.length`. -/
def rangeC : ℕ := 2 * g.base.nodes.length

/-- Cost of `isValid`: the fully charged base check, then every extra output index is compared
with `nodes.length` (measured again at every index, inside the closure). -/
def isValidGC : ℕ :=
  g.base.isValidC' +
    (g.outs.map (fun o => 1 + g.base.nodes.length + natC o + natC g.base.nodes.length)).sum

/-- Cost of `reps`: the range, then every index is read, its identifier accessed and compared. -/
def repsC : ℕ :=
  g.rangeC + ((List.range g.base.nodes.length).map (fun j =>
    1 + accessC g.base.canonIds j + natC (g.repOf j) + natC j)).sum

/-- Cost of `nodeArcs`: `reps` is recomputed, then a pair of shifted labels per representative. -/
def nodeArcsC : ℕ := g.repsC + (g.reps.map (fun r => 1 + 2 * natC r)).sum

/-- Cost of `netNodes`: `reps` is computed twice (once per map), each map shifts its labels,
the two appends copy the lists, and `netS`/`netT` are formed. -/
def netNodesC : ℕ :=
  2 * g.repsC + 2 * (g.reps.map (fun r => 1 + natC r)).sum + 3 * g.reps.length + 2 * g.netSC + 2

/-- Cost of `dedupList` (each entry is scanned for in the deduplicated remainder). -/
def dedupC : List (ℕ × ℕ) → ℕ
  | [] => 0
  | x :: l => 1 + Network.memC natC (dedupList l) x + dedupC l

/-- The raw (pre-deduplication) edge list. -/
def edgeRaw : List (ℕ × ℕ) :=
  (List.range g.base.nodes.length).flatMap
    (fun j => (g.argsOf j).map (fun a => (2 * g.repOf a + 1, 2 * g.repOf j)))

/-- Cost of `edgeArcs`: the range; each node accessed; for each argument both identifiers are
looked up (the node's own identifier is re-read inside the inner closure) and shifted; the
per-node lists are flattened (one cell per copied arc and per node); then deduplication. -/
def edgeArcsC : ℕ :=
  g.rangeC + ((List.range g.base.nodes.length).map (fun j =>
    1 + accessC g.base.nodes j +
      ((g.argsOf j).map (fun a => 1 + accessC g.base.canonIds a + natC (g.repOf a) +
        accessC g.base.canonIds j + natC (g.repOf j))).sum)).sum +
    (g.edgeRaw.length + g.base.nodes.length) + dedupC g.edgeRaw

/-- The raw source-arc list. -/
def srcRaw : List (ℕ × ℕ) :=
  ((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j => (g.netS, 2 * g.repOf j))

/-- Cost of `srcArcs`: the range; each node accessed for the source test; for each kept node
`netS` is formed inside the closure and the identifier looked up and shifted. -/
def srcArcsC : ℕ :=
  g.rangeC + ((List.range g.base.nodes.length).map (fun j => 1 + accessC g.base.nodes j)).sum +
    (((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j =>
      1 + g.netSC + accessC g.base.canonIds j + natC (g.repOf j))).sum +
    dedupC g.srcRaw

/-- Cost of `nodes.idxOf nd`: a scan comparing nodes. -/
def idxOfC (nd : Node) : ℕ := (g.base.nodes.map (fun nd' => 1 + nodeC nd + nodeC nd')).sum

/-- The raw sink-arc list. -/
def snkRaw : List (ℕ × ℕ) := g.outNodes.map (fun j => (2 * g.repOf j + 1, g.netT))

/-- Cost of `snkArcs`: the two `idxOf` scans of `outNodes` (each building a `src` node), the
append, then per output node the identifier lookup, the shift and `netT` inside the closure. -/
def snkArcsC : ℕ :=
  natC g.base.x + g.idxOfC (.src g.base.x) + natC g.base.y + g.idxOfC (.src g.base.y) + 2 +
    (g.outNodes.map (fun j => 1 + accessC g.base.canonIds j + natC (g.repOf j) + g.netSC)).sum +
    dedupC g.snkRaw

/-- Cost of the three appends forming the arc list (one cell per copied element of the left
operand of each append). -/
def appendsC : ℕ :=
  g.nodeArcs.length + (g.nodeArcs ++ g.edgeArcs).length +
    (g.nodeArcs ++ g.edgeArcs ++ g.srcArcs).length

/-- Cost of building the split network: the four arc lists, their appends, the node list and the
two terminals. -/
def networkC : ℕ :=
  g.netNodesC + g.nodeArcsC + g.edgeArcsC + g.srcArcsC + g.snkArcsC + g.appendsC + 2 * g.netSC

/-- Cost of `rhoFlow`: the network, the maximum flow, the count (`netS` is re-formed inside the
filter closure at every flow arc) and the final length. -/
def rhoFlowC : ℕ :=
  g.networkC + g.network.maxflowC natC +
    (g.network.maxflow.map (fun a => 1 + g.netSC + natC a.1 + natC g.netS)).sum +
    (g.network.maxflow.filter (fun a => a.1 == g.netS)).length + 1

/-! The execution-linked versions take the identifier table `ids` explicitly, exactly like the
executable definitions `repsL`, `edgeArcsL`, …, `rhoFlowL`; the unparametrised cost
functions above are their instances at `ids = g.base.canonIds` (definitionally). -/

def repsCL (ids : List ℕ) : ℕ :=
  g.rangeC + ((List.range g.base.nodes.length).map (fun j =>
    1 + accessC ids j + natC (ids.getD j 0) + natC j)).sum

def nodeArcsCL (ids : List ℕ) : ℕ := g.repsCL ids + ((g.repsL ids).map (fun r => 1 + 2 * natC r)).sum

def netNodesCL (ids : List ℕ) : ℕ :=
  2 * g.repsCL ids + 2 * ((g.repsL ids).map (fun r => 1 + natC r)).sum + 3 * (g.repsL ids).length +
    2 * g.netSC + 2

def edgeRawL (ids : List ℕ) : List (ℕ × ℕ) :=
  (List.range g.base.nodes.length).flatMap
    (fun j => (g.argsOf j).map (fun a => (2 * ids.getD a 0 + 1, 2 * ids.getD j 0)))

def edgeArcsCL (ids : List ℕ) : ℕ :=
  g.rangeC + ((List.range g.base.nodes.length).map (fun j =>
    1 + accessC g.base.nodes j +
      ((g.argsOf j).map (fun a => 1 + accessC ids a + natC (ids.getD a 0) +
        accessC ids j + natC (ids.getD j 0))).sum)).sum +
    ((g.edgeRawL ids).length + g.base.nodes.length) + dedupC (g.edgeRawL ids)

def srcRawL (ids : List ℕ) : List (ℕ × ℕ) :=
  ((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j => (g.netS, 2 * ids.getD j 0))

def srcArcsCL (ids : List ℕ) : ℕ :=
  g.rangeC + ((List.range g.base.nodes.length).map (fun j => 1 + accessC g.base.nodes j)).sum +
    (((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j =>
      1 + g.netSC + accessC ids j + natC (ids.getD j 0))).sum +
    dedupC (g.srcRawL ids)

def snkRawL (ids : List ℕ) : List (ℕ × ℕ) := g.outNodes.map (fun j => (2 * ids.getD j 0 + 1, g.netT))

def snkArcsCL (ids : List ℕ) : ℕ :=
  natC g.base.x + g.idxOfC (.src g.base.x) + natC g.base.y + g.idxOfC (.src g.base.y) + 2 +
    (g.outNodes.map (fun j => 1 + accessC ids j + natC (ids.getD j 0) + g.netSC)).sum +
    dedupC (g.snkRawL ids)

def appendsCL (ids : List ℕ) : ℕ :=
  (g.nodeArcsL ids).length + (g.nodeArcsL ids ++ g.edgeArcsL ids).length +
    (g.nodeArcsL ids ++ g.edgeArcsL ids ++ g.srcArcsL ids).length

def networkCL (ids : List ℕ) : ℕ :=
  g.netNodesCL ids + g.nodeArcsCL ids + g.edgeArcsCL ids + g.srcArcsCL ids + g.snkArcsCL ids +
    g.appendsCL ids + 2 * g.netSC

/-- Cost of `rhoFlowL ids`. -/
def rhoFlowCL (ids : List ℕ) : ℕ :=
  g.networkCL ids + (g.networkL ids).maxflowC natC +
    ((g.networkL ids).maxflow.map (fun a => 1 + g.netSC + natC a.1 + natC g.netS)).sum +
    ((g.networkL ids).maxflow.filter (fun a => a.1 == g.netS)).length + 1

theorem rhoFlowCL_canonIds : g.rhoFlowCL g.base.canonIds = g.rhoFlowC := rfl

/-- Total charged cost of `strictDecideP k g`, following its `if` structure exactly: the degree
comparison, then (if `2 ≤ k`) the validity check, then (if valid) the identifier table — computed
once and shared — and the test scan, then (if the tests are distinct) the flow computation and
the final comparison. -/
def strictDecidePC (k : ℕ) : ℕ :=
  natC 2 + natC k +
    (if 2 ≤ k then
      g.isValidGC +
        (if g.isValid then
          let ids := g.base.canonIds
          g.base.canonIdsC' + g.base.testsDistinctC ids +
            (if g.base.testsDistinct ids then
              g.rhoFlowCL ids + natC k + natC (k + 1) + natC (g.rhoFlowL ids)
             else 0)
         else 0)
     else 0)

theorem strictDecidePC_def (k : ℕ) : g.strictDecidePC k =
    natC 2 + natC k +
      (if 2 ≤ k then
        g.isValidGC +
          (if g.isValid then
            g.base.canonIdsC' + g.base.testsDistinctC g.base.canonIds +
              (if g.base.testsDistinct g.base.canonIds then
                g.rhoFlowC + natC k + natC (k + 1) + natC g.rhoFlow
               else 0)
           else 0)
       else 0) := rfl

/-! ### Size facts -/

theorem sizeInstance_le_sizeG : sizeInstance g.base ≤ sizeG g := by unfold sizeG; omega

theorem outs_length_le : g.outs.length ≤ sizeG g := by
  unfold sizeG
  have := length_le_listC natC g.outs (fun o _ => one_le_natC o)
  omega

theorem natC_out_le (o : ℕ) (ho : o ∈ g.outs) : natC o ≤ sizeG g := by
  unfold sizeG
  have := (le_sum_map_of_mem natC ho).trans (sum_map_le_listC natC g.outs)
  omega

theorem seven_le_sizeG : 7 ≤ sizeG g := g.base.seven_le_size.trans g.sizeInstance_le_sizeG

theorem nodes_le_size : g.base.nodes.length ≤ sizeInstance g.base := g.base.nodes_length_le

/-- Canonical identifiers never exceed the number of nodes. -/
theorem repOf_le_len (a : ℕ) : g.repOf a ≤ g.base.nodes.length := by
  unfold repOf
  rcases Nat.lt_or_ge a g.base.nodes.length with h | h
  · exact (g.base.buildList_canonStep_getD_le _ a).trans h.le
  · rw [List.getD_eq_default _ _ (by rw [Instance.canonIds_length]; exact h)]
    exact Nat.zero_le _

theorem natC_repOf_le (a : ℕ) : natC (g.repOf a) ≤ 3 * sizeInstance g.base :=
  g.base.natC_le_three ((g.repOf_le_len a).trans g.nodes_le_size)

theorem natC_idx_le (j : ℕ) (hj : j < g.base.nodes.length) : natC j ≤ 3 * sizeInstance g.base :=
  g.base.natC_le_three (hj.le.trans g.nodes_le_size)

/-- Bound on the code length of every network label. -/
def labelB : ℕ := natC (2 * g.base.nodes.length + 1)

theorem labelB_le : g.labelB ≤ 4 * sizeInstance g.base + 3 := by
  unfold labelB
  have := natC_le_linear (2 * g.base.nodes.length + 1)
  have := g.nodes_le_size
  omega

theorem reps_length_le : g.reps.length ≤ g.base.nodes.length := by
  unfold reps repsL
  exact (List.length_filter_le _ _).trans (by simp)

theorem netNodes_length : g.network.nodes.length = 2 * g.reps.length + 2 := by
  show (g.reps.map (fun r => 2 * r) ++ g.reps.map (fun r => 2 * r + 1) ++
    [g.netS, g.netT]).length = _
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem label_le (x : ℕ) (hx : x ∈ g.network.nodes) : natC x ≤ g.labelB := by
  rw [g.mem_netNodes] at hx
  unfold labelB
  apply natC_mono
  rcases hx with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl | rfl
  · have := g.reps_lt r hr; omega
  · have := g.reps_lt r hr; omega
  · simp [netS]
  · simp [netT]

theorem argsOf_length_eq (j : ℕ) :
    (g.argsOf j).length = Instance.argsLen (g.base.nodes.getD j (.src 0)) := by
  unfold argsOf
  cases g.base.nodes.getD j (.src 0) <;> simp [Instance.argsLen]

theorem edgeRaw_length_le : g.edgeRaw.length ≤ sizeInstance g.base := by
  unfold edgeRaw
  rw [List.length_flatMap]
  have := g.base.sum_range_argsLen_le g.base.nodes.length le_rfl
  refine le_trans (le_of_eq ?_) this
  congr 1
  apply List.map_congr_left
  intro j _
  simp [g.argsOf_length_eq]

theorem srcRaw_length_le : g.srcRaw.length ≤ g.base.nodes.length := by
  unfold srcRaw
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem outNodes_length : g.outNodes.length = 2 + g.outs.length := by
  simp [outNodes]; omega

theorem snkRaw_length : g.snkRaw.length = 2 + g.outs.length := by
  simp [snkRaw, outNodes]; omega

theorem arcs_length_le : g.network.arcs.length ≤ 3 * sizeInstance g.base + 2 + g.outs.length := by
  show (g.nodeArcs ++ g.edgeArcs ++ g.srcArcs ++ g.snkArcs).length ≤ _
  simp only [List.length_append]
  have h1 : g.nodeArcs.length ≤ g.base.nodes.length := by
    show (g.reps.map (fun r => (2 * r, 2 * r + 1))).length ≤ _
    rw [List.length_map]; exact g.reps_length_le
  have h2 : g.edgeArcs.length ≤ sizeInstance g.base := by
    show (dedupList g.edgeRaw).length ≤ _
    rw [dedupList_length]
    exact (List.toFinset_card_le _).trans g.edgeRaw_length_le
  have h3 : g.srcArcs.length ≤ g.base.nodes.length := by
    show (dedupList g.srcRaw).length ≤ _
    rw [dedupList_length]
    exact (List.toFinset_card_le _).trans g.srcRaw_length_le
  have h4 : g.snkArcs.length ≤ 2 + g.outs.length := by
    show (dedupList g.snkRaw).length ≤ _
    rw [dedupList_length]
    exact (List.toFinset_card_le _).trans (le_of_eq g.snkRaw_length)
  have := g.nodes_le_size
  omega

/-! ### Bounds on the construction cost -/


/-! ### Bounds on the construction cost -/

theorem memC_le' (L : ℕ) (l : List (ℕ × ℕ)) (e : ℕ × ℕ)
    (hl : ∀ e' ∈ l, Network.pc natC e' ≤ 2 * L) (he : Network.pc natC e ≤ 2 * L) :
    Network.memC natC l e ≤ l.length * (1 + 4 * L) := by
  unfold Network.memC
  apply sum_map_le_of_le
  intro e' he'
  have := hl e' he'
  omega

theorem pc_le_labelB (e : ℕ × ℕ) (h1 : e.1 ≤ 2 * g.base.nodes.length + 1)
    (h2 : e.2 ≤ 2 * g.base.nodes.length + 1) : Network.pc natC e ≤ 2 * g.labelB := by
  unfold Network.pc labelB
  have := natC_mono h1
  have := natC_mono h2
  omega

theorem dedupC_le (L : ℕ) : ∀ (l : List (ℕ × ℕ)), (∀ e ∈ l, Network.pc natC e ≤ 2 * L) →
    dedupC l ≤ l.length * (1 + l.length * (1 + 4 * L))
  | [], _ => by simp [dedupC]
  | x :: l, h => by
      simp only [dedupC, List.length_cons]
      have hmem : ∀ e ∈ dedupList l, e ∈ l := by
        intro e he
        rw [← List.mem_toFinset, dedupList_toFinset, List.mem_toFinset] at he
        exact he
      have h1 := memC_le' L (dedupList l) x
        (fun e he => h e (List.mem_cons_of_mem _ (hmem e he)))
        (h x List.mem_cons_self)
      have h2 := dedupC_le L l (fun e he => h e (List.mem_cons_of_mem _ he))
      have h3 : (dedupList l).length ≤ l.length := by
        rw [dedupList_length]; exact List.toFinset_card_le _
      have := Nat.mul_le_mul_right (1 + 4 * L) h3
      nlinarith

theorem sum_range_add_mul (n A c : ℕ) (h : ℕ → ℕ) :
    ((List.range n).map (fun j => A + h j * c)).sum = n * A + c * ((List.range n).map h).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      ring

theorem sum_argsOf_le :
    ((List.range g.base.nodes.length).map (fun j => (g.argsOf j).length)).sum ≤
      sizeInstance g.base := by
  have := g.base.sum_range_argsLen_le g.base.nodes.length le_rfl
  refine le_trans (le_of_eq ?_) this
  congr 1
  apply List.map_congr_left
  intro j _
  exact g.argsOf_length_eq j

theorem netSC_le : g.netSC ≤ g.base.nodes.length + 1 + g.labelB := by
  unfold netSC labelB
  have : natC g.netT ≤ natC (2 * g.base.nodes.length + 1) := natC_mono (by simp [netT])
  omega

theorem natC_reps_le (r : ℕ) (hr : r ∈ g.reps) : natC r ≤ 3 * sizeInstance g.base :=
  g.natC_idx_le r (g.reps_lt r hr)

theorem repsC_le : g.repsC ≤ g.rangeC + g.base.nodes.length *
    (g.base.nodes.length + 2 + 6 * sizeInstance g.base) := by
  unfold repsC
  have : ((List.range g.base.nodes.length).map (fun j =>
      1 + accessC g.base.canonIds j + natC (g.repOf j) + natC j)).sum ≤
      g.base.nodes.length * (g.base.nodes.length + 2 + 6 * sizeInstance g.base) := by
    apply sum_range_le_of_le
    intro j hj
    have h1 : accessC g.base.canonIds j ≤ g.base.nodes.length + 1 := by
      have := accessC_le g.base.canonIds j
      rw [Instance.canonIds_length] at this
      exact this
    have h2 := g.natC_repOf_le j
    have h3 := g.natC_idx_le j hj
    omega
  omega

theorem nodeArcsC_le : g.nodeArcsC ≤ g.repsC + g.base.nodes.length * (1 + 6 * sizeInstance g.base) := by
  unfold nodeArcsC
  have := sum_map_le_of_le g.reps (fun r => 1 + 2 * natC r) (1 + 6 * sizeInstance g.base)
    (fun r hr => by have := g.natC_reps_le r hr; dsimp only; omega)
  have := Nat.mul_le_mul_right (1 + 6 * sizeInstance g.base) g.reps_length_le
  omega

theorem netNodesC_le : g.netNodesC ≤ 2 * g.repsC + 2 * (g.base.nodes.length * (1 + 3 * sizeInstance g.base)) +
    3 * g.base.nodes.length + 2 * g.netSC + 2 := by
  unfold netNodesC
  have := sum_map_le_of_le g.reps (fun r => 1 + natC r) (1 + 3 * sizeInstance g.base)
    (fun r hr => by have := g.natC_reps_le r hr; dsimp only; omega)
  have := Nat.mul_le_mul_right (1 + 3 * sizeInstance g.base) g.reps_length_le
  have := g.reps_length_le
  omega

theorem edgeRaw_labels (e : ℕ × ℕ) (he : e ∈ g.edgeRaw) : Network.pc natC e ≤ 2 * g.labelB := by
  unfold edgeRaw at he
  rw [List.mem_flatMap] at he
  obtain ⟨j, _, he⟩ := he
  rw [List.mem_map] at he
  obtain ⟨a, _, rfl⟩ := he
  apply g.pc_le_labelB
  · have := g.repOf_le_len a; dsimp only; omega
  · have := g.repOf_le_len j; dsimp only; omega

theorem edgeArcsC_le : g.edgeArcsC ≤
    g.rangeC + g.base.nodes.length * (g.base.nodes.length + 2) +
      sizeInstance g.base * (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) +
      (sizeInstance g.base + g.base.nodes.length) +
      sizeInstance g.base * (1 + sizeInstance g.base * (1 + 4 * g.labelB)) := by
  unfold edgeArcsC
  have hacc : ∀ i, accessC g.base.canonIds i ≤ g.base.nodes.length + 1 := by
    intro i
    have := accessC_le g.base.canonIds i
    rw [Instance.canonIds_length] at this
    exact this
  have hacc' : ∀ i, accessC g.base.nodes i ≤ g.base.nodes.length + 1 := fun i => accessC_le _ _
  have h1 : ((List.range g.base.nodes.length).map (fun j =>
      1 + accessC g.base.nodes j +
        ((g.argsOf j).map (fun a => 1 + accessC g.base.canonIds a + natC (g.repOf a) +
          accessC g.base.canonIds j + natC (g.repOf j))).sum)).sum ≤
      ((List.range g.base.nodes.length).map (fun j =>
        (g.base.nodes.length + 2) +
          (g.argsOf j).length * (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base))).sum := by
    apply List.sum_le_sum
    intro j _
    have h2 : ((g.argsOf j).map (fun a => 1 + accessC g.base.canonIds a + natC (g.repOf a) +
        accessC g.base.canonIds j + natC (g.repOf j))).sum ≤
        (g.argsOf j).length * (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) := by
      apply sum_map_le_of_le
      intro a _
      have := hacc a
      have := hacc j
      have := g.natC_repOf_le a
      have := g.natC_repOf_le j
      omega
    have := hacc' j
    omega
  rw [sum_range_add_mul] at h1
  have h3 := g.sum_argsOf_le
  have h4 := dedupC_le g.labelB g.edgeRaw g.edgeRaw_labels
  have h5 := g.edgeRaw_length_le
  have h6 : (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) *
      ((List.range g.base.nodes.length).map (fun j => (g.argsOf j).length)).sum ≤
      (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) * sizeInstance g.base :=
    Nat.mul_le_mul_left _ h3
  have h7 : g.edgeRaw.length * (1 + g.edgeRaw.length * (1 + 4 * g.labelB)) ≤
      sizeInstance g.base * (1 + sizeInstance g.base * (1 + 4 * g.labelB)) := by
    apply Nat.mul_le_mul h5
    have := Nat.mul_le_mul_right (1 + 4 * g.labelB) h5
    omega
  have h8 : (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) * sizeInstance g.base =
      sizeInstance g.base * (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) := Nat.mul_comm _ _
  omega

theorem srcRaw_labels (e : ℕ × ℕ) (he : e ∈ g.srcRaw) : Network.pc natC e ≤ 2 * g.labelB := by
  unfold srcRaw at he
  rw [List.mem_map] at he
  obtain ⟨j, _, rfl⟩ := he
  apply g.pc_le_labelB
  · simp [netS]
  · have := g.repOf_le_len j; dsimp only; omega

theorem srcArcsC_le : g.srcArcsC ≤
    g.rangeC + g.base.nodes.length * (2 * g.base.nodes.length + 4 + g.netSC + 3 * sizeInstance g.base) +
      g.base.nodes.length * (1 + g.base.nodes.length * (1 + 4 * g.labelB)) := by
  unfold srcArcsC
  have h1a : ((List.range g.base.nodes.length).map (fun j => 1 + accessC g.base.nodes j)).sum ≤
      g.base.nodes.length * (g.base.nodes.length + 2) := by
    apply sum_range_le_of_le
    intro j _
    have := accessC_le g.base.nodes j
    omega
  have h1b : (((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j =>
      1 + g.netSC + accessC g.base.canonIds j + natC (g.repOf j))).sum ≤
      g.base.nodes.length * (g.base.nodes.length + 2 + g.netSC + 3 * sizeInstance g.base) := by
    have : (((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j =>
        1 + g.netSC + accessC g.base.canonIds j + natC (g.repOf j))).sum ≤
        ((List.range g.base.nodes.length).filter g.isSrcNode).length *
          (g.base.nodes.length + 2 + g.netSC + 3 * sizeInstance g.base) := by
      apply sum_map_le_of_le
      intro j _
      have h2 := accessC_le g.base.canonIds j
      rw [Instance.canonIds_length] at h2
      have := g.natC_repOf_le j
      omega
    have hl : ((List.range g.base.nodes.length).filter g.isSrcNode).length ≤ g.base.nodes.length :=
      (List.length_filter_le _ _).trans (by simp)
    have := Nat.mul_le_mul_right (g.base.nodes.length + 2 + g.netSC + 3 * sizeInstance g.base) hl
    omega
  have h1 : ((List.range g.base.nodes.length).map (fun j => 1 + accessC g.base.nodes j)).sum +
      (((List.range g.base.nodes.length).filter g.isSrcNode).map (fun j =>
        1 + g.netSC + accessC g.base.canonIds j + natC (g.repOf j))).sum ≤
      g.base.nodes.length * (2 * g.base.nodes.length + 4 + g.netSC + 3 * sizeInstance g.base) := by
    have : g.base.nodes.length * (g.base.nodes.length + 2) +
        g.base.nodes.length * (g.base.nodes.length + 2 + g.netSC + 3 * sizeInstance g.base) =
        g.base.nodes.length * (2 * g.base.nodes.length + 4 + g.netSC + 3 * sizeInstance g.base) := by ring
    omega
  have h4 := dedupC_le g.labelB g.srcRaw g.srcRaw_labels
  have h5 := g.srcRaw_length_le
  have h6 : g.srcRaw.length * (1 + g.srcRaw.length * (1 + 4 * g.labelB)) ≤
      g.base.nodes.length * (1 + g.base.nodes.length * (1 + 4 * g.labelB)) := by
    apply Nat.mul_le_mul h5
    have := Nat.mul_le_mul_right (1 + 4 * g.labelB) h5
    omega
  omega

theorem idxOfC_le (i : ℕ) (hi : natC i ≤ sizeInstance g.base) :
    g.idxOfC (.src i) ≤ g.base.nodes.length * (2 + 2 * sizeInstance g.base) := by
  unfold idxOfC
  apply sum_map_le_of_le
  intro nd hnd
  have := g.base.nodeC_le_of_mem hnd
  have e : nodeC (Node.src i) = 1 + natC i := rfl
  omega

theorem snkRaw_labels (e : ℕ × ℕ) (he : e ∈ g.snkRaw) : Network.pc natC e ≤ 2 * g.labelB := by
  unfold snkRaw at he
  rw [List.mem_map] at he
  obtain ⟨j, _, rfl⟩ := he
  apply g.pc_le_labelB
  · have := g.repOf_le_len j; dsimp only; omega
  · simp [netT]

theorem snkArcsC_le : g.snkArcsC ≤
    2 * sizeInstance g.base + 2 * (g.base.nodes.length * (2 + 2 * sizeInstance g.base)) + 2 +
      (2 + g.outs.length) * (g.base.nodes.length + 2 + 3 * sizeInstance g.base + g.netSC) +
      (2 + g.outs.length) * (1 + (2 + g.outs.length) * (1 + 4 * g.labelB)) := by
  unfold snkArcsC
  have h1 := g.idxOfC_le g.base.x g.base.natC_x_le
  have h2 := g.idxOfC_le g.base.y g.base.natC_y_le
  have hx := g.base.natC_x_le
  have hy := g.base.natC_y_le
  have h3 : (g.outNodes.map (fun j =>
      1 + accessC g.base.canonIds j + natC (g.repOf j) + g.netSC)).sum ≤
      g.outNodes.length * (g.base.nodes.length + 2 + 3 * sizeInstance g.base + g.netSC) := by
    apply sum_map_le_of_le
    intro j _
    have h4 := accessC_le g.base.canonIds j
    rw [Instance.canonIds_length] at h4
    have := g.natC_repOf_le j
    omega
  have h6 := dedupC_le g.labelB g.snkRaw g.snkRaw_labels
  rw [g.snkRaw_length] at h6
  rw [g.outNodes_length] at h3
  omega

/-! ### Bounds in the input size -/

theorem labelB_le_sizeG : g.labelB ≤ 5 * sizeG g := by
  have := g.labelB_le; have := g.sizeInstance_le_sizeG; have := g.seven_le_sizeG; omega

theorem netSC_le_sizeG : g.netSC ≤ 7 * sizeG g := by
  have := g.netSC_le; have := g.labelB_le_sizeG; have := g.nodes_le_size
  have := g.sizeInstance_le_sizeG; have := g.seven_le_sizeG; omega

theorem netNodes_length_le : g.network.nodes.length ≤ 3 * sizeG g := by
  rw [g.netNodes_length]
  have := g.reps_length_le; have := g.nodes_le_size; have := g.sizeInstance_le_sizeG
  have := g.seven_le_sizeG
  omega

theorem arcs_length_le_sizeG : g.network.arcs.length ≤ 5 * sizeG g := by
  have := g.arcs_length_le; have := g.sizeInstance_le_sizeG; have := g.outs_length_le
  have := g.seven_le_sizeG
  omega

theorem repsC_le_sizeG : g.repsC ≤ 8 * sizeG g ^ 2 := by
  have h := g.repsC_le
  have hN : g.base.nodes.length ≤ sizeG g := g.nodes_le_size.trans g.sizeInstance_le_sizeG
  have hB : sizeInstance g.base ≤ sizeG g := g.sizeInstance_le_sizeG
  have h7 : 7 ≤ sizeG g := g.seven_le_sizeG
  unfold rangeC at h
  have e1 : g.base.nodes.length * (g.base.nodes.length + 2 + 6 * sizeInstance g.base) ≤
      sizeG g * (7 * sizeG g + 2) := Nat.mul_le_mul hN (by omega)
  have : sizeG g * (7 * sizeG g + 2) = 7 * sizeG g ^ 2 + 2 * sizeG g := by ring
  have : 4 * sizeG g ≤ sizeG g ^ 2 := by nlinarith
  omega

/-- The appends copy at most three times the final arc list. -/
theorem appendsC_le : g.appendsC ≤ 3 * g.network.arcs.length := by
  have : g.network.arcs = g.nodeArcs ++ g.edgeArcs ++ g.srcArcs ++ g.snkArcs := rfl
  unfold appendsC
  rw [this]
  simp only [List.length_append]
  omega

/-- The network construction costs at most `140 · S³`. -/
theorem networkC_le_sizeG : g.networkC ≤ 140 * sizeG g ^ 3 := by
  unfold networkC
  have ha := g.appendsC_le
  have hN : g.base.nodes.length ≤ sizeG g := g.nodes_le_size.trans g.sizeInstance_le_sizeG
  have hB : sizeInstance g.base ≤ sizeG g := g.sizeInstance_le_sizeG
  have ho : g.outs.length ≤ sizeG g := g.outs_length_le
  have hL : g.labelB ≤ 5 * sizeG g := g.labelB_le_sizeG
  have hS : g.netSC ≤ 7 * sizeG g := g.netSC_le_sizeG
  have h7 : 7 ≤ sizeG g := g.seven_le_sizeG
  have hr := g.repsC_le_sizeG
  have hm := g.arcs_length_le_sizeG
  have hn1 := g.nodeArcsC_le
  have hn2 := g.netNodesC_le
  have he := g.edgeArcsC_le
  have hs := g.srcArcsC_le
  have hk := g.snkArcsC_le
  unfold rangeC at he hs
  -- each product against `S`
  have e1 : g.base.nodes.length * (1 + 6 * sizeInstance g.base) ≤ sizeG g * (7 * sizeG g) :=
    Nat.mul_le_mul hN (by omega)
  have e2 : g.base.nodes.length * (1 + 3 * sizeInstance g.base) ≤ sizeG g * (4 * sizeG g) :=
    Nat.mul_le_mul hN (by omega)
  have e3 : g.base.nodes.length * (g.base.nodes.length + 2) ≤ sizeG g * (2 * sizeG g) :=
    Nat.mul_le_mul hN (by omega)
  have e4 : sizeInstance g.base * (2 * g.base.nodes.length + 3 + 6 * sizeInstance g.base) ≤
      sizeG g * (9 * sizeG g) := Nat.mul_le_mul hB (by omega)
  have e5 : sizeInstance g.base * (1 + sizeInstance g.base * (1 + 4 * g.labelB)) ≤
      sizeG g * (sizeG g + sizeG g * (21 * sizeG g)) := Nat.mul_le_mul hB (by
        have := Nat.mul_le_mul hB (by omega : 1 + 4 * g.labelB ≤ 21 * sizeG g); omega)
  have e6 : g.base.nodes.length * (2 * g.base.nodes.length + 4 + g.netSC + 3 * sizeInstance g.base) ≤
      sizeG g * (13 * sizeG g) := Nat.mul_le_mul hN (by omega)
  have e7 : g.base.nodes.length * (1 + g.base.nodes.length * (1 + 4 * g.labelB)) ≤
      sizeG g * (sizeG g + sizeG g * (21 * sizeG g)) := Nat.mul_le_mul hN (by
        have := Nat.mul_le_mul hN (by omega : 1 + 4 * g.labelB ≤ 21 * sizeG g); omega)
  have e8 : g.base.nodes.length * (2 + 2 * sizeInstance g.base) ≤ sizeG g * (3 * sizeG g) :=
    Nat.mul_le_mul hN (by omega)
  have e9 : (2 + g.outs.length) * (g.base.nodes.length + 2 + 3 * sizeInstance g.base + g.netSC) ≤
      (2 * sizeG g) * (12 * sizeG g) := Nat.mul_le_mul (by omega) (by omega)
  have e10 : (2 + g.outs.length) * (1 + (2 + g.outs.length) * (1 + 4 * g.labelB)) ≤
      (2 * sizeG g) * (sizeG g + (2 * sizeG g) * (21 * sizeG g)) := Nat.mul_le_mul (by omega) (by
        have := Nat.mul_le_mul (by omega : 2 + g.outs.length ≤ 2 * sizeG g)
          (by omega : 1 + 4 * g.labelB ≤ 21 * sizeG g); omega)
  have hS2 : sizeG g * sizeG g = sizeG g ^ 2 := by ring
  have hS3 : sizeG g * (sizeG g * sizeG g) = sizeG g ^ 3 := by ring
  have hpos : sizeG g ^ 2 ≤ sizeG g ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hpos1 : sizeG g ≤ sizeG g ^ 3 := by
    calc sizeG g = sizeG g ^ 1 := (pow_one _).symm
      _ ≤ sizeG g ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  nlinarith

theorem maxflowC_le_sizeG (hv : g.Valid) : g.network.maxflowC natC ≤ 90000 * sizeG g ^ 6 := by
  have h1 := g.network.maxflowC_le natC (g.network_ok hv) g.labelB g.label_le
  have h2 := flowBound_mono' g.netNodes_length_le g.arcs_length_le_sizeG g.labelB_le_sizeG
  exact h1.trans (h2.trans (flowBound_closed _ g.seven_le_sizeG))

theorem count_le_sizeG (hv : g.Valid) :
    (g.network.maxflow.map (fun a => 1 + g.netSC + natC a.1 + natC g.netS)).sum +
      (g.network.maxflow.filter (fun a => a.1 == g.netS)).length ≤ 100 * sizeG g ^ 2 := by
  have hN := g.network_ok hv
  have hg := (g.network.maxflow_spec hN).1
  have hm := g.network.good_length_le _ hg
  have h1 : (g.network.maxflow.map (fun a => 1 + g.netSC + natC a.1 + natC g.netS)).sum ≤
      g.network.maxflow.length * (1 + g.netSC + 2 * g.labelB) := by
    apply sum_map_le_of_le
    intro a ha
    have h2 : a ∈ g.network.arcs := hg.flow.sub a (List.mem_toFinset.mpr ha)
    have h3 := g.label_le a.1 (hN.arcs_mem a h2).1
    have h4 : natC g.netS ≤ g.labelB := natC_mono (by simp [netS])
    omega
  have h5 := g.arcs_length_le_sizeG
  have h6 := g.labelB_le_sizeG
  have h7 := g.netSC_le_sizeG
  have h8 := g.seven_le_sizeG
  have h9 : g.network.maxflow.length * (1 + g.netSC + 2 * g.labelB) ≤ (5 * sizeG g) * (18 * sizeG g) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hfl := List.length_filter_le (fun a : ℕ × ℕ => a.1 == g.netS) g.network.maxflow
  have : (5 * sizeG g) * (18 * sizeG g) = 90 * sizeG g ^ 2 := by ring
  have : sizeG g ≤ sizeG g ^ 2 := by nlinarith
  omega

theorem natC_rhoFlow_le (hv : g.Valid) : natC g.rhoFlow ≤ 11 * sizeG g := by
  have h1 : g.rhoFlow ≤ g.network.arcs.length := by
    rw [g.rhoFlow_eq_value hv]
    exact g.network.value_le_arcs (g.network.maxflow_spec (g.network_ok hv)).1.flow
  have := natC_le_linear g.rhoFlow
  have := g.arcs_length_le_sizeG
  have := g.seven_le_sizeG
  omega

theorem rhoFlowC_le_sizeG (hv : g.Valid) : g.rhoFlowC ≤ 90000 * sizeG g ^ 6 + 241 * sizeG g ^ 3 := by
  unfold rhoFlowC
  have h1 := g.networkC_le_sizeG
  have h2 := g.maxflowC_le_sizeG hv
  have h3 := g.count_le_sizeG hv
  have h7 := g.seven_le_sizeG
  have : sizeG g ^ 2 ≤ sizeG g ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have : 1 ≤ sizeG g ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

theorem isValidGC_le : g.isValidGC ≤ 45 * sizeG g ^ 2 := by
  unfold isValidGC
  have h1 := g.base.isValidC'_le
  have h2 : (g.outs.map (fun o => 1 + g.base.nodes.length + natC o + natC g.base.nodes.length)).sum ≤
      g.outs.length * (1 + 5 * sizeG g) := by
    apply sum_map_le_of_le
    intro o ho
    have := g.natC_out_le o ho
    have := g.base.natC_len_le
    have := g.nodes_le_size
    have := g.sizeInstance_le_sizeG
    omega
  have h3 := Nat.mul_le_mul_right (1 + 5 * sizeG g) g.outs_length_le
  have hB := g.sizeInstance_le_sizeG
  have h7 := g.seven_le_sizeG
  have hB2 : sizeInstance g.base ^ 2 ≤ sizeG g ^ 2 := Nat.pow_le_pow_left hB 2
  nlinarith

theorem natC_succ_le (k : ℕ) : natC (k + 1) ≤ natC k + 2 := by
  unfold natC
  have : (k + 1).size ≤ k.size + 1 := by
    rw [Nat.size_le, pow_succ]
    have := Nat.lt_size_self k
    omega
  omega

/-- **Polynomial charged bit cost of the polynomial-time decision, uniformly in binary `k`.**
Under the charged operations and evaluation rules stated at the top of this file,
`strictDecideP k g` costs at most `91000 · S⁶ + 3 · natC k` bit steps on every input, where `S`
is the bit length of the instance and `natC k` the bit length of the degree (compared with `2`,
incremented once, compared with `ρ`; never unfolded); the binary input `encodeInput k g` has
length `natC k + S`. -/
theorem strictDecidePC_le (k : ℕ) : g.strictDecidePC k ≤ 91000 * sizeG g ^ 6 + 3 * natC k := by
  rw [g.strictDecidePC_def]
  have h7 := g.seven_le_sizeG
  have hV := g.isValidGC_le
  have hS2 : sizeG g ^ 2 ≤ sizeG g ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hS3 : sizeG g ^ 3 ≤ sizeG g ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hS1 : sizeG g ≤ sizeG g ^ 6 := by
    calc sizeG g = sizeG g ^ 1 := (pow_one _).symm
      _ ≤ sizeG g ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2n : natC 2 ≤ 5 := natC_le_linear 2
  have hk1 := natC_succ_le k
  split_ifs with hk hv ht
  · have hv' : g.Valid := hv
    have h1 := g.base.canonIdsC'_le
    have h2 := g.base.testsDistinctC_le
    have hB := g.sizeInstance_le_sizeG
    have hB2 : sizeInstance g.base ^ 2 ≤ sizeG g ^ 2 := Nat.pow_le_pow_left hB 2
    have hB3 : sizeInstance g.base ^ 3 ≤ sizeG g ^ 3 := Nat.pow_le_pow_left hB 3
    have h3 := g.rhoFlowC_le_sizeG hv'
    have h6 := g.natC_rhoFlow_le hv'
    have hlow : 8 * sizeG g ^ 3 + 13 * sizeG g ^ 2 + 5 * sizeG g + 7 * sizeG g ^ 2 + 45 * sizeG g ^ 2 +
        241 * sizeG g ^ 3 + 11 * sizeG g + 7 ≤ 1000 * sizeG g ^ 6 := by omega
    omega
  · have h1 := g.base.canonIdsC'_le
    have h2 := g.base.testsDistinctC_le
    have hB := g.sizeInstance_le_sizeG
    have hB2 : sizeInstance g.base ^ 2 ≤ sizeG g ^ 2 := Nat.pow_le_pow_left hB 2
    have hB3 : sizeInstance g.base ^ 3 ≤ sizeG g ^ 3 := Nat.pow_le_pow_left hB 3
    omega
  · omega
  · omega

end GInstance
end DisequalityDispersion.Encoded
