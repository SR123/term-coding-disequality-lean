import UnitFlow
import GeneralAlgorithm
import GeneralComputable

/-! # Polynomial-time `ρ`: the split network and the max-flow computation (R5, item 3)

The minimum vertex cut `ρ` between the source nodes and the output nodes of the
canonical DAG is computed as a maximum flow in the *split network* on canonical
node identifiers: every representative `r` becomes an arc `2r → 2r+1`, every
argument edge `a → j` becomes an arc `2·rep a + 1 → 2·rep j`, a super-source
`s = 2N` feeds every source representative and every output representative
feeds a super-sink `t = 2N+1`.  All arcs have unit capacity, so
`Flow.Network.maxflow` (augmenting paths) computes the minimum cut.

* `rhoFlow_eq`: the flow value equals `cutSize` of the decoded instance;
* `strictDecideP_eq`: the polynomial-time decision agrees with `strictDecideG`
  on every input, hence (`strictDecideP_iff`) it is exactly correct against
  `Strict k` for every degree `k ≥ 2`. -/

namespace DisequalityDispersion.Encoded
namespace GInstance
open Flow

variable (g : GInstance)

/-! ### Executable definitions

The identifier table `ids = g.base.canonIds` is computed once by the caller and passed
explicitly to the constructions (`…L ids`); the unparametrised names below are the
specification-level abbreviations `… = …L g.base.canonIds` (definitional). -/

/-- Argument indices of node `j` (empty for sources). -/
def argsOf (j : ℕ) : List ℕ :=
  match g.base.nodes.getD j (.src 0) with
  | .src _ => []
  | .app _ args => args

/-- Is node `j` a source node? -/
def isSrcNode (j : ℕ) : Bool :=
  match g.base.nodes.getD j (.src 0) with
  | .src _ => true
  | .app _ _ => false

def netS : ℕ := 2 * g.base.nodes.length
def netT : ℕ := 2 * g.base.nodes.length + 1

/-- The canonical representatives, read off the table `ids`. -/
def repsL (ids : List ℕ) : List ℕ :=
  (List.range g.base.nodes.length).filter (fun j => ids.getD j 0 == j)

def netNodesL (ids : List ℕ) : List ℕ :=
  (g.repsL ids).map (fun r => 2 * r) ++ (g.repsL ids).map (fun r => 2 * r + 1) ++ [g.netS, g.netT]

/-- The arc through a representative (its unit vertex capacity). -/
def nodeArcsL (ids : List ℕ) : List (ℕ × ℕ) := (g.repsL ids).map (fun r => (2 * r, 2 * r + 1))

/-- Argument edges, on representatives. -/
def edgeArcsL (ids : List ℕ) : List (ℕ × ℕ) :=
  dedupList ((List.range g.base.nodes.length).flatMap
    (fun j => (g.argsOf j).map (fun a => (2 * ids.getD a 0 + 1, 2 * ids.getD j 0))))

/-- Super-source arcs into the source representatives. -/
def srcArcsL (ids : List ℕ) : List (ℕ × ℕ) :=
  dedupList (((List.range g.base.nodes.length).filter g.isSrcNode).map
    (fun j => (g.netS, 2 * ids.getD j 0)))

/-- Super-sink arcs out of the output representatives. -/
def snkArcsL (ids : List ℕ) : List (ℕ × ℕ) :=
  dedupList (g.outNodes.map (fun j => (2 * ids.getD j 0 + 1, g.netT)))

/-- The split network. -/
def networkL (ids : List ℕ) : Network ℕ :=
  ⟨g.netNodesL ids, g.nodeArcsL ids ++ g.edgeArcsL ids ++ g.srcArcsL ids ++ g.snkArcsL ids,
    g.netS, g.netT⟩

/-- **Polynomial-time `ρ`**: the value of the maximum flow of the split network. -/
def rhoFlowL (ids : List ℕ) : ℕ :=
  ((g.networkL ids).maxflow.filter (fun a => a.1 == g.netS)).length

/-- **The polynomial-time decision.**  Written with nested `if` (not `&&`) so that the
evaluation order is explicit and no laziness of `&&` is assumed: the degree test, then
validation, then — only on valid inputs — the identifier table is computed once (`let`) and
shared by the test scan and the flow computation, which runs only when the tests are
distinct. -/
def strictDecideP (k : ℕ) : Bool :=
  if 2 ≤ k then
    if g.isValid then
      let ids := g.base.canonIds
      if g.base.testsDistinct ids then decide (k + 1 ≤ g.rhoFlowL ids) else false
    else false
  else false

/-- Canonical identifier of node `j`. -/
def repOf (j : ℕ) : ℕ := g.base.canonIds.getD j 0

def reps : List ℕ := g.repsL g.base.canonIds
def netNodes : List ℕ := g.netNodesL g.base.canonIds
def nodeArcs : List (ℕ × ℕ) := g.nodeArcsL g.base.canonIds
def edgeArcs : List (ℕ × ℕ) := g.edgeArcsL g.base.canonIds
def srcArcs : List (ℕ × ℕ) := g.srcArcsL g.base.canonIds
def snkArcs : List (ℕ × ℕ) := g.snkArcsL g.base.canonIds
def network : Network ℕ := g.networkL g.base.canonIds
def rhoFlow : ℕ := g.rhoFlowL g.base.canonIds

/-- The guarded decision agrees with the Boolean conjunction. -/
theorem strictDecideP_def (k : ℕ) : g.strictDecideP k =
    (decide (2 ≤ k) && g.isValid && g.base.testsDistinct g.base.canonIds &&
      decide (k + 1 ≤ g.rhoFlow)) := by
  unfold strictDecideP
  by_cases hk : 2 ≤ k
  · rw [if_pos hk]
    cases hv : g.isValid
    · simp
    · simp only [if_true]
      cases ht : g.base.testsDistinct g.base.canonIds
      · simp
      · simp [hk, rhoFlow]
  · rw [if_neg hk]; simp [hk]

theorem network_arcs : g.network.arcs = g.nodeArcs ++ g.edgeArcs ++ g.srcArcs ++ g.snkArcs := rfl
theorem network_nodes : g.network.nodes = g.netNodes := rfl

/-! ### Representatives -/

section valid
variable (hv : g.Valid)
include hv

theorem repOf_eq (j : ℕ) (hj : j < g.base.nodes.length) :
    g.repOf j = g.base.rep (g.baseValid hv) j :=
  g.base.canonIds_getD (g.baseValid hv) j hj

theorem repOf_lt (j : ℕ) (hj : j < g.base.nodes.length) : g.repOf j < g.base.nodes.length := by
  rw [g.repOf_eq hv j hj]
  exact lt_of_le_of_lt (g.base.rep_le _ j) hj

theorem repOf_le (j : ℕ) (hj : j < g.base.nodes.length) : g.repOf j ≤ j := by
  rw [g.repOf_eq hv j hj]
  exact g.base.rep_le _ j

theorem repOf_repOf (j : ℕ) (hj : j < g.base.nodes.length) : g.repOf (g.repOf j) = g.repOf j := by
  rw [g.repOf_eq hv _ (g.repOf_lt hv j hj), g.repOf_eq hv j hj]
  exact g.base.rep_rep _ j

theorem termD_repOf (j : ℕ) (hj : j < g.base.nodes.length) :
    g.base.termD (g.baseValid hv) (g.repOf j) = g.base.termD (g.baseValid hv) j := by
  rw [g.repOf_eq hv j hj]
  exact (g.base.rep_spec _ j).2

theorem repOf_eq_iff (i j : ℕ) (hi : i < g.base.nodes.length) (hj : j < g.base.nodes.length) :
    g.repOf i = g.repOf j ↔ g.base.termD (g.baseValid hv) i = g.base.termD (g.baseValid hv) j :=
  g.base.canonIds_eq_iff (g.baseValid hv) i j hi hj

omit hv in
theorem mem_reps (r : ℕ) : r ∈ g.reps ↔ r < g.base.nodes.length ∧ g.repOf r = r := by
  simp [reps, repsL, repOf]

theorem repOf_mem_reps (j : ℕ) (hj : j < g.base.nodes.length) : g.repOf j ∈ g.reps :=
  (g.mem_reps _).mpr ⟨g.repOf_lt hv j hj, g.repOf_repOf hv j hj⟩

omit hv in
theorem reps_nodup : g.reps.Nodup := List.Nodup.filter _ List.nodup_range

omit hv in
theorem reps_lt (r : ℕ) (hr : r ∈ g.reps) : r < g.base.nodes.length := ((g.mem_reps r).mp hr).1

omit hv in
theorem mem_nodeArcs (e : ℕ × ℕ) : e ∈ g.nodeArcs ↔ ∃ r ∈ g.reps, e = (2 * r, 2 * r + 1) := by
  simp only [nodeArcs, nodeArcsL, reps, List.mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩

omit hv in
theorem mem_edgeArcs (e : ℕ × ℕ) : e ∈ g.edgeArcs ↔
    ∃ j, j < g.base.nodes.length ∧ ∃ a ∈ g.argsOf j, e = (2 * g.repOf a + 1, 2 * g.repOf j) := by
  rw [edgeArcs, edgeArcsL, ← List.mem_toFinset, dedupList_toFinset, List.mem_toFinset,
    List.mem_flatMap]
  simp only [List.mem_range, List.mem_map, repOf]
  constructor
  · rintro ⟨j, hj, a, ha, rfl⟩; exact ⟨j, hj, a, ha, rfl⟩
  · rintro ⟨j, hj, a, ha, rfl⟩; exact ⟨j, hj, a, ha, rfl⟩

omit hv in
theorem mem_srcArcs (e : ℕ × ℕ) : e ∈ g.srcArcs ↔
    ∃ j, j < g.base.nodes.length ∧ g.isSrcNode j = true ∧ e = (g.netS, 2 * g.repOf j) := by
  rw [srcArcs, srcArcsL, ← List.mem_toFinset, dedupList_toFinset, List.mem_toFinset,
    List.mem_map]
  simp only [List.mem_filter, List.mem_range, repOf]
  constructor
  · rintro ⟨j, ⟨hj, hs⟩, rfl⟩; exact ⟨j, hj, hs, rfl⟩
  · rintro ⟨j, hj, hs, rfl⟩; exact ⟨j, ⟨hj, hs⟩, rfl⟩

omit hv in
theorem mem_snkArcs (e : ℕ × ℕ) : e ∈ g.snkArcs ↔
    ∃ j ∈ g.outNodes, e = (2 * g.repOf j + 1, g.netT) := by
  rw [snkArcs, snkArcsL, ← List.mem_toFinset, dedupList_toFinset, List.mem_toFinset,
    List.mem_map]
  simp only [repOf]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

omit hv in
/-- Shapes of the arcs. -/
theorem mem_arcs_iff (e : ℕ × ℕ) :
    e ∈ g.network.arcs ↔
      (∃ r ∈ g.reps, e = (2 * r, 2 * r + 1)) ∨
      (∃ j, j < g.base.nodes.length ∧ ∃ a ∈ g.argsOf j, e = (2 * g.repOf a + 1, 2 * g.repOf j)) ∨
      (∃ j, j < g.base.nodes.length ∧ g.isSrcNode j = true ∧ e = (g.netS, 2 * g.repOf j)) ∨
      (∃ j ∈ g.outNodes, e = (2 * g.repOf j + 1, g.netT)) := by
  show e ∈ g.nodeArcs ++ g.edgeArcs ++ g.srcArcs ++ g.snkArcs ↔ _
  simp only [List.mem_append, g.mem_nodeArcs, g.mem_edgeArcs, g.mem_srcArcs, g.mem_snkArcs,
    or_assoc]

omit hv in
theorem mem_netNodes (v : ℕ) :
    v ∈ g.network.nodes ↔ (∃ r ∈ g.reps, v = 2 * r) ∨ (∃ r ∈ g.reps, v = 2 * r + 1) ∨
      v = g.netS ∨ v = g.netT := by
  show v ∈ (g.repsL g.base.canonIds).map (fun r => 2 * r) ++
    (g.repsL g.base.canonIds).map (fun r => 2 * r + 1) ++ [g.netS, g.netT] ↔ _
  have hr : g.repsL g.base.canonIds = g.reps := rfl
  rw [hr]
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | h | h)
    · exact Or.inl ⟨r, hr, rfl⟩
    · exact Or.inr (Or.inl ⟨r, hr, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | h | h)
    · exact Or.inl (Or.inl ⟨r, hr, rfl⟩)
    · exact Or.inl (Or.inr ⟨r, hr, rfl⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- Arguments of a node are earlier nodes. -/
theorem argsOf_lt (j : ℕ) (hj : j < g.base.nodes.length) : ∀ a ∈ g.argsOf j, a < j := by
  unfold argsOf
  rw [List.getD_eq_getElem _ _ hj]
  cases hnd : g.base.nodes[j] with
  | src i => simp
  | app f args =>
      obtain ⟨_, _, hargs, _⟩ := g.base.decode_app (g.baseValid hv) j f args hj hnd
      exact hargs

/-- An argument decodes to an immediate argument of the node's term. -/
theorem argsOf_isArg (j : ℕ) (hj : j < g.base.nodes.length) (a : ℕ) (ha : a ∈ g.argsOf j) :
    IsArg (g.base.termD (g.baseValid hv) a) (g.base.termD (g.baseValid hv) j) := by
  unfold argsOf at ha
  rw [List.getD_eq_getElem _ _ hj] at ha
  cases hnd : g.base.nodes[j] with
  | src i => rw [hnd] at ha; simp at ha
  | app f args =>
      rw [hnd] at ha
      have ha' : a ∈ args := ha
      obtain ⟨hf, hlen, _, hta⟩ := g.base.decode_app (g.baseValid hv) j f args hj hnd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha'
      rw [hta]
      refine ⟨⟨f, hf⟩, _, ⟨i, by omega⟩, rfl, ?_⟩
      simp [List.getElem?_eq_getElem hi]

/-- Argument representatives differ from the node's representative. -/
theorem repOf_arg_ne (j : ℕ) (hj : j < g.base.nodes.length) (a : ℕ) (ha : a ∈ g.argsOf j) :
    g.repOf a ≠ g.repOf j := by
  intro h
  rw [g.repOf_eq_iff hv a j (lt_trans (g.argsOf_lt hv j hj a ha) hj) hj] at h
  have := isArg_size_lt (g.argsOf_isArg hv j hj a ha)
  rw [h] at this
  exact lt_irrefl _ this

/-- A source node decodes to a variable, and conversely. -/
theorem isSrcNode_iff (j : ℕ) (hj : j < g.base.nodes.length) :
    g.isSrcNode j = true ↔ ∃ v, g.base.termD (g.baseValid hv) j = .var v := by
  unfold isSrcNode
  rw [List.getD_eq_getElem _ _ hj]
  cases hnd : g.base.nodes[j] with
  | src i =>
      obtain ⟨hi, hta⟩ := g.base.decode_src (g.baseValid hv) j i hj hnd
      simp [hta]
  | app f args =>
      obtain ⟨_, _, _, hta⟩ := g.base.decode_app (g.baseValid hv) j f args hj hnd
      simp [hta]

/-- An `app` node decodes to an application whose arguments are the decoded `argsOf`. -/
theorem argsOf_app (j : ℕ) (hj : j < g.base.nodes.length) (hs : g.isSrcNode j = false) :
    ∃ (f : Fin g.base.m) (_ : (g.argsOf j).length = g.base.arity f),
      g.base.termD (g.baseValid hv) j =
        .app f (fun i => g.base.termD (g.baseValid hv) ((g.argsOf j).getD i.1 0)) := by
  unfold isSrcNode at hs
  unfold argsOf
  rw [List.getD_eq_getElem _ _ hj] at hs ⊢
  cases hnd : g.base.nodes[j] with
  | src i => rw [hnd] at hs; simp at hs
  | app f args =>
      obtain ⟨hf, hlen, _, hta⟩ := g.base.decode_app (g.baseValid hv) j f args hj hnd
      exact ⟨⟨f, hf⟩, hlen, hta⟩

theorem network_ok : g.network.Ok := by
  have hN : ∀ r ∈ g.reps, r < g.base.nodes.length := g.reps_lt
  have hrep : ∀ j, j < g.base.nodes.length → g.repOf j < g.base.nodes.length := g.repOf_lt hv
  have hS : g.network.s = g.netS := rfl
  have hT : g.network.t = g.netT := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nodes nodup
    show (g.reps.map (fun r => 2 * r) ++ g.reps.map (fun r => 2 * r + 1) ++
      [g.netS, g.netT]).Nodup
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨g.reps_nodup.map (fun a b h => by omega),
      g.reps_nodup.map (fun a b h => by omega), ?_⟩, by simp [netS, netT], ?_⟩
    · intro a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨r, _, rfl⟩ := ha
      obtain ⟨r', _, rfl⟩ := hb
      omega
    · intro a ha b hb
      simp only [List.mem_append, List.mem_map] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false, netS, netT] at hb
      rcases ha with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> have := hN r hr <;> omega
  · -- arcs nodup
    show (g.nodeArcs ++ g.edgeArcs ++ g.srcArcs ++ g.snkArcs).Nodup
    have h1 : g.nodeArcs.Nodup := g.reps_nodup.map (fun a b h => by
      simp only [Prod.mk.injEq] at h; omega)
    have h2 : g.edgeArcs.Nodup := dedupList_nodup _
    have h3 : g.srcArcs.Nodup := dedupList_nodup _
    have h4 : g.snkArcs.Nodup := dedupList_nodup _
    have e1 : ∀ e ∈ g.nodeArcs, e.1 % 2 = 0 ∧ e.2 = e.1 + 1 ∧ e.1 < 2 * g.base.nodes.length := by
      intro e he
      rw [g.mem_nodeArcs] at he
      obtain ⟨r, hr, rfl⟩ := he
      have := hN r hr
      dsimp only; omega
    have e2 : ∀ e ∈ g.edgeArcs, e.1 % 2 = 1 ∧ e.2 % 2 = 0 ∧ e.2 < 2 * g.base.nodes.length := by
      intro e he
      rw [g.mem_edgeArcs] at he
      obtain ⟨j, hj, a, _, rfl⟩ := he
      have := hrep j hj
      dsimp only; omega
    have e3 : ∀ e ∈ g.srcArcs, e.1 = 2 * g.base.nodes.length ∧ e.2 % 2 = 0 ∧
        e.2 < 2 * g.base.nodes.length := by
      intro e he
      rw [g.mem_srcArcs] at he
      obtain ⟨j, hj, _, rfl⟩ := he
      have := hrep j hj
      dsimp only [netS]; omega
    have e4 : ∀ e ∈ g.snkArcs, e.1 % 2 = 1 ∧ e.2 = 2 * g.base.nodes.length + 1 := by
      intro e he
      rw [g.mem_snkArcs] at he
      obtain ⟨j, _, rfl⟩ := he
      dsimp only [netT]; omega
    rw [List.nodup_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨⟨h1, h2, ?_⟩, h3, ?_⟩, h4, ?_⟩
    · intro a ha b hb hab; subst hab
      obtain ⟨p1, p2, p3⟩ := e1 a ha; obtain ⟨q1, q2, q3⟩ := e2 a hb; omega
    · intro a ha b hb hab; subst hab
      rw [List.mem_append] at ha
      obtain ⟨q1, q2, q3⟩ := e3 a hb
      rcases ha with ha | ha
      · obtain ⟨p1, p2, p3⟩ := e1 a ha; omega
      · obtain ⟨p1, p2, p3⟩ := e2 a ha; omega
    · intro a ha b hb hab; subst hab
      rw [List.mem_append, List.mem_append] at ha
      obtain ⟨q1, q2⟩ := e4 a hb
      rcases ha with (ha | ha) | ha
      · obtain ⟨p1, p2, p3⟩ := e1 a ha; omega
      · obtain ⟨p1, p2, p3⟩ := e2 a ha; omega
      · obtain ⟨p1, p2, p3⟩ := e3 a ha; omega
  · show g.netS ≠ g.netT
    simp [netS, netT]
  · show g.netS ∈ g.network.nodes
    rw [g.mem_netNodes]; simp
  · show g.netT ∈ g.network.nodes
    rw [g.mem_netNodes]; simp
  · -- arcs_mem
    intro e he
    rw [g.mem_arcs_iff] at he
    rw [hS, hT] at *
    simp only [g.mem_netNodes]
    rcases he with ⟨r, hr, rfl⟩ | ⟨j, hj, a, ha, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨Or.inl ⟨r, hr, rfl⟩, Or.inr (Or.inl ⟨r, hr, rfl⟩)⟩
    · have ha' : a < g.base.nodes.length := lt_trans (g.argsOf_lt hv j hj a ha) hj
      exact ⟨Or.inr (Or.inl ⟨_, g.repOf_mem_reps hv a ha', rfl⟩),
        Or.inl ⟨_, g.repOf_mem_reps hv j hj, rfl⟩⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inl ⟨_, g.repOf_mem_reps hv j hj, rfl⟩⟩
    · exact ⟨Or.inr (Or.inl ⟨_, g.repOf_mem_reps hv j (g.outNodes_lt hv j hj), rfl⟩),
        Or.inr (Or.inr (Or.inr rfl))⟩
  · -- no antiparallel arcs
    intro e he hanti
    rw [g.mem_arcs_iff] at he hanti
    simp only [netS, netT, Prod.mk.injEq] at he hanti
    rcases he with ⟨r, hr, rfl⟩ | ⟨j, hj, a, ha, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨j, hj, rfl⟩
    · have := hN r hr
      rcases hanti with ⟨r', hr', h⟩ | ⟨j', hj', a', ha', h⟩ | ⟨j', hj', _, h⟩ | ⟨j', hj', h⟩
      · omega
      · have hne := g.repOf_arg_ne hv j' hj' a' ha'
        have := hrep j' hj'
        omega
      · omega
      · have := hrep j' (g.outNodes_lt hv j' hj'); omega
    · have hne := g.repOf_arg_ne hv j hj a ha
      have := hrep j hj
      have := hrep a (lt_trans (g.argsOf_lt hv j hj a ha) hj)
      rcases hanti with ⟨r', hr', h⟩ | ⟨j', hj', a', ha', h⟩ | ⟨j', hj', _, h⟩ | ⟨j', hj', h⟩
      · omega
      · have := hrep j' hj'; omega
      · omega
      · have := hrep j' (g.outNodes_lt hv j' hj'); omega
    · have := hrep j hj
      rcases hanti with ⟨r', hr', h⟩ | ⟨j', hj', a', ha', h⟩ | ⟨j', hj', _, h⟩ | ⟨j', hj', h⟩
      · omega
      · have := hrep j' hj'; omega
      · have := hrep j' hj'; omega
      · omega
    · have := hrep j (g.outNodes_lt hv j hj)
      rcases hanti with ⟨r', hr', h⟩ | ⟨j', hj', a', ha', h⟩ | ⟨j', hj', _, h⟩ | ⟨j', hj', h⟩
      · have := hN r' hr'; omega
      · have := hrep a' (lt_trans (g.argsOf_lt hv j' hj' a' ha') hj'); omega
      · omega
      · have := hrep j' (g.outNodes_lt hv j' hj'); omega
  · -- nothing into s
    intro e he
    rw [g.mem_arcs_iff] at he
    rw [hS]
    simp only [netS, netT] at he ⊢
    rcases he with ⟨r, hr, rfl⟩ | ⟨j, hj, a, ha, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨j, hj, rfl⟩
    · have := hN r hr; simp; omega
    · have := hrep j hj; simp; omega
    · have := hrep j hj; simp; omega
    · simp
  · -- nothing out of t
    intro e he
    rw [g.mem_arcs_iff] at he
    rw [hT]
    simp only [netS, netT] at he ⊢
    rcases he with ⟨r, hr, rfl⟩ | ⟨j, hj, a, ha, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨j, hj, rfl⟩
    · have := hN r hr; simp; omega
    · have := hrep a (lt_trans (g.argsOf_lt hv j hj a ha) hj); simp; omega
    · simp
    · have := hrep j (g.outNodes_lt hv j hj); simp; omega


/-! ### From a term cut to a network cut -/

/-- "Pre-avoidance": a variable, or an application with an argument avoiding `K`. -/
def Pre (K : Finset g.base.Tm) (t : g.base.Tm) : Prop :=
  (∃ v, t = .var v) ∨ (∃ f ts, t = .app f ts ∧ ∃ i, Avoids K (ts i))

omit hv in
theorem mem_of_pre_not_avoids (K : Finset g.base.Tm) (t : g.base.Tm) (hp : g.Pre K t)
    (ha : ¬ Avoids K t) : t ∈ K := by
  rcases hp with ⟨v, rfl⟩ | ⟨f, ts, rfl, i, hi⟩
  · by_contra h
    exact ha (Avoids.var v h)
  · by_contra h
    exact ha (Avoids.app f ts h i hi)

open Classical in
/-- The network cut induced by a term cut: `s`, the entry copies of pre-avoiding
representatives and the exit copies of avoiding representatives. -/
noncomputable def cutSet (K : Finset g.base.Tm) : Finset ℕ :=
  g.network.nodes.toFinset.filter (fun v => v = g.netS ∨
    (v / 2 < g.base.nodes.length ∧
      ((v % 2 = 0 ∧ g.Pre K (g.base.termD (g.baseValid hv) (v / 2))) ∨
       (v % 2 = 1 ∧ Avoids K (g.base.termD (g.baseValid hv) (v / 2))))))

open Classical in
theorem mem_cutSet (K : Finset g.base.Tm) (v : ℕ) :
    v ∈ g.cutSet hv K ↔ v ∈ g.network.nodes ∧ (v = g.netS ∨
      (v / 2 < g.base.nodes.length ∧
        ((v % 2 = 0 ∧ g.Pre K (g.base.termD (g.baseValid hv) (v / 2))) ∨
         (v % 2 = 1 ∧ Avoids K (g.base.termD (g.baseValid hv) (v / 2)))))) := by
  unfold cutSet
  rw [Finset.mem_filter, List.mem_toFinset]

theorem s_mem_cutSet (K : Finset g.base.Tm) : g.netS ∈ g.cutSet hv K := by
  rw [g.mem_cutSet]
  exact ⟨(g.network_ok hv).s_mem, Or.inl rfl⟩

theorem t_notMem_cutSet (K : Finset g.base.Tm) : g.netT ∉ g.cutSet hv K := by
  rw [g.mem_cutSet]
  rintro ⟨_, h | ⟨h, _⟩⟩
  · simp [netS, netT] at h
  · simp only [netT] at h; omega

theorem entry_mem_cutSet (K : Finset g.base.Tm) (j : ℕ) (hj : j < g.base.nodes.length)
    (hp : g.Pre K (g.base.termD (g.baseValid hv) j)) : 2 * g.repOf j ∈ g.cutSet hv K := by
  rw [g.mem_cutSet]
  refine ⟨(g.mem_netNodes _).mpr (Or.inl ⟨_, g.repOf_mem_reps hv j hj, rfl⟩),
    Or.inr ⟨?_, Or.inl ⟨by omega, ?_⟩⟩⟩
  · have := g.repOf_lt hv j hj; omega
  · have e : 2 * g.repOf j / 2 = g.repOf j := by omega
    rw [e, g.termD_repOf hv j hj]
    exact hp

theorem exit_mem_cutSet_iff (K : Finset g.base.Tm) (j : ℕ) (hj : j < g.base.nodes.length) :
    2 * g.repOf j + 1 ∈ g.cutSet hv K ↔ Avoids K (g.base.termD (g.baseValid hv) j) := by
  rw [g.mem_cutSet]
  have e : (2 * g.repOf j + 1) / 2 = g.repOf j := by omega
  have hlt := g.repOf_lt hv j hj
  constructor
  · rintro ⟨_, h | ⟨_, ⟨h, _⟩ | ⟨_, h⟩⟩⟩
    · simp only [netS] at h; omega
    · omega
    · rw [e, g.termD_repOf hv j hj] at h; exact h
  · intro h
    refine ⟨?_, Or.inr ⟨by omega, Or.inr ⟨by omega, by rw [e, g.termD_repOf hv j hj]; exact h⟩⟩⟩
    exact (g.mem_netNodes _).mpr (Or.inr (Or.inl ⟨_, g.repOf_mem_reps hv j hj, rfl⟩))

theorem entry_mem_cutSet_iff (K : Finset g.base.Tm) (j : ℕ) (hj : j < g.base.nodes.length) :
    2 * g.repOf j ∈ g.cutSet hv K ↔ g.Pre K (g.base.termD (g.baseValid hv) j) := by
  constructor
  · rw [g.mem_cutSet]
    have e : (2 * g.repOf j) / 2 = g.repOf j := by omega
    have hlt := g.repOf_lt hv j hj
    rintro ⟨_, h | ⟨_, ⟨_, h⟩ | ⟨h, _⟩⟩⟩
    · simp only [netS] at h; omega
    · rw [e, g.termD_repOf hv j hj] at h; exact h
    · omega
  · exact g.entry_mem_cutSet hv K j hj

/-- Arguments give pre-avoidance of the parent. -/
theorem pre_of_arg (K : Finset g.base.Tm) (j : ℕ) (hj : j < g.base.nodes.length) (a : ℕ)
    (ha : a ∈ g.argsOf j) (h : Avoids K (g.base.termD (g.baseValid hv) a)) :
    g.Pre K (g.base.termD (g.baseValid hv) j) := by
  obtain ⟨f, ts, i, hj', hi⟩ := g.argsOf_isArg hv j hj a ha
  exact Or.inr ⟨f, ts, hj', i, hi ▸ h⟩

theorem pre_of_src (K : Finset g.base.Tm) (j : ℕ) (hj : j < g.base.nodes.length)
    (hs : g.isSrcNode j = true) : g.Pre K (g.base.termD (g.baseValid hv) j) := by
  obtain ⟨v, hv'⟩ := (g.isSrcNode_iff hv j hj).mp hs
  exact Or.inl ⟨v, hv'⟩

/-- Only vertex arcs of cut representatives cross the induced network cut. -/
theorem crossing_cutSet (b : List ℕ) (hb : g.isCutB g.base.canonIds b = true) (e : ℕ × ℕ)
    (he : e ∈ g.network.arcs) (h1 : e.1 ∈ g.cutSet hv (g.termCut hv b))
    (h2 : e.2 ∉ g.cutSet hv (g.termCut hv b)) :
    ∃ r ∈ g.cutReps g.base.canonIds b, e = (2 * r, 2 * r + 1) := by
  set K := g.termCut hv b with hK
  rw [g.mem_arcs_iff] at he
  rcases he with ⟨r, hr, rfl⟩ | ⟨j, hj, a, ha, rfl⟩ | ⟨j, hj, hs, rfl⟩ | ⟨j, hj, rfl⟩
  · obtain ⟨hrN, hrr⟩ := (g.mem_reps r).mp hr
    refine ⟨r, ?_, rfl⟩
    have hr' : g.repOf r = r := hrr
    dsimp only at h1 h2
    rw [← hr', g.entry_mem_cutSet_iff hv K r hrN] at h1
    rw [← hr', g.exit_mem_cutSet_iff hv K r hrN] at h2
    have hmem := g.mem_of_pre_not_avoids K _ h1 h2
    rw [hK, g.mem_termCut_iff hv b r hrN] at hmem
    unfold cutB at hmem
    unfold cutReps
    simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hrN, hr', ?_⟩
    have : g.base.canonIds.getD r 0 = r := hr'
    rw [this] at hmem
    simpa using hmem
  · exfalso
    dsimp only at h1 h2
    have ha' : a < g.base.nodes.length := lt_trans (g.argsOf_lt hv j hj a ha) hj
    rw [g.exit_mem_cutSet_iff hv K a ha'] at h1
    exact h2 ((g.entry_mem_cutSet_iff hv K j hj).mpr (g.pre_of_arg hv K j hj a ha h1))
  · exfalso
    dsimp only at h2
    exact h2 ((g.entry_mem_cutSet_iff hv K j hj).mpr (g.pre_of_src hv K j hj hs))
  · exfalso
    dsimp only at h1
    rw [g.exit_mem_cutSet_iff hv K j (g.outNodes_lt hv j hj)] at h1
    have hcut := (g.isCutB_iff hv b).mp hb
    refine hcut _ ?_ h1
    rw [g.outputs_eq hv]
    exact List.mem_map.mpr ⟨j, hj, rfl⟩

/-- The induced network cut has capacity at most the number of cut representatives. -/
theorem cap_cutSet_le (b : List ℕ) (hb : g.isCutB g.base.canonIds b = true) :
    g.network.cap (g.cutSet hv (g.termCut hv b)) ≤ g.cutCard g.base.canonIds b := by
  unfold Network.cap cutCard
  have hnd : (g.cutReps g.base.canonIds b).Nodup := List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card_of_injOn (fun e => e.1 / 2)
  · intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq, List.mem_toFinset] at he
    obtain ⟨r, hr, rfl⟩ := g.crossing_cutSet hv b hb e he.1 he.2.1 he.2.2
    simp only [Finset.mem_coe, List.mem_toFinset]
    have : (2 * r, 2 * r + 1).1 / 2 = r := by dsimp only; omega
    rw [this]; exact hr
  · intro e he e' he' hee
    simp only [Finset.coe_filter, Set.mem_setOf_eq, List.mem_toFinset] at he he'
    obtain ⟨r, _, rfl⟩ := g.crossing_cutSet hv b hb e he.1 he.2.1 he.2.2
    obtain ⟨r', _, rfl⟩ := g.crossing_cutSet hv b hb e' he'.1 he'.2.1 he'.2.2
    simp only at hee
    have : r = r' := by omega
    subst this; rfl

/-- **Flow ≤ every cut vector.** -/
theorem value_le_cutCard (b : List ℕ) (hb : g.isCutB g.base.canonIds b = true) :
    g.network.value g.network.maxflow.toFinset ≤ g.cutCard g.base.canonIds b :=
  (g.network.value_le_cap (g.network_ok hv) (g.network.maxflow_spec (g.network_ok hv)).1.flow _
    (g.s_mem_cutSet hv _) (g.t_notMem_cutSet hv _)).trans (g.cap_cutSet_le hv b hb)


/-! ### From a network cut to a term cut -/

/-- The representative charged to a crossing arc. -/
def pickOf (e : ℕ × ℕ) : ℕ :=
  if e.2 = g.netT then e.1 / 2 else if e.1 % 2 = 0 ∧ e.1 ≠ g.netS then e.1 / 2 else e.2 / 2

/-- Representatives charged to the arcs leaving the node set `S`. -/
def picks (S : List ℕ) : List ℕ :=
  (g.network.arcs.filter (fun e => e.1 ∈ S ∧ e.2 ∉ S)).map g.pickOf

/-- The cut vector of a node set. -/
def vecOfCut (S : List ℕ) : List ℕ :=
  (List.range g.base.nodes.length).map (fun r => if r ∈ g.picks S then 1 else 0)

omit hv in
theorem vecOfCut_getD (S : List ℕ) (r : ℕ) (hr : r < g.base.nodes.length) :
    (g.vecOfCut S).getD r 0 = if r ∈ g.picks S then 1 else 0 := by
  unfold vecOfCut
  rw [List.getD_eq_getElem _ _ (by simpa using hr)]
  simp

theorem cutB_vecOfCut (S : List ℕ) (j : ℕ) (hj : j < g.base.nodes.length) :
    cutB g.base.canonIds (g.vecOfCut S) j = true ↔ g.repOf j ∈ g.picks S := by
  unfold cutB
  have : g.base.canonIds.getD j 0 = g.repOf j := rfl
  rw [this, g.vecOfCut_getD S _ (g.repOf_lt hv j hj)]
  split_ifs with h <;> simp [h]

/-- The cut count of the induced vector is at most the capacity of `S`. -/
theorem cutCard_vecOfCut_le (S : List ℕ) :
    g.cutCard g.base.canonIds (g.vecOfCut S) ≤ g.network.cap S.toFinset := by
  unfold cutCard Network.cap
  have hnd : (g.cutReps g.base.canonIds (g.vecOfCut S)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hsub : (g.cutReps g.base.canonIds (g.vecOfCut S)).toFinset ⊆ (g.picks S).toFinset := by
    intro r hr
    simp only [List.mem_toFinset, cutReps, List.mem_filter, List.mem_range, Bool.and_eq_true,
      beq_iff_eq] at hr
    obtain ⟨hrN, _, hbit⟩ := hr
    rw [g.vecOfCut_getD S r hrN] at hbit
    rw [List.mem_toFinset]
    by_contra h
    rw [if_neg h] at hbit
    exact absurd hbit (by decide)
  have hfilt : (g.network.arcs.filter (fun e => e.1 ∈ S ∧ e.2 ∉ S)).Nodup :=
    List.Nodup.filter _ (g.network_ok hv).arcs_nodup
  calc (g.cutReps g.base.canonIds (g.vecOfCut S)).length
      = (g.cutReps g.base.canonIds (g.vecOfCut S)).toFinset.card :=
        (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (g.picks S).toFinset.card := Finset.card_le_card hsub
    _ ≤ (g.picks S).length := List.toFinset_card_le _
    _ = (g.network.arcs.filter (fun e => e.1 ∈ S ∧ e.2 ∉ S)).length := by
        simp [picks]
    _ = (g.network.arcs.filter (fun e => e.1 ∈ S ∧ e.2 ∉ S)).toFinset.card :=
        (List.toFinset_card_of_nodup hfilt).symm
    _ = (g.network.arcs.toFinset.filter (fun e => e.1 ∈ S.toFinset ∧ e.2 ∉ S.toFinset)).card := by
        congr 1
        ext e
        simp

omit hv in
/-- A crossing arc charges its representative. -/
theorem pick_mem_picks (S : List ℕ) (e : ℕ × ℕ) (he : e ∈ g.network.arcs) (h1 : e.1 ∈ S)
    (h2 : e.2 ∉ S) : g.pickOf e ∈ g.picks S := by
  unfold picks
  rw [List.mem_map]
  exact ⟨e, List.mem_filter.mpr ⟨he, by simp [h1, h2]⟩, rfl⟩

/-- Avoiding the induced term cut forces the exit copy into `S`. -/
theorem exit_mem_of_avoids (S : List ℕ) (hs : g.netS ∈ S) :
    ∀ j, j < g.base.nodes.length →
      Avoids (g.termCut hv (g.vecOfCut S)) (g.base.termD (g.baseValid hv) j) →
      2 * g.repOf j + 1 ∈ S := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj ha
      have hnot : g.repOf j ∉ g.picks S := by
        intro h
        rw [← g.cutB_vecOfCut hv S j hj, ← g.mem_termCut_iff hv _ j hj] at h
        exact avoids_not_mem ha h
      have hlt := g.repOf_lt hv j hj
      -- step A: the entry copy is in `S`
      have hentry : 2 * g.repOf j ∈ S := by
        by_contra hno
        by_cases hsrc : g.isSrcNode j = true
        · have he : (g.netS, 2 * g.repOf j) ∈ g.network.arcs :=
            (g.mem_arcs_iff _).mpr (Or.inr (Or.inr (Or.inl ⟨j, hj, hsrc, rfl⟩)))
          have := g.pick_mem_picks S _ he hs hno
          unfold pickOf at this
          simp only [netS, netT] at this
          have e1 : ¬ (2 * g.repOf j = 2 * g.base.nodes.length + 1) := by omega
          have e2 : ¬ ((2 * g.base.nodes.length) % 2 = 0 ∧
              2 * g.base.nodes.length ≠ 2 * g.base.nodes.length) := by omega
          rw [if_neg e1, if_neg e2] at this
          have e3 : 2 * g.repOf j / 2 = g.repOf j := by omega
          rw [e3] at this
          exact hnot this
        · have hsrc' : g.isSrcNode j = false := by simpa using hsrc
          obtain ⟨f, hlen, hta⟩ := g.argsOf_app hv j hj hsrc'
          rw [hta] at ha
          cases ha with
          | app _ _ _ i hi =>
              have hi' : i.1 < (g.argsOf j).length := by rw [hlen]; exact i.2
              set a := (g.argsOf j).getD i.1 0 with hadef
              have hamem : a ∈ g.argsOf j := by
                rw [hadef, List.getD_eq_getElem _ _ hi']
                exact List.getElem_mem _
              have halt : a < j := g.argsOf_lt hv j hj a hamem
              have hexit := ih a halt (lt_trans halt hj) hi
              have he : (2 * g.repOf a + 1, 2 * g.repOf j) ∈ g.network.arcs :=
                (g.mem_arcs_iff _).mpr (Or.inr (Or.inl ⟨j, hj, a, hamem, rfl⟩))
              have := g.pick_mem_picks S _ he hexit hno
              unfold pickOf at this
              simp only [netS, netT] at this
              have e1 : ¬ (2 * g.repOf j = 2 * g.base.nodes.length + 1) := by omega
              have e2 : ¬ ((2 * g.repOf a + 1) % 2 = 0 ∧
                  2 * g.repOf a + 1 ≠ 2 * g.base.nodes.length) := by omega
              rw [if_neg e1, if_neg e2] at this
              have e3 : 2 * g.repOf j / 2 = g.repOf j := by omega
              rw [e3] at this
              exact hnot this
      -- step B: the vertex arc keeps the exit copy in `S`
      by_contra hno
      have he : (2 * g.repOf j, 2 * g.repOf j + 1) ∈ g.network.arcs :=
        (g.mem_arcs_iff _).mpr (Or.inl ⟨_, g.repOf_mem_reps hv j hj, rfl⟩)
      have := g.pick_mem_picks S _ he hentry hno
      unfold pickOf at this
      simp only [netS, netT] at this
      have e1 : ¬ (2 * g.repOf j + 1 = 2 * g.base.nodes.length + 1) := by omega
      have e2 : (2 * g.repOf j) % 2 = 0 ∧ 2 * g.repOf j ≠ 2 * g.base.nodes.length := by omega
      rw [if_neg e1, if_pos e2] at this
      have e3 : 2 * g.repOf j / 2 = g.repOf j := by omega
      rw [e3] at this
      exact hnot this

/-- **Every `s`–`t` node cut yields a cut vector.** -/
theorem isCutB_vecOfCut (S : List ℕ) (hs : g.netS ∈ S) (ht : g.netT ∉ S) :
    g.isCutB g.base.canonIds (g.vecOfCut S) = true := by
  rw [g.isCutB_iff hv]
  intro t ht' ha
  rw [g.outputs_eq hv] at ht'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht'
  have hjN := g.outNodes_lt hv j hj
  have hexit := g.exit_mem_of_avoids hv S hs j hjN ha
  have he : (2 * g.repOf j + 1, g.netT) ∈ g.network.arcs :=
    (g.mem_arcs_iff _).mpr (Or.inr (Or.inr (Or.inr ⟨j, hj, rfl⟩)))
  have := g.pick_mem_picks S _ he hexit ht
  unfold pickOf at this
  simp only [if_true] at this
  have e3 : (2 * g.repOf j + 1) / 2 = g.repOf j := by omega
  rw [e3, ← g.cutB_vecOfCut hv S j hjN, ← g.mem_termCut_iff hv _ j hjN] at this
  exact avoids_not_mem ha this

/-! ### The flow value is `ρ` -/

theorem rhoFlow_eq_value :
    g.rhoFlow = g.network.value g.network.maxflow.toFinset := by
  show ((g.network.maxflow.filter (fun a => a.1 == g.netS)).length) = _
  unfold Network.value Network.outdeg
  have hnd := (g.network.maxflow_spec (g.network_ok hv)).1.nodup
  rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter, List.mem_toFinset, beq_iff_eq]
  rfl

/-- **Correctness of the polynomial-time cut computation.** -/
theorem rhoFlow_eq : g.rhoFlow = cutSize (g.outputs hv) (g.tests hv) := by
  rw [g.rhoFlow_eq_value hv]
  apply le_antisymm
  · obtain ⟨K, _, hK, hc⟩ := exists_min_cut (g.outputs hv) (g.tests hv)
    rw [← hc]
    exact (g.value_le_cutCard hv _ (g.isCutB_vecOf hv K hK)).trans (g.cutCard_vecOf_le hv K)
  · obtain ⟨hg, ht, hs', ht', hv'⟩ := g.network.maxflow_spec (g.network_ok hv)
    have hs : g.netS ∈ g.network.seen g.network.maxflow := g.network.s_mem_seen _
    have hb := g.isCutB_vecOfCut hv _ hs ht
    rw [hv']
    exact (cutSize_le_card_of_isCut _ _ _ ((g.isCutB_iff hv _).mp hb)).trans
      ((g.termCut_card_le hv _).trans (g.cutCard_vecOfCut_le hv _))

end valid

/-! ### The polynomial-time decision -/

/-- `strictDecideP` agrees with the exhaustive decision on every input. -/
theorem strictDecideP_eq (k : ℕ) : g.strictDecideP k = g.strictDecideG k := by
  rw [g.strictDecideP_def]
  unfold strictDecideG
  by_cases hv : g.Valid
  · rw [g.rhoFlow_eq hv, ← g.rhoExec_eq hv]
  · have : g.isValid = false := Bool.eq_false_iff.mpr hv
    simp [this]

/-- **Exact correctness of the polynomial-time decision**, every degree `k ≥ 2`. -/
theorem strictDecideP_iff (k : ℕ) (hk : 2 ≤ k) : g.strictDecideP k = true ↔ g.Strict k := by
  rw [g.strictDecideP_eq]
  exact g.strictDecideG_iff k hk

theorem strictDecideP_of_invalid (k : ℕ) (h : ¬ g.Valid) : g.strictDecideP k = false := by
  rw [g.strictDecideP_eq]; exact g.strictDecideG_of_invalid k h

theorem strictDecideP_of_degree_lt (k : ℕ) (hk : k < 2) : g.strictDecideP k = false := by
  rw [g.strictDecideP_eq]; exact g.strictDecideG_of_degree_lt k hk

theorem primrec_strictDecideP : Primrec fun p : ℕ × GInstance => p.2.strictDecideP p.1 :=
  primrec_strictDecideG.of_eq (fun p => (p.2.strictDecideP_eq p.1).symm)

theorem computablePred_Strict_degree' (k : ℕ) (hk : 2 ≤ k) :
    ComputablePred (GInstance.Strict k) :=
  computablePred_Strict_degree k hk

end GInstance
end DisequalityDispersion.Encoded
