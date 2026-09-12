import TableSearch
import StrictAlgorithm
import TermMenger

/-! # The executable general decision (R5, items 1)

`strictDecideG k g` validates the encoded general instance, canonicalises the
node DAG, rejects identical-side tests, computes the minimum vertex cut `ρ`
between the output nodes and the source nodes by exhaustive enumeration of
cut candidates over the canonical node identifiers (`rhoExec`, proved equal to
`cutSize` of the decoded instance), and accepts iff `k + 1 ≤ ρ`.  It is false
on invalid inputs and on degrees below two, and it is exactly correct against
`Strict` in the general semantics (`strictDecideG_iff`).

`rhoExec` is exponential in the number of nodes (a computability certificate,
not the polynomial max-flow algorithm; see the return report). -/

namespace DisequalityDispersion.Encoded
namespace GInstance

variable (g : GInstance)

/-! ### Executable definitions -/

/-- Node index of the retained source `x` (the first `src x` node). -/
def xNode : ℕ := g.base.nodes.idxOf (.src g.base.x)
/-- Node index of the retained source `y`. -/
def yNode : ℕ := g.base.nodes.idxOf (.src g.base.y)
/-- All output node indices `(x, y, t₃, …)`. -/
def outNodes : List ℕ := [g.xNode, g.yNode] ++ g.outs

/-- Node `j` is cut by the bit vector `b` (read at its canonical identifier). -/
def cutB (ids b : List ℕ) (j : ℕ) : Bool := b.getD (ids.getD j 0) 0 == 1

/-- One step of the source-reachability computation avoiding the cut. -/
def avoidsStep (ids b : List ℕ) (vals : List Bool) (j : ℕ) : Bool :=
  !(cutB ids b j) && (match g.base.nodes.getD j (.src 0) with
    | .src _ => true
    | .app _ args => args.any (fun a => vals.getD a false))

/-- For every node: is some source reachable through the arguments avoiding the cut? -/
def avoidsDP (ids b : List ℕ) : List Bool := buildList (g.avoidsStep ids b) g.base.nodes.length

/-- The bit vector is a cut: no output node reaches a source. -/
def isCutB (ids b : List ℕ) : Bool :=
  g.outNodes.all (fun j => !((g.avoidsDP ids b).getD j false))

/-- The canonical representatives selected by the bit vector. -/
def cutReps (ids b : List ℕ) : List ℕ :=
  (List.range g.base.nodes.length).filter (fun j => ids.getD j 0 == j && b.getD j 0 == 1)

/-- Number of cut vertices (distinct terms). -/
def cutCard (ids b : List ℕ) : ℕ := (g.cutReps ids b).length

/-- Executable minimum cut size. -/
def rhoExec : ℕ :=
  let ids := g.base.canonIds
  (allLists 2 g.base.nodes.length).foldr
    (fun b acc => if g.isCutB ids b then min (g.cutCard ids b) acc else acc) g.base.nodes.length

/-- **The executable general decision.** -/
def strictDecideG (k : ℕ) : Bool :=
  decide (2 ≤ k) && g.isValid && g.base.testsDistinct g.base.canonIds && decide (k + 1 ≤ g.rhoExec)

/-! ### The output nodes -/

section outputs

theorem src_x_mem (hv : g.Valid) : (Node.src g.base.x) ∈ g.base.nodes := by
  have hb := g.baseValid hv
  have hg := (g.base.valid_iff.mp hb).2.2.2.2.2.2.2.2.2
  have htests := (g.base.valid_iff.mp hb).2.2.2.2.2.2.2.2.1
  unfold Instance.guardOk at hg
  rw [List.any_eq_true] at hg
  obtain ⟨ij, hij, h⟩ := hg
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  rw [List.getD_eq_getElem _ _ (htests ij hij).1] at h
  rw [← h.1]
  exact List.getElem_mem _

theorem src_y_mem (hv : g.Valid) : (Node.src g.base.y) ∈ g.base.nodes := by
  have hb := g.baseValid hv
  have hg := (g.base.valid_iff.mp hb).2.2.2.2.2.2.2.2.2
  have htests := (g.base.valid_iff.mp hb).2.2.2.2.2.2.2.2.1
  unfold Instance.guardOk at hg
  rw [List.any_eq_true] at hg
  obtain ⟨ij, hij, h⟩ := hg
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  rw [List.getD_eq_getElem _ _ (htests ij hij).2] at h
  rw [← h.2]
  exact List.getElem_mem _

theorem xNode_lt (hv : g.Valid) : g.xNode < g.base.nodes.length :=
  List.idxOf_lt_length_iff.mpr (g.src_x_mem hv)

theorem yNode_lt (hv : g.Valid) : g.yNode < g.base.nodes.length :=
  List.idxOf_lt_length_iff.mpr (g.src_y_mem hv)

theorem termD_xNode (hv : g.Valid) : g.base.termD (g.baseValid hv) g.xNode = .var (g.base.xv (g.baseValid hv)) := by
  obtain ⟨_, h⟩ := g.base.decode_src (g.baseValid hv) g.xNode g.base.x (g.xNode_lt hv)
    (List.getElem_idxOf (g.xNode_lt hv))
  rw [h]; rfl

theorem termD_yNode (hv : g.Valid) : g.base.termD (g.baseValid hv) g.yNode = .var (g.base.yv (g.baseValid hv)) := by
  obtain ⟨_, h⟩ := g.base.decode_src (g.baseValid hv) g.yNode g.base.y (g.yNode_lt hv)
    (List.getElem_idxOf (g.yNode_lt hv))
  rw [h]; rfl

theorem outputs_eq (hv : g.Valid) : g.outputs hv = g.outNodes.map (g.base.termD (g.baseValid hv)) := by
  unfold outputs outNodes
  simp only [List.map_append, List.map_cons, List.map_nil, g.termD_xNode hv, g.termD_yNode hv]

theorem outNodes_lt (hv : g.Valid) : ∀ j ∈ g.outNodes, j < g.base.nodes.length := by
  intro j hj
  simp only [outNodes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with (rfl | rfl) | hj
  · exact g.xNode_lt hv
  · exact g.yNode_lt hv
  · exact (g.valid_iff.mp hv).2 j hj

end outputs

theorem avoids_not_mem {V F : Type} {arity : F → ℕ} {K : Finset (Term V F arity)}
    {t : Term V F arity} (h : Avoids K t) : t ∉ K := by
  cases h <;> assumption

/-! ### Cut vectors and term cuts -/

section cuts
open Classical
variable (hv : g.Valid) (b : List ℕ)

/-- The term cut named by a bit vector. -/
noncomputable def termCut : Finset (g.base.Tm) :=
  ((List.range g.base.nodes.length).filter (fun j => cutB g.base.canonIds b j)).toFinset.image (g.base.termD (g.baseValid hv))

theorem cutB_congr (i j : ℕ) (hi : i < g.base.nodes.length) (hj : j < g.base.nodes.length) (h : g.base.termD (g.baseValid hv) i = g.base.termD (g.baseValid hv) j) :
    cutB g.base.canonIds b i = cutB g.base.canonIds b j := by
  unfold cutB
  rw [(g.base.canonIds_eq_iff (g.baseValid hv) i j hi hj).mpr h]

theorem mem_termCut_iff (j : ℕ) (hj : j < g.base.nodes.length) :
    g.base.termD (g.baseValid hv) j ∈ g.termCut hv b ↔ cutB g.base.canonIds b j = true := by
  unfold termCut
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hc⟩, he⟩
    rw [← g.cutB_congr hv b i j hi hj he]
    exact hc
  · intro h
    exact ⟨j, ⟨hj, h⟩, rfl⟩

/-- The reachability table computes `Avoids` for the term cut. -/
theorem avoidsDP_iff : ∀ j, j < g.base.nodes.length →
    ((g.avoidsDP g.base.canonIds b).getD j false = true ↔ Avoids (g.termCut hv b) (g.base.termD (g.baseValid hv) j)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj
      unfold avoidsDP
      rw [buildList_getD _ _ _ hj]
      unfold avoidsStep
      rw [List.getD_eq_getElem _ _ hj]
      cases hnd : g.base.nodes[j] with
      | src i =>
          obtain ⟨hi, hta⟩ := g.base.decode_src (g.baseValid hv) j i hj hnd
          have hmem := g.mem_termCut_iff hv b j hj
          rw [hta] at hmem
          rw [hta, avoids_var_iff, hmem]
          simp
      | app f args =>
          obtain ⟨hf, hlen, hargs, hta⟩ := g.base.decode_app (g.baseValid hv) j f args hj hnd
          have hmem := g.mem_termCut_iff hv b j hj
          constructor
          · intro h
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              List.any_eq_true] at h
            obtain ⟨hc, a, ha, hDP⟩ := h
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
            have hnotin : g.base.termD (g.baseValid hv) j ∉ g.termCut hv b := by
              rw [hmem]; simp [hc]
            rw [hta] at hnotin ⊢
            refine Avoids.app _ _ hnotin ⟨i, by omega⟩ ?_
            have hDP' : (g.avoidsDP g.base.canonIds b).getD args[i] false = true := by
              unfold avoidsDP
              rw [buildList_getD _ _ _ (lt_trans (hargs _ (List.getElem_mem hi)) hj)]
              rw [buildList_getD _ _ _ (hargs _ (List.getElem_mem hi))] at hDP
              exact hDP
            have := (ih _ (hargs _ (List.getElem_mem hi))
              (lt_trans (hargs _ (List.getElem_mem hi)) hj)).mp hDP'
            simp only [List.getD_eq_getElem _ _ hi]
            exact this
          · intro h
            rw [hta] at h
            cases h with
            | app _ _ hn i hi =>
                rw [← hta, hmem] at hn
                simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                  List.any_eq_true]
                refine ⟨by simpa using hn, args.getD i.1 0, ?_, ?_⟩
                · have hi' : i.1 < args.length := by rw [hlen]; exact i.2
                  rw [List.getD_eq_getElem _ _ hi']
                  exact List.getElem_mem _
                · have hlt : args.getD i.1 0 < j := by
                    have hi' : i.1 < args.length := by rw [hlen]; exact i.2
                    rw [List.getD_eq_getElem _ _ hi']
                    exact hargs _ (List.getElem_mem _)
                  have := (ih _ hlt (lt_trans hlt hj)).mpr hi
                  unfold avoidsDP at this
                  rw [buildList_getD _ _ _ (lt_trans hlt hj)] at this
                  rw [buildList_getD _ _ _ hlt]
                  exact this

theorem isCutB_iff : g.isCutB g.base.canonIds b = true ↔ IsCut (g.termCut hv b) (g.outputs hv) := by
  unfold isCutB IsCut
  rw [g.outputs_eq hv]
  simp only [List.all_eq_true, List.forall_mem_map, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro h j hj ha
    have := h j hj
    rw [← g.avoidsDP_iff hv b j (g.outNodes_lt hv j hj)] at ha
    rw [ha] at this
    exact absurd this (by decide)
  · intro h j hj
    have := h j hj
    rw [← g.avoidsDP_iff hv b j (g.outNodes_lt hv j hj)] at this
    simpa using this

/-- The term cut has at most `cutCard` elements. -/
theorem termCut_card_le : (g.termCut hv b).card ≤ g.cutCard g.base.canonIds b := by
  have hsub : g.termCut hv b ⊆ (g.cutReps g.base.canonIds b).toFinset.image (g.base.termD (g.baseValid hv)) := by
    intro t ht
    unfold termCut at ht
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_filter, List.mem_range] at ht
    obtain ⟨j, ⟨hj, hc⟩, rfl⟩ := ht
    simp only [Finset.mem_image, List.mem_toFinset, cutReps, List.mem_filter, List.mem_range,
      Bool.and_eq_true, beq_iff_eq]
    refine ⟨g.base.rep (g.baseValid hv) j, ⟨lt_of_le_of_lt (g.base.rep_le (g.baseValid hv) j) hj, ?_, ?_⟩, (g.base.rep_spec (g.baseValid hv) j).2⟩
    · rw [g.base.canonIds_getD (g.baseValid hv) _ (lt_of_le_of_lt (g.base.rep_le (g.baseValid hv) j) hj)]
      exact g.base.rep_rep (g.baseValid hv) j
    · unfold cutB at hc
      rw [g.base.canonIds_getD (g.baseValid hv) j hj] at hc
      simpa using hc
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (List.toFinset_card_le _))

/-- Every term cut yields a cut vector of no larger count. -/
noncomputable def vecOf (K : Finset (g.base.Tm)) : List ℕ :=
  (List.range g.base.nodes.length).map (fun j => if g.base.canonIds.getD j 0 = j ∧ g.base.termD (g.baseValid hv) j ∈ K then 1 else 0)

theorem vecOf_mem (K : Finset (g.base.Tm)) : g.vecOf hv K ∈ allLists 2 g.base.nodes.length := by
  rw [mem_allLists]
  refine ⟨by simp [vecOf], ?_⟩
  intro v hv'
  simp only [vecOf, List.mem_map] at hv'
  obtain ⟨j, _, rfl⟩ := hv'
  split_ifs <;> omega

theorem vecOf_getD (K : Finset (g.base.Tm)) (j : ℕ) (hj : j < g.base.nodes.length) :
    (g.vecOf hv K).getD j 0 = if g.base.canonIds.getD j 0 = j ∧ g.base.termD (g.baseValid hv) j ∈ K then 1 else 0 := by
  unfold vecOf
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem cutB_vecOf (K : Finset (g.base.Tm)) (j : ℕ) (hj : j < g.base.nodes.length) :
    cutB g.base.canonIds (g.vecOf hv K) j = true ↔ g.base.termD (g.baseValid hv) j ∈ K := by
  unfold cutB
  rw [g.base.canonIds_getD (g.baseValid hv) j hj, g.vecOf_getD hv K _ (lt_of_le_of_lt (g.base.rep_le (g.baseValid hv) j) hj),
    g.base.canonIds_getD (g.baseValid hv) _ (lt_of_le_of_lt (g.base.rep_le (g.baseValid hv) j) hj), g.base.rep_rep (g.baseValid hv) j, (g.base.rep_spec (g.baseValid hv) j).2]
  simp

/-- On decoded terms, avoiding the vector cut of `K` is avoiding `K`. -/
theorem avoids_vecOf (K : Finset (g.base.Tm)) : ∀ j, j < g.base.nodes.length →
    Avoids (g.termCut hv (g.vecOf hv K)) (g.base.termD (g.baseValid hv) j) → Avoids K (g.base.termD (g.baseValid hv) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      intro hj h
      have hmem := g.mem_termCut_iff hv (g.vecOf hv K) j hj
      rw [g.cutB_vecOf hv K j hj] at hmem
      cases hnd : g.base.nodes[j] with
      | src i =>
          obtain ⟨hi, hta⟩ := g.base.decode_src (g.baseValid hv) j i hj hnd
          rw [hta] at h hmem ⊢
          rw [avoids_var_iff] at h ⊢
          rw [← hmem]; exact h
      | app f args =>
          obtain ⟨hf, hlen, hargs, hta⟩ := g.base.decode_app (g.baseValid hv) j f args hj hnd
          rw [hta] at h hmem ⊢
          cases h with
          | app _ _ hn i hi =>
              refine Avoids.app _ _ (by rw [← hmem]; exact hn) i ?_
              have hi' : i.1 < args.length := by rw [hlen]; exact i.2
              have hlt : args.getD i.1 0 < j := by
                rw [List.getD_eq_getElem _ _ hi']
                exact hargs _ (List.getElem_mem _)
              exact ih _ hlt (lt_trans hlt hj) hi

theorem isCutB_vecOf (K : Finset (g.base.Tm)) (hK : IsCut K (g.outputs hv)) :
    g.isCutB g.base.canonIds (g.vecOf hv K) = true := by
  rw [g.isCutB_iff hv]
  intro t ht ha
  have ht' := ht
  rw [g.outputs_eq hv] at ht'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht'
  exact hK _ ht (g.avoids_vecOf hv K j (g.outNodes_lt hv j hj) ha)

theorem cutCard_vecOf_le (K : Finset (g.base.Tm)) : g.cutCard g.base.canonIds (g.vecOf hv K) ≤ K.card := by
  unfold cutCard
  have hnd : (g.cutReps g.base.canonIds (g.vecOf hv K)).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card_of_injOn (g.base.termD (g.baseValid hv))
  · intro j hj
    simp only [Finset.mem_coe, List.mem_toFinset, cutReps, List.mem_filter, List.mem_range,
      Bool.and_eq_true, beq_iff_eq] at hj
    obtain ⟨hjN, hrep, hbit⟩ := hj
    rw [g.vecOf_getD hv K j hjN] at hbit
    by_cases h : g.base.canonIds.getD j 0 = j ∧ g.base.termD (g.baseValid hv) j ∈ K
    · exact h.2
    · rw [if_neg h] at hbit
      exact absurd hbit (by decide)
  · intro i hi j hj he
    simp only [Finset.mem_coe, List.mem_toFinset, cutReps, List.mem_filter, List.mem_range,
      Bool.and_eq_true, beq_iff_eq] at hi hj
    have hri := hi.2.1
    have hrj := hj.2.1
    rw [g.base.canonIds_getD (g.baseValid hv) i hi.1] at hri
    rw [g.base.canonIds_getD (g.baseValid hv) j hj.1] at hrj
    rw [← hri, ← hrj]
    exact (g.base.rep_eq_iff (g.baseValid hv) i j).mpr he

/-! ### `rhoExec` computes `cutSize` -/

theorem foldr_min_le {β : Type} (l : List β) (p : β → Bool) (c : β → ℕ) (init : ℕ) (x : β)
    (hx : x ∈ l) (hp : p x = true) :
    l.foldr (fun y acc => if p y then min (c y) acc else acc) init ≤ c x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [if_pos hp]; exact min_le_left _ _
      · split_ifs
        · exact le_trans (min_le_right _ _) (ih hx)
        · exact ih hx

theorem le_foldr_min {β : Type} (l : List β) (p : β → Bool) (c : β → ℕ) (init m : ℕ)
    (hinit : m ≤ init) (h : ∀ x ∈ l, p x = true → m ≤ c x) :
    m ≤ l.foldr (fun y acc => if p y then min (c y) acc else acc) init := by
  induction l with
  | nil => exact hinit
  | cons y l ih =>
      simp only [List.foldr_cons]
      split_ifs with hp
      · exact le_min (h y List.mem_cons_self hp) (ih (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx))
      · exact ih (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)

/-- All decoded nodes form a cut, so `cutSize ≤ g.base.nodes.length`. -/
theorem cutSize_le_nodes : cutSize (g.outputs hv) (g.tests hv) ≤ g.base.nodes.length := by
  have hK : IsCut ((List.range g.base.nodes.length).toFinset.image (g.base.termD (g.baseValid hv))) (g.outputs hv) := by
    intro t ht ha
    rw [g.outputs_eq hv] at ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    have hmem : g.base.termD (g.baseValid hv) j ∈ (List.range g.base.nodes.length).toFinset.image (g.base.termD (g.baseValid hv)) :=
      Finset.mem_image.mpr ⟨j, by simp [g.outNodes_lt hv j hj], rfl⟩
    exact avoids_not_mem ha hmem
  refine (cutSize_le_card_of_isCut _ _ _ hK).trans (Finset.card_image_le.trans ?_)
  rw [List.toFinset_card_of_nodup List.nodup_range, List.length_range]

/-- **Correctness of the cut computation.** -/
theorem rhoExec_eq : g.rhoExec = cutSize (g.outputs hv) (g.tests hv) := by
  unfold rhoExec
  apply le_antisymm
  · obtain ⟨K, _, hK, hc⟩ := exists_min_cut (g.outputs hv) (g.tests hv)
    rw [← hc]
    exact (foldr_min_le _ _ _ _ (g.vecOf hv K) (g.vecOf_mem hv K) (g.isCutB_vecOf hv K hK)).trans
      (g.cutCard_vecOf_le hv K)
  · apply le_foldr_min _ _ _ _ _ (g.cutSize_le_nodes hv)
    intro b _ hb'
    exact (cutSize_le_card_of_isCut _ _ _ ((g.isCutB_iff hv b).mp hb')).trans
      (g.termCut_card_le hv b)

end cuts

/-! ### Correctness of the decision -/

/-- **Exact correctness against the general semantics**, for every degree `k ≥ 2`. -/
theorem strictDecideG_iff (k : ℕ) (hk : 2 ≤ k) : g.strictDecideG k = true ↔ g.Strict k := by
  unfold strictDecideG
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨_, hv⟩, hdist⟩, hρ⟩
    have hv' : g.Valid := hv
    refine ⟨hv', ?_⟩
    have hdist' := (g.base.testsDistinct_iff (g.baseValid hv')).mp hdist
    rw [g.rhoExec_eq hv'] at hρ
    exact (strict_degree_iff' k hk (g.base.xv (g.baseValid hv')) (g.base.yv (g.baseValid hv'))
      (g.base.xv_ne_yv _) (g.outputs hv') (g.tests hv') (g.var_x_mem_outputs hv')
      (g.var_y_mem_outputs hv') (g.guard_mem_tests hv')).mpr ⟨hdist', hρ⟩
  · rintro ⟨hv, hs⟩
    obtain ⟨hdist, hρ⟩ := (strict_degree_iff' k hk (g.base.xv (g.baseValid hv))
      (g.base.yv (g.baseValid hv)) (g.base.xv_ne_yv _) (g.outputs hv) (g.tests hv)
      (g.var_x_mem_outputs hv) (g.var_y_mem_outputs hv) (g.guard_mem_tests hv)).mp hs
    refine ⟨⟨⟨hk, hv⟩, (g.base.testsDistinct_iff (g.baseValid hv)).mpr hdist⟩, ?_⟩
    rw [g.rhoExec_eq hv]
    exact hρ

/-- Malformed encodings are rejected. -/
theorem strictDecideG_of_invalid (k : ℕ) (h : ¬ g.Valid) : g.strictDecideG k = false := by
  unfold strictDecideG
  have : g.isValid = false := by
    unfold Valid at h
    exact Bool.eq_false_iff.mpr h
  simp [this]

/-- Degrees below two are rejected. -/
theorem strictDecideG_of_degree_lt (k : ℕ) (hk : k < 2) : g.strictDecideG k = false := by
  unfold strictDecideG
  have : decide (2 ≤ k) = false := by simp; omega
  simp [this]

/-- On the three-output class, the general decision at degree two agrees with the
Phase-A procedure `strictDecide`. -/
theorem strictDecideG_ofInstance (γ : Instance) :
    (ofInstance γ).strictDecideG 2 = γ.strictDecide := by
  apply Bool.eq_iff_iff.mpr
  rw [(ofInstance γ).strictDecideG_iff 2 le_rfl, γ.strictDecide_iff, Strict_two_ofInstance]

end GInstance
end DisequalityDispersion.Encoded
