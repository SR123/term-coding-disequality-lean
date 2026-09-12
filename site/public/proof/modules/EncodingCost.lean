import StrictAlgorithm
import Mathlib.Data.Nat.Size

/-! # Bit encoding, input size and the cost of the strict procedure (T2)

## Bit encoding

`encodeBits γ : List Bool` is a self-delimiting binary encoding: a natural `n`
is written as `size n` ones, a zero, then the `size n` binary digits of `n`
(`natC n = 2 * size n + 1` bits); a list is its length followed by the
encodings of its entries; a node carries a one-bit tag.  The input size is
`N = sizeInstance γ = (encodeBits γ).length`.  Every declared source, symbol,
node, argument and test is written out, so `N` bounds all list lengths and
the bit length of every literal.

## Cost model

Costs are counted in bit steps on the actual executable definitions of
`EncodedSyntax.lean` / `StrictAlgorithm.lean`, one cost function per
definition with the same recursion shape:

* reading, copying or comparing a natural `n` costs `natC n` (its code length);
  comparing `a` with `b` costs `natC a + natC b`;
* a sequential access `l.getD i d` costs `accessC l i = min i l.length + 1`
  (cells walked; the list is a linked list, no random access is assumed);
* every list cell visited by a traversal (`all`, `any`, `map`, `length`,
  `Nodup` pairwise scan, `foldl` in `buildList`) costs `1`, plus the cost of
  the work done at that cell;
* `firstIndex p n` is charged for evaluating `p i` at every `i < n`
  (an upper bound on what it actually evaluates);
* comparing two nodes (or two signatures) costs `nodeC` of both.

The final theorem `strictDecideC_le` bounds the total charged cost by
`100 * N ^ 3`.  This is a cost semantics for the Lean definitions, not a
machine-model simulation; see the report for the remaining bridge. -/

namespace DisequalityDispersion.Encoded

/-! ### Sizes -/

/-- Code length of a natural: `2 * size n + 1`. -/
def natC (n : ℕ) : ℕ := 2 * Nat.size n + 1

/-- Cost of a sequential access at index `i`. -/
def accessC {α : Type} (l : List α) (i : ℕ) : ℕ := min i l.length + 1

/-- Code length of a list given the code length of its entries. -/
def listC {α : Type} (c : α → ℕ) (l : List α) : ℕ := natC l.length + (l.map c).sum

def pairC (p : ℕ × ℕ) : ℕ := natC p.1 + natC p.2

def nodeC : Node → ℕ
  | .src i => 1 + natC i
  | .app f args => 1 + natC f + listC natC args

/-- Input size in bits. -/
def sizeInstance (γ : Instance) : ℕ :=
  listC natC γ.sources + listC pairC γ.symbols + listC nodeC γ.nodes +
    natC γ.x + natC γ.y + natC γ.t + listC pairC γ.tests

/-! ### The concrete bit encoding -/

def encodeNat (n : ℕ) : List Bool := List.replicate (Nat.size n) true ++ false :: n.bits

def encodeList {α : Type} (f : α → List Bool) (l : List α) : List Bool :=
  encodeNat l.length ++ (l.map f).flatten

def encodePair (p : ℕ × ℕ) : List Bool := encodeNat p.1 ++ encodeNat p.2

def encodeNode : Node → List Bool
  | .src i => false :: encodeNat i
  | .app f args => true :: (encodeNat f ++ encodeList encodeNat args)

def encodeBits (γ : Instance) : List Bool :=
  encodeList encodeNat γ.sources ++ encodeList encodePair γ.symbols ++
    encodeList encodeNode γ.nodes ++ encodeNat γ.x ++ encodeNat γ.y ++ encodeNat γ.t ++
    encodeList encodePair γ.tests

theorem encodeNat_length (n : ℕ) : (encodeNat n).length = natC n := by
  simp [encodeNat, natC, Nat.size_eq_bits_len]
  omega

theorem encodeList_length {α : Type} (f : α → List Bool) (c : α → ℕ)
    (h : ∀ x, (f x).length = c x) (l : List α) : (encodeList f l).length = listC c l := by
  unfold encodeList listC
  rw [List.length_append, encodeNat_length, List.length_flatten, List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  exact h x

theorem encodePair_length (p : ℕ × ℕ) : (encodePair p).length = pairC p := by
  simp [encodePair, pairC, encodeNat_length]

theorem encodeNode_length (nd : Node) : (encodeNode nd).length = nodeC nd := by
  cases nd with
  | src i => simp [encodeNode, nodeC, encodeNat_length]; omega
  | app f args =>
      simp only [encodeNode, nodeC, List.length_cons, List.length_append, encodeNat_length,
        encodeList_length encodeNat natC encodeNat_length]
      omega

/-- The declared input size is the length of the actual bit encoding. -/
theorem encodeBits_length (γ : Instance) : (encodeBits γ).length = sizeInstance γ := by
  unfold encodeBits sizeInstance
  simp only [List.length_append, encodeNat_length,
    encodeList_length encodeNat natC encodeNat_length,
    encodeList_length encodePair pairC encodePair_length,
    encodeList_length encodeNode nodeC encodeNode_length]

/-! ### Elementary bounds -/

theorem one_le_natC (n : ℕ) : 1 ≤ natC n := by unfold natC; omega

theorem natC_mono {a b : ℕ} (h : a ≤ b) : natC a ≤ natC b := by
  unfold natC
  have := Nat.size_le_size h
  omega

theorem natC_le_linear (n : ℕ) : natC n ≤ 2 * n + 1 := by
  unfold natC
  have : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem accessC_le {α : Type} (l : List α) (i : ℕ) : accessC l i ≤ l.length + 1 := by
  unfold accessC
  omega

theorem sum_map_le_of_le {α : Type} (l : List α) (c : α → ℕ) (B : ℕ)
    (h : ∀ x ∈ l, c x ≤ B) : (l.map c).sum ≤ l.length * B := by
  have := List.sum_le_card_nsmul (l.map c) B (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h y hy)
  simpa using this

theorem sum_range_le_of_le (n : ℕ) (c : ℕ → ℕ) (B : ℕ) (h : ∀ j, j < n → c j ≤ B) :
    ((List.range n).map c).sum ≤ n * B := by
  have := sum_map_le_of_le (List.range n) c B (by
    intro j hj
    exact h j (List.mem_range.mp hj))
  simpa using this

theorem length_le_sum_map {α : Type} (l : List α) (c : α → ℕ) (h : ∀ x ∈ l, 1 ≤ c x) :
    l.length ≤ (l.map c).sum := by
  have := List.length_le_sum_of_one_le (l.map c) (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h y hy)
  simpa using this

theorem le_sum_map_of_mem {α : Type} {l : List α} (c : α → ℕ) {x : α} (hx : x ∈ l) :
    c x ≤ (l.map c).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem length_le_listC {α : Type} (c : α → ℕ) (l : List α) (h : ∀ x ∈ l, 1 ≤ c x) :
    l.length ≤ listC c l := by
  unfold listC
  have := length_le_sum_map l c h
  omega

theorem sum_map_le_listC {α : Type} (c : α → ℕ) (l : List α) : (l.map c).sum ≤ listC c l := by
  unfold listC; omega

theorem natC_length_le_listC {α : Type} (c : α → ℕ) (l : List α) : natC l.length ≤ listC c l := by
  unfold listC; omega

/-- Sum over indices of a function of the accessed entry equals the sum over entries. -/
theorem sum_range_getD {α : Type} (l : List α) (d : α) (g : α → ℕ) :
    ((List.range l.length).map (fun j => g (l.getD j d))).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
        List.map_cons, List.sum_cons]
      rw [← ih]
      rfl

/-! ### Facts about the input size -/

namespace Instance
variable (γ : Instance)

theorem sources_length_le : γ.sources.length ≤ sizeInstance γ := by
  have := length_le_listC natC γ.sources (fun x _ => one_le_natC x)
  unfold sizeInstance; omega

theorem symbols_length_le : γ.symbols.length ≤ sizeInstance γ := by
  have := length_le_listC pairC γ.symbols (fun x _ => by
    unfold pairC; have := one_le_natC x.1; omega)
  unfold sizeInstance; omega

theorem one_le_nodeC (nd : Node) : 1 ≤ nodeC nd := by
  cases nd with
  | src i => simp [nodeC]
  | app f args => simp only [nodeC]; omega

theorem nodes_length_le : γ.nodes.length ≤ sizeInstance γ := by
  have := length_le_listC nodeC γ.nodes (fun x _ => one_le_nodeC x)
  unfold sizeInstance; omega

theorem tests_length_le : γ.tests.length ≤ sizeInstance γ := by
  have := length_le_listC pairC γ.tests (fun x _ => by
    unfold pairC; have := one_le_natC x.1; omega)
  unfold sizeInstance; omega

theorem sum_nodeC_le : (γ.nodes.map nodeC).sum ≤ sizeInstance γ := by
  have := sum_map_le_listC nodeC γ.nodes
  unfold sizeInstance; omega

theorem nodeC_le_of_mem {nd : Node} (h : nd ∈ γ.nodes) : nodeC nd ≤ sizeInstance γ :=
  (le_sum_map_of_mem nodeC h).trans (γ.sum_nodeC_le)

theorem natC_x_le : natC γ.x ≤ sizeInstance γ := by unfold sizeInstance; omega
theorem natC_y_le : natC γ.y ≤ sizeInstance γ := by unfold sizeInstance; omega
theorem natC_t_le : natC γ.t ≤ sizeInstance γ := by unfold sizeInstance; omega

theorem natC_source_le {i : ℕ} (h : i ∈ γ.sources) : natC i ≤ sizeInstance γ := by
  have := (le_sum_map_of_mem natC h).trans (sum_map_le_listC natC γ.sources)
  unfold sizeInstance; omega

theorem symbol_le {p : ℕ × ℕ} (h : p ∈ γ.symbols) :
    natC p.1 ≤ sizeInstance γ ∧ natC p.2 ≤ sizeInstance γ := by
  have := (le_sum_map_of_mem pairC h).trans (sum_map_le_listC pairC γ.symbols)
  have e : pairC p = natC p.1 + natC p.2 := rfl
  unfold sizeInstance
  constructor <;> omega

theorem sum_symbol_fst_le : ((γ.symbols.map Prod.fst).map natC).sum ≤ sizeInstance γ := by
  rw [List.map_map]
  have h1 : ((γ.symbols.map (natC ∘ Prod.fst))).sum ≤ (γ.symbols.map pairC).sum := by
    apply List.sum_le_sum
    intro p _
    simp [pairC]
  have := sum_map_le_listC pairC γ.symbols
  unfold sizeInstance; omega

theorem sum_source_natC_le : (γ.sources.map natC).sum ≤ sizeInstance γ := by
  have := sum_map_le_listC natC γ.sources
  unfold sizeInstance; omega

theorem test_le {ij : ℕ × ℕ} (h : ij ∈ γ.tests) : natC ij.1 + natC ij.2 ≤ sizeInstance γ := by
  have := (le_sum_map_of_mem pairC h).trans (sum_map_le_listC pairC γ.tests)
  have e : pairC ij = natC ij.1 + natC ij.2 := rfl
  unfold sizeInstance; omega

theorem seven_le_size : 7 ≤ sizeInstance γ := by
  unfold sizeInstance
  have h1 := one_le_natC γ.x
  have h2 := one_le_natC γ.y
  have h3 := one_le_natC γ.t
  have h4 := natC_length_le_listC natC γ.sources
  have h5 := natC_length_le_listC pairC γ.symbols
  have h6 := natC_length_le_listC nodeC γ.nodes
  have h7 := natC_length_le_listC pairC γ.tests
  have := one_le_natC γ.sources.length
  have := one_le_natC γ.symbols.length
  have := one_le_natC γ.nodes.length
  have := one_le_natC γ.tests.length
  omega

/-- Any value bounded by `N` has code length at most `3N`. -/
theorem natC_le_three {v : ℕ} (h : v ≤ sizeInstance γ) : natC v ≤ 3 * sizeInstance γ := by
  have := natC_le_linear v
  have := γ.seven_le_size
  omega

theorem natC_k_le : natC γ.k ≤ 3 * sizeInstance γ := γ.natC_le_three γ.sources_length_le
theorem natC_m_le : natC γ.m ≤ 3 * sizeInstance γ := γ.natC_le_three γ.symbols_length_le
theorem natC_len_le : natC γ.nodes.length ≤ 3 * sizeInstance γ :=
  γ.natC_le_three γ.nodes_length_le

theorem natC_arityOf_le (f : ℕ) : natC (γ.arityOf f) ≤ sizeInstance γ := by
  unfold arityOf
  rcases Nat.lt_or_ge f γ.symbols.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact (γ.symbol_le (List.getElem_mem h)).2
  · rw [List.getD_eq_default _ _ h]
    have := γ.seven_le_size
    show natC 0 ≤ _
    unfold natC
    simp [Nat.size_zero]
    omega

/-- Facts about an application node of the instance. -/
theorem app_node_facts {f : ℕ} {args : List ℕ} (h : Node.app f args ∈ γ.nodes) :
    natC f ≤ sizeInstance γ ∧ args.length ≤ sizeInstance γ ∧
      natC args.length ≤ 3 * sizeInstance γ ∧
      (args.map natC).sum ≤ sizeInstance γ ∧ ∀ a ∈ args, natC a ≤ sizeInstance γ := by
  have hn := γ.nodeC_le_of_mem h
  simp only [nodeC, listC] at hn
  have hl := length_le_sum_map args natC (fun a _ => one_le_natC a)
  refine ⟨by omega, by omega, γ.natC_le_three (by omega), by omega, ?_⟩
  intro a ha
  have := le_sum_map_of_mem natC ha
  omega

/-- Number of arguments of a node. -/
def argsLen : Node → ℕ
  | .src _ => 0
  | .app _ args => args.length

theorem argsLen_le_nodeC (nd : Node) : argsLen nd ≤ nodeC nd := by
  cases nd with
  | src i => simp [argsLen]
  | app f args =>
      simp only [argsLen, nodeC, listC]
      have := length_le_sum_map args natC (fun a _ => one_le_natC a)
      omega

theorem sum_argsLen_le : (γ.nodes.map argsLen).sum ≤ sizeInstance γ :=
  (List.sum_le_sum (fun nd _ => argsLen_le_nodeC nd)).trans γ.sum_nodeC_le

theorem nodeC_getD_le (j : ℕ) (d : Node) (hd : nodeC d ≤ sizeInstance γ) :
    nodeC (γ.nodes.getD j d) ≤ sizeInstance γ := by
  rcases Nat.lt_or_ge j γ.nodes.length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact γ.nodeC_le_of_mem (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact hd

theorem nodeC_src_zero_le : nodeC (Node.src 0) ≤ sizeInstance γ := by
  have := γ.seven_le_size
  simp [nodeC, natC, Nat.size_zero]
  omega

theorem nodeC_app_zero_le : nodeC (Node.app 0 []) ≤ sizeInstance γ := by
  have := γ.seven_le_size
  simp [nodeC, natC, listC, Nat.size_zero]
  omega

theorem nodes_getD_mem (j : ℕ) (hj : j < γ.nodes.length) (d : Node) :
    γ.nodes.getD j d ∈ γ.nodes := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

end Instance

/-! ### Cost functions (one per executable definition) -/

namespace Instance
variable (γ : Instance)

/-- Pairwise scan for `decide l.Nodup`: every earlier entry is compared with every later one. -/
def nodupC : List ℕ → ℕ
  | [] => 0
  | a :: l => (l.map (fun b => natC a + natC b)).sum + nodupC l

/-- Cost of `nodeOk j nd`. -/
def nodeOkC (j : ℕ) : Node → ℕ
  | .src i => natC i + natC γ.k
  | .app f args =>
      natC f + natC γ.m + accessC γ.symbols f + natC args.length + natC (γ.arityOf f) +
        (args.map (fun a => natC a + natC j)).sum

/-- Cost of `nodesOk`: each node is accessed and checked. -/
def nodesOkC : ℕ :=
  ((List.range γ.nodes.length).map
    (fun j => 1 + accessC γ.nodes j + γ.nodeOkC j (γ.nodes.getD j (.src 0)))).sum

/-- Cost of `guardOk`: every test is scanned, both nodes are accessed and compared. -/
def guardC : ℕ :=
  (γ.tests.map (fun ij => 1 + accessC γ.nodes ij.1 + accessC γ.nodes ij.2 +
    nodeC (γ.nodes.getD ij.1 (.app 0 [])) + nodeC (γ.nodes.getD ij.2 (.app 0 [])) +
    natC γ.x + natC γ.y)).sum

/-- Cost of `isValid`. -/
def isValidC : ℕ :=
  (γ.sources.length + natC γ.k + 1) + nodupC γ.sources +
    (γ.symbols.length + nodupC (γ.symbols.map Prod.fst)) +
    (natC γ.x + natC γ.k) + (natC γ.y + natC γ.k) + (natC γ.x + natC γ.y) +
    γ.nodesOkC + (γ.nodes.length + natC γ.t + natC γ.nodes.length) +
    (γ.tests.map (fun ij => 1 + natC ij.1 + natC ij.2 + 2 * natC γ.nodes.length)).sum +
    γ.guardC

/-- Cost of computing `sigWith ids nd`. -/
def sigC (ids : List ℕ) : Node → ℕ
  | .src _ => 1
  | .app _ args => 1 + (args.map (fun a => accessC ids a)).sum

/-- Cost of `canonStep ids j`: signature of node `j`, a scan over all `i < j`
(access, signature, comparison), then the final lookup. -/
def canonStepC (ids : List ℕ) (j : ℕ) : ℕ :=
  let nd := γ.nodes.getD j (.src 0)
  let sg := sigWith ids nd
  let r := firstIndex (fun i => decide (sigWith ids (γ.nodes.getD i (.src 0)) = sg)) j
  accessC γ.nodes j + sigC ids nd +
    ((List.range j).map (fun i => 1 + accessC γ.nodes i + sigC ids (γ.nodes.getD i (.src 0)) +
      nodeC (sigWith ids (γ.nodes.getD i (.src 0))) + nodeC sg)).sum +
    natC j + natC r + accessC ids r

/-- Cost of `canonIds`. -/
def canonIdsC : ℕ :=
  ((List.range γ.nodes.length).map (fun j => 1 + γ.canonStepC (buildList γ.canonStep j) j)).sum

/-- Cost of `flagStep flags j`. -/
def flagStepC (flags : List Bool) (j : ℕ) : ℕ :=
  accessC γ.nodes j +
    match γ.nodes.getD j (.src 0) with
    | .src i => natC i + natC γ.x + natC γ.y
    | .app _ args => (args.map (fun a => 1 + accessC flags a)).sum

/-- Cost of `usesOther`. -/
def usesOtherC : ℕ :=
  ((List.range γ.nodes.length).map (fun j => 1 + γ.flagStepC (buildList γ.flagStep j) j)).sum

/-- Cost of `testsDistinct ids`. -/
def testsDistinctC (ids : List ℕ) : ℕ :=
  (γ.tests.map (fun ij => 1 + accessC ids ij.1 + accessC ids ij.2 +
    natC (ids.getD ij.1 0) + natC (ids.getD ij.2 0))).sum

/-- Total charged cost of `strictDecide` (all phases are charged, whether or not
validation short-circuits). -/
def strictDecideC : ℕ :=
  γ.isValidC + γ.canonIdsC + γ.testsDistinctC γ.canonIds + γ.usesOtherC +
    accessC γ.usesOther γ.t

/-! ### Bounds -/

theorem nodupC_le (l : List ℕ) : nodupC l ≤ l.length * (l.map natC).sum := by
  induction l with
  | nil => simp [nodupC]
  | cons a l ih =>
      simp only [nodupC, List.length_cons, List.map_cons, List.sum_cons]
      rw [List.sum_map_add]
      have h1 : (l.map (fun _ => natC a)).sum = l.length * natC a := by
        simp [List.map_const']
      rw [h1]
      nlinarith [ih]

theorem sigC_le (ids : List ℕ) (nd : Node) :
    sigC ids nd ≤ 1 + argsLen nd * (ids.length + 1) := by
  cases nd with
  | src i => simp [sigC, argsLen]
  | app f args =>
      simp only [sigC, argsLen]
      have := sum_map_le_of_le args (fun a => accessC ids a) (ids.length + 1)
        (fun a _ => accessC_le ids a)
      omega

theorem nodeC_sigWith_le (ids : List ℕ) (hids : ∀ a, ids.getD a 0 ≤ a) (nd : Node) :
    nodeC (sigWith ids nd) ≤ nodeC nd := by
  cases nd with
  | src i => simp [sigWith]
  | app f args =>
      simp only [sigWith, nodeC, listC, List.length_map, List.map_map]
      have : ((args.map (natC ∘ fun a => ids.getD a 0))).sum ≤ (args.map natC).sum := by
        apply List.sum_le_sum
        intro a _
        exact natC_mono (hids a)
      omega

/-- Entries of the partial identifier list never exceed their own index. -/
theorem buildList_canonStep_getD_le (j a : ℕ) : (buildList γ.canonStep j).getD a 0 ≤ a := by
  induction j generalizing a with
  | zero => simp [buildList]
  | succ j ih =>
      rw [buildList_succ]
      rcases Nat.lt_or_ge a j with h | h
      · rw [List.getD_append _ _ _ _ (by rw [buildList_length]; exact h)]
        exact ih a
      · rcases Nat.lt_or_ge a (j + 1) with h' | h'
        · have : a = j := by omega
          subst this
          rw [List.getD_append_right _ _ _ _ (by rw [buildList_length])]
          rw [buildList_length, Nat.sub_self]
          simp only [List.getD_cons_zero]
          unfold canonStep
          simp only
          split
          · rename_i hr
            exact (ih _).trans (le_of_lt hr)
          · exact le_refl _
        · rw [List.getD_eq_default]
          · omega
          · simp [buildList_length]; omega

theorem sum_range_mono (c : ℕ → ℕ) {j n : ℕ} (h : j ≤ n) :
    ((List.range j).map c).sum ≤ ((List.range n).map c).sum := by
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  rw [List.range_add, List.map_append, List.sum_append]
  omega

theorem sum_range_argsLen_le (j : ℕ) (hj : j ≤ γ.nodes.length) :
    ((List.range j).map (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum ≤ sizeInstance γ := by
  refine (sum_range_mono _ hj).trans ?_
  rw [sum_range_getD]
  exact γ.sum_argsLen_le

theorem canonStepC_le (j : ℕ) (hj : j < γ.nodes.length) :
    γ.canonStepC (buildList γ.canonStep j) j ≤
      4 * sizeInstance γ ^ 2 + 11 * sizeInstance γ + 3 +
        (sizeInstance γ + 1) * argsLen (γ.nodes.getD j (.src 0)) := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hidsl : (buildList γ.canonStep j).length = j := buildList_length _ _
  have hidsle : ∀ a, (buildList γ.canonStep j).getD a 0 ≤ a := γ.buildList_canonStep_getD_le j
  have hargs := γ.sum_range_argsLen_le j (le_of_lt hj)
  set N := sizeInstance γ with hN
  set ids := buildList γ.canonStep j with hids
  unfold canonStepC
  simp only
  set nd := γ.nodes.getD j (.src 0) with hnd
  set sg := sigWith ids nd with hsg
  set r := firstIndex (fun i => decide (sigWith ids (γ.nodes.getD i (.src 0)) = sg)) j with hr
  have hr_le : r ≤ j := firstIndex_le _ _
  have h1 : accessC γ.nodes j ≤ N + 1 := (accessC_le _ _).trans (by omega)
  have h2 : sigC ids nd ≤ 1 + (N + 1) * argsLen nd := by
    refine (sigC_le ids nd).trans ?_
    rw [hidsl, Nat.mul_comm]
    have : (j + 1) * argsLen nd ≤ (N + 1) * argsLen nd := Nat.mul_le_mul_right _ (by omega)
    omega
  have hnd_le : nodeC nd ≤ N := γ.nodeC_getD_le j _ γ.nodeC_src_zero_le
  have hsg_le : nodeC sg ≤ N := (nodeC_sigWith_le ids hidsle nd).trans hnd_le
  have hpt : ∀ i ∈ List.range j, 1 + accessC γ.nodes i + sigC ids (γ.nodes.getD i (.src 0)) +
      nodeC (sigWith ids (γ.nodes.getD i (.src 0))) + nodeC sg ≤
      (3 * N + 3) + (N + 1) * argsLen (γ.nodes.getD i (.src 0)) := by
    intro i _
    have a1 : accessC γ.nodes i ≤ N + 1 := (accessC_le _ _).trans (by omega)
    have a2 := sigC_le ids (γ.nodes.getD i (.src 0))
    rw [hidsl, Nat.mul_comm] at a2
    have a2' : (j + 1) * argsLen (γ.nodes.getD i (.src 0)) ≤
        (N + 1) * argsLen (γ.nodes.getD i (.src 0)) := Nat.mul_le_mul_right _ (by omega)
    have a3 : nodeC (sigWith ids (γ.nodes.getD i (.src 0))) ≤ N :=
      (nodeC_sigWith_le ids hidsle _).trans (γ.nodeC_getD_le i _ γ.nodeC_src_zero_le)
    omega
  have hsum := List.sum_le_sum hpt
  have hrhs : ((List.range j).map (fun i => (3 * N + 3) +
      (N + 1) * argsLen (γ.nodes.getD i (.src 0)))).sum =
      j * (3 * N + 3) + (N + 1) * ((List.range j).map
        (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum := by
    rw [List.sum_map_add, List.sum_map_mul_left]
    simp [List.map_const']
  rw [hrhs] at hsum
  have h3 : (N + 1) * ((List.range j).map (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum ≤
      (N + 1) * N := Nat.mul_le_mul_left _ hargs
  have h4 : natC j ≤ 3 * N := γ.natC_le_three (by omega)
  have h5 : natC r ≤ 3 * N := γ.natC_le_three (by omega)
  have h6 : accessC ids r ≤ N + 1 := (accessC_le _ _).trans (by omega)
  have hj' : j * (3 * N + 3) ≤ N * (3 * N + 3) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem canonIdsC_le : γ.canonIdsC ≤ 4 * sizeInstance γ ^ 3 + 13 * sizeInstance γ ^ 2 +
    5 * sizeInstance γ := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hargs := γ.sum_range_argsLen_le γ.nodes.length le_rfl
  have hpt : ∀ j ∈ List.range γ.nodes.length,
      1 + γ.canonStepC (buildList γ.canonStep j) j ≤
        (4 * sizeInstance γ ^ 2 + 11 * sizeInstance γ + 4) +
          (sizeInstance γ + 1) * argsLen (γ.nodes.getD j (.src 0)) := by
    intro j hj
    have := γ.canonStepC_le j (List.mem_range.mp hj)
    omega
  set N := sizeInstance γ with hN
  unfold canonIdsC
  have hsum := List.sum_le_sum hpt
  have hrhs : ((List.range γ.nodes.length).map (fun j => (4 * N ^ 2 + 11 * N + 4) +
      (N + 1) * argsLen (γ.nodes.getD j (.src 0)))).sum =
      γ.nodes.length * (4 * N ^ 2 + 11 * N + 4) + (N + 1) * ((List.range γ.nodes.length).map
        (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum := by
    rw [List.sum_map_add, List.sum_map_mul_left]
    simp [List.map_const']
  rw [hrhs] at hsum
  have h2 : (N + 1) * ((List.range γ.nodes.length).map
      (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum ≤ (N + 1) * N :=
    Nat.mul_le_mul_left _ hargs
  have h3 : γ.nodes.length * (4 * N ^ 2 + 11 * N + 4) ≤ N * (4 * N ^ 2 + 11 * N + 4) :=
    Nat.mul_le_mul_right _ hlen
  nlinarith

theorem nodeOkC_le (j : ℕ) (hj : j < γ.nodes.length) :
    γ.nodeOkC j (γ.nodes.getD j (.src 0)) ≤
      10 * sizeInstance γ + 1 + 3 * sizeInstance γ * argsLen (γ.nodes.getD j (.src 0)) := by
  have hmem := γ.nodes_getD_mem j hj (.src 0)
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hk := γ.natC_k_le
  have hm := γ.natC_m_le
  have hj' : natC j ≤ 3 * sizeInstance γ := γ.natC_le_three (by omega)
  cases hnd : γ.nodes.getD j (.src 0) with
  | src i =>
      rw [hnd] at hmem
      have := γ.nodeC_le_of_mem hmem
      simp only [nodeC] at this
      simp only [nodeOkC, argsLen]
      omega
  | app f args =>
      rw [hnd] at hmem
      obtain ⟨hf, hal, hnl, hsum, _⟩ := γ.app_node_facts hmem
      simp only [nodeOkC, argsLen]
      have ha : accessC γ.symbols f ≤ sizeInstance γ + 1 :=
        (accessC_le _ _).trans (by have := γ.symbols_length_le; omega)
      have har := γ.natC_arityOf_le f
      have hs : (args.map (fun a => natC a + natC j)).sum =
          (args.map natC).sum + args.length * natC j := by
        rw [List.sum_map_add]
        simp [List.map_const']
      rw [hs]
      have : args.length * natC j ≤ args.length * (3 * sizeInstance γ) :=
        Nat.mul_le_mul_left _ hj'
      nlinarith

theorem nodesOkC_le : γ.nodesOkC ≤ 15 * sizeInstance γ ^ 2 + 3 * sizeInstance γ := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hargs := γ.sum_range_argsLen_le γ.nodes.length le_rfl
  have hpt : ∀ j ∈ List.range γ.nodes.length,
      1 + accessC γ.nodes j + γ.nodeOkC j (γ.nodes.getD j (.src 0)) ≤
        (12 * sizeInstance γ + 3) + (3 * sizeInstance γ) * argsLen (γ.nodes.getD j (.src 0)) := by
    intro j hj
    have := γ.nodeOkC_le j (List.mem_range.mp hj)
    have ha : accessC γ.nodes j ≤ sizeInstance γ + 1 := (accessC_le _ _).trans (by omega)
    omega
  set N := sizeInstance γ with hN
  unfold nodesOkC
  have hsum := List.sum_le_sum hpt
  have hrhs : ((List.range γ.nodes.length).map (fun j => (12 * N + 3) +
      (3 * N) * argsLen (γ.nodes.getD j (.src 0)))).sum =
      γ.nodes.length * (12 * N + 3) + (3 * N) * ((List.range γ.nodes.length).map
        (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum := by
    rw [List.sum_map_add, List.sum_map_mul_left]
    simp [List.map_const']
  rw [hrhs] at hsum
  have h2 : (3 * N) * ((List.range γ.nodes.length).map
      (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum ≤ (3 * N) * N :=
    Nat.mul_le_mul_left _ hargs
  have h3 : γ.nodes.length * (12 * N + 3) ≤ N * (12 * N + 3) := Nat.mul_le_mul_right _ hlen
  nlinarith

theorem guardC_le : γ.guardC ≤ 6 * sizeInstance γ ^ 2 + 3 * sizeInstance γ := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have htl : γ.tests.length ≤ sizeInstance γ := γ.tests_length_le
  have hx := γ.natC_x_le
  have hy := γ.natC_y_le
  unfold guardC
  have := sum_map_le_of_le γ.tests (fun ij => 1 + accessC γ.nodes ij.1 + accessC γ.nodes ij.2 +
    nodeC (γ.nodes.getD ij.1 (.app 0 [])) + nodeC (γ.nodes.getD ij.2 (.app 0 [])) +
    natC γ.x + natC γ.y) (6 * sizeInstance γ + 3) (by
    intro ij _
    dsimp only
    have a1 : accessC γ.nodes ij.1 ≤ sizeInstance γ + 1 := (accessC_le _ _).trans (by omega)
    have a2 : accessC γ.nodes ij.2 ≤ sizeInstance γ + 1 := (accessC_le _ _).trans (by omega)
    have a3 := γ.nodeC_getD_le ij.1 _ γ.nodeC_app_zero_le
    have a4 := γ.nodeC_getD_le ij.2 _ γ.nodeC_app_zero_le
    omega)
  have : γ.tests.length * (6 * sizeInstance γ + 3) ≤ sizeInstance γ * (6 * sizeInstance γ + 3) :=
    Nat.mul_le_mul_right _ htl
  nlinarith

theorem isValidC_le : γ.isValidC ≤ 30 * sizeInstance γ ^ 2 + 27 * sizeInstance γ + 1 := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hsl : γ.sources.length ≤ sizeInstance γ := γ.sources_length_le
  have hyl : γ.symbols.length ≤ sizeInstance γ := γ.symbols_length_le
  have htl : γ.tests.length ≤ sizeInstance γ := γ.tests_length_le
  have hk := γ.natC_k_le
  have hx := γ.natC_x_le
  have hy := γ.natC_y_le
  have ht := γ.natC_t_le
  have hl := γ.natC_len_le
  have hn1 : nodupC γ.sources ≤ sizeInstance γ * sizeInstance γ := by
    refine (nodupC_le _).trans ?_
    exact Nat.mul_le_mul hsl γ.sum_source_natC_le
  have hn2 : nodupC (γ.symbols.map Prod.fst) ≤ sizeInstance γ * sizeInstance γ := by
    refine (nodupC_le _).trans ?_
    rw [List.length_map]
    exact Nat.mul_le_mul hyl γ.sum_symbol_fst_le
  have hno := γ.nodesOkC_le
  have hg := γ.guardC_le
  have hts : (γ.tests.map (fun ij => 1 + natC ij.1 + natC ij.2 +
      2 * natC γ.nodes.length)).sum ≤ sizeInstance γ * (7 * sizeInstance γ + 1) := by
    refine (sum_map_le_of_le γ.tests _ (7 * sizeInstance γ + 1) ?_).trans ?_
    · intro ij hij
      have := γ.test_le hij
      omega
    · exact Nat.mul_le_mul_right _ htl
  unfold isValidC
  nlinarith

theorem flagStepC_le (j : ℕ) (hj : j < γ.nodes.length) :
    γ.flagStepC (buildList γ.flagStep j) j ≤
      4 * sizeInstance γ + 1 + (sizeInstance γ + 2) * argsLen (γ.nodes.getD j (.src 0)) := by
  have hmem := γ.nodes_getD_mem j hj (.src 0)
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hfl : (buildList γ.flagStep j).length = j := buildList_length _ _
  have hx := γ.natC_x_le
  have hy := γ.natC_y_le
  have ha : accessC γ.nodes j ≤ sizeInstance γ + 1 := (accessC_le _ _).trans (by omega)
  unfold flagStepC
  cases hnd : γ.nodes.getD j (.src 0) with
  | src i =>
      rw [hnd] at hmem
      have := γ.nodeC_le_of_mem hmem
      simp only [nodeC] at this
      dsimp only [argsLen]
      show accessC γ.nodes j + (natC i + natC γ.x + natC γ.y) ≤ _
      omega
  | app f args =>
      dsimp only [argsLen]
      show accessC γ.nodes j + (args.map (fun a => 1 + accessC (buildList γ.flagStep j) a)).sum ≤ _
      have := sum_map_le_of_le args (fun a => 1 + accessC (buildList γ.flagStep j) a)
        (sizeInstance γ + 2) (by
          intro a _
          dsimp only
          have := accessC_le (buildList γ.flagStep j) a
          rw [hfl] at this
          omega)
      rw [Nat.mul_comm] at this
      omega

theorem usesOtherC_le : γ.usesOtherC ≤ 5 * sizeInstance γ ^ 2 + 4 * sizeInstance γ := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have hargs := γ.sum_range_argsLen_le γ.nodes.length le_rfl
  have hpt : ∀ j ∈ List.range γ.nodes.length,
      1 + γ.flagStepC (buildList γ.flagStep j) j ≤
        (4 * sizeInstance γ + 2) + (sizeInstance γ + 2) * argsLen (γ.nodes.getD j (.src 0)) := by
    intro j hj
    have := γ.flagStepC_le j (List.mem_range.mp hj)
    omega
  set N := sizeInstance γ with hN
  unfold usesOtherC
  have hsum := List.sum_le_sum hpt
  have hrhs : ((List.range γ.nodes.length).map (fun j => (4 * N + 2) +
      (N + 2) * argsLen (γ.nodes.getD j (.src 0)))).sum =
      γ.nodes.length * (4 * N + 2) + (N + 2) * ((List.range γ.nodes.length).map
        (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum := by
    rw [List.sum_map_add, List.sum_map_mul_left]
    simp [List.map_const']
  rw [hrhs] at hsum
  have h2 : (N + 2) * ((List.range γ.nodes.length).map
      (fun i => argsLen (γ.nodes.getD i (.src 0)))).sum ≤ (N + 2) * N :=
    Nat.mul_le_mul_left _ hargs
  have h3 : γ.nodes.length * (4 * N + 2) ≤ N * (4 * N + 2) := Nat.mul_le_mul_right _ hlen
  nlinarith

theorem testsDistinctC_le : γ.testsDistinctC γ.canonIds ≤
    4 * sizeInstance γ ^ 2 + 3 * sizeInstance γ := by
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have htl : γ.tests.length ≤ sizeInstance γ := γ.tests_length_le
  have hcl : γ.canonIds.length = γ.nodes.length := γ.canonIds_length
  have hle : ∀ a, γ.canonIds.getD a 0 ≤ a := γ.buildList_canonStep_getD_le γ.nodes.length
  unfold testsDistinctC
  have := sum_map_le_of_le γ.tests (fun ij => 1 + accessC γ.canonIds ij.1 +
    accessC γ.canonIds ij.2 + natC (γ.canonIds.getD ij.1 0) + natC (γ.canonIds.getD ij.2 0))
    (4 * sizeInstance γ + 3) (by
    intro ij hij
    dsimp only
    have ht := γ.test_le hij
    have a1 : accessC γ.canonIds ij.1 ≤ sizeInstance γ + 1 :=
      (accessC_le _ _).trans (by omega)
    have a2 : accessC γ.canonIds ij.2 ≤ sizeInstance γ + 1 :=
      (accessC_le _ _).trans (by omega)
    have a3 := natC_mono (hle ij.1)
    have a4 := natC_mono (hle ij.2)
    omega)
  have : γ.tests.length * (4 * sizeInstance γ + 3) ≤ sizeInstance γ * (4 * sizeInstance γ + 3) :=
    Nat.mul_le_mul_right _ htl
  nlinarith

/-- **Polynomial bit cost of the strict procedure.**  Under the cost model of
this module, `strictDecide γ` is charged at most `20 N³` bit steps, where
`N = sizeInstance γ = (encodeBits γ).length` is the input bit length. -/
theorem strictDecideC_le : γ.strictDecideC ≤ 20 * sizeInstance γ ^ 3 := by
  have h7 := γ.seven_le_size
  have hlen : γ.nodes.length ≤ sizeInstance γ := γ.nodes_length_le
  have h1 := γ.isValidC_le
  have h2 := γ.canonIdsC_le
  have h3 := γ.testsDistinctC_le
  have h4 := γ.usesOtherC_le
  have h5 : accessC γ.usesOther γ.t ≤ sizeInstance γ + 1 := by
    refine (accessC_le _ _).trans ?_
    unfold usesOther
    rw [buildList_length]
    omega
  unfold strictDecideC
  set N := sizeInstance γ with hN
  have hN2 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hN1 : N ≤ N ^ 2 := by nlinarith
  have h52 : 52 * N ^ 2 ≤ 8 * N ^ 3 := by
    have : 7 * N ^ 2 ≤ N ^ 3 := by
      calc 7 * N ^ 2 ≤ N * N ^ 2 := Nat.mul_le_mul_right _ h7
        _ = N ^ 3 := by ring
    nlinarith
  nlinarith

end Instance

end DisequalityDispersion.Encoded
