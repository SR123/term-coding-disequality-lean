import StrictAlgorithm
import Transport
import CompilerBridge

/-! # The effective hard compiler on the encoded C3 class (T3)

For fixed `d` and fixed relator list `rels`, `compileWord d rels w` is the
encoded C3 instance whose decoded semantics is exactly the existing hard
compiler `compilerTests d rels w` of `CompilerBridge.lean`: sources
`x = 0` (false), `y = 1` (true), output `t = x`, `2d` unary symbols
`(i, true) ↦ 1 + 2i`, `(i, false) ↦ 2i`, the `2d` inverse-law tests, the
relator tests, the guard and the target-word test, in that order, with
`2d + rels.length + 2` tests.  Raw signed words are kept verbatim. -/

namespace DisequalityDispersion

theorem Term.app_congr {V F : Type} {arity : F → ℕ} {f g : F} (h : f = g)
    {ts : Fin (arity f) → Term V F arity} {us : Fin (arity g) → Term V F arity}
    (H : ∀ (i : Fin (arity f)) (j : Fin (arity g)), i.1 = j.1 → ts i = us j) :
    Term.app f ts = Term.app g us := by
  subst h
  congr
  funext i
  exact H i i rfl

theorem List.getElem?_append_middle {α : Type} (a b c : List α) (p : ℕ) (hp : p < b.length) :
    (a ++ b ++ c)[a.length + p]? = some b[p] := by
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
  simp [hp]

theorem List.getElem?_append_last {α : Type} (a b : List α) (p : ℕ) (hp : p < b.length) :
    (a ++ b)[a.length + p]? = some b[p] := by
  rw [List.getElem?_append_right (by omega)]
  simp [hp]

namespace Encoded
open Instance

/-! ### Word chains -/

/-- Symbol index of a signed letter: `(i, b) ↦ [b] + 2 i`. -/
def letterCode {d : ℕ} (l : Letter (Fin d)) : ℕ := (if l.2 then 1 else 0) + 2 * l.1.1

theorem letterCode_lt {d : ℕ} (l : Letter (Fin d)) : letterCode l < 2 * d := by
  unfold letterCode
  have := l.1.2
  split <;> omega

/-- Nodes for one word placed from index `s`, and the root index (`0` = source `x`
for the empty word).  The word is outermost-first, as in `wordTerm`. -/
def wordNodes {d : ℕ} (s : ℕ) : List (Letter (Fin d)) → List Node × ℕ
  | [] => ([], 0)
  | l :: w =>
      let p := wordNodes s w
      (p.1 ++ [.app (letterCode l) [p.2]], s + p.1.length)

/-- Chains for a list of words placed consecutively from index `s`, with roots. -/
def chains {d : ℕ} (s : ℕ) : List (List (Letter (Fin d))) → List Node × List ℕ
  | [] => ([], [])
  | v :: vs =>
      let p := wordNodes s v
      let q := chains (s + p.1.length) vs
      (p.1 ++ q.1, p.2 :: q.2)

/-- The `2d` inverse-law words, in the order of `compilerTests`. -/
def laws (d : ℕ) : List (List (Letter (Fin d))) :=
  (List.finRange d).map (fun i => [(i, true), (i, false)]) ++
  (List.finRange d).map (fun i => [(i, false), (i, true)])

/-- The encoded hard instance for the target word `w`. -/
def compileWord (d : ℕ) (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d))) :
    Instance :=
  let lr := chains 2 (laws d ++ rels)
  let pw := wordNodes (2 + lr.1.length) w
  { sources := [0, 1]
    symbols := (List.range (2 * d)).map (fun s => (s, 1))
    nodes := [.src 0, .src 1] ++ lr.1 ++ pw.1
    x := 0
    y := 1
    t := 0
    tests := [(0, 1)] ++ lr.2.map (fun ρ => (ρ, 1)) ++ [(pw.2, 0)] }

section chainLemmas
variable {d : ℕ}

theorem wordNodes_length (s : ℕ) (w : List (Letter (Fin d))) :
    (wordNodes s w).1.length = w.length := by
  induction w with
  | nil => rfl
  | cons l w ih => simp [wordNodes, ih]

theorem wordNodes_root_lt (s : ℕ) (hs : 1 ≤ s) (w : List (Letter (Fin d))) :
    (wordNodes s w).2 < s + w.length := by
  cases w with
  | nil => simp only [wordNodes, List.length_nil, Nat.add_zero]; omega
  | cons l w => simp [wordNodes, wordNodes_length]

theorem wordNodes_getElem (s : ℕ) (hs : 1 ≤ s) (w : List (Letter (Fin d))) :
    ∀ p (hp : p < (wordNodes s w).1.length),
      ∃ (l : Letter (Fin d)) (a : ℕ), (wordNodes s w).1[p] = .app (letterCode l) [a] ∧ a < s + p := by
  induction w with
  | nil => intro p hp; simp [wordNodes] at hp
  | cons l w ih =>
      intro p hp
      simp only [wordNodes, List.length_append, List.length_singleton] at hp
      rcases Nat.lt_or_ge p (wordNodes s w).1.length with h | h
      · obtain ⟨l', a, he, ha⟩ := ih p h
        refine ⟨l', a, ?_, ha⟩
        simp only [wordNodes]
        rw [List.getElem_append_left h]
        exact he
      · have hp' : p = (wordNodes s w).1.length := by omega
        subst hp'
        refine ⟨l, (wordNodes s w).2, ?_, ?_⟩
        · simp [wordNodes]
        · have := wordNodes_root_lt s hs w
          rw [wordNodes_length]
          exact this

theorem chains_length (s : ℕ) (vs : List (List (Letter (Fin d)))) :
    (chains s vs).1.length = (vs.map List.length).sum := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => simp [chains, wordNodes_length, ih]

theorem chains_roots_length (s : ℕ) (vs : List (List (Letter (Fin d)))) :
    (chains s vs).2.length = vs.length := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => simp [chains, ih]

theorem chains_getElem (s : ℕ) (hs : 1 ≤ s) (vs : List (List (Letter (Fin d)))) :
    ∀ p (hp : p < (chains s vs).1.length),
      ∃ (l : Letter (Fin d)) (a : ℕ), (chains s vs).1[p] = .app (letterCode l) [a] ∧ a < s + p := by
  induction vs generalizing s with
  | nil => intro p hp; simp [chains] at hp
  | cons v vs ih =>
      intro p hp
      simp only [chains, List.length_append] at hp
      rcases Nat.lt_or_ge p (wordNodes s v).1.length with h | h
      · obtain ⟨l, a, he, ha⟩ := wordNodes_getElem s hs v p h
        refine ⟨l, a, ?_, ha⟩
        simp only [chains]
        rw [List.getElem_append_left h]
        exact he
      · obtain ⟨l, a, he, ha⟩ := ih (s + (wordNodes s v).1.length) (by omega)
          (p - (wordNodes s v).1.length) (by omega)
        refine ⟨l, a, ?_, by omega⟩
        simp only [chains]
        rw [List.getElem_append_right h]
        exact he

theorem chains_root_lt (s : ℕ) (hs : 1 ≤ s) (vs : List (List (Letter (Fin d)))) :
    ∀ ρ ∈ (chains s vs).2, ρ < s + (chains s vs).1.length := by
  induction vs generalizing s with
  | nil => intro ρ h; simp [chains] at h
  | cons v vs ih =>
      intro ρ h
      simp only [chains, List.mem_cons] at h
      simp only [chains, List.length_append]
      rcases h with rfl | h
      · have := wordNodes_root_lt s hs v
        rw [wordNodes_length]
        omega
      · have := ih (s + (wordNodes s v).1.length) (by omega) ρ h
        omega

end chainLemmas

/-! ### Validity of the compiled instance -/

section compiled
variable (d : ℕ) (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))

theorem compileWord_k : (compileWord d rels w).k = 2 := rfl
theorem compileWord_sources : (compileWord d rels w).sources = [0, 1] := rfl
theorem compileWord_symbols :
    (compileWord d rels w).symbols = (List.range (2 * d)).map (fun s => (s, 1)) := rfl
theorem compileWord_x : (compileWord d rels w).x = 0 := rfl
theorem compileWord_y : (compileWord d rels w).y = 1 := rfl
theorem compileWord_t : (compileWord d rels w).t = 0 := rfl
theorem compileWord_nodes : (compileWord d rels w).nodes =
    [.src 0, .src 1] ++ (chains 2 (laws d ++ rels)).1 ++
      (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1 := rfl
theorem compileWord_tests : (compileWord d rels w).tests =
    [(0, 1)] ++ (chains 2 (laws d ++ rels)).2.map (fun ρ => (ρ, 1)) ++
      [((wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).2, 0)] := rfl

theorem compileWord_m : (compileWord d rels w).m = 2 * d := by
  simp [Instance.m, compileWord]

theorem compileWord_arityOf (f : ℕ) (hf : f < 2 * d) : (compileWord d rels w).arityOf f = 1 := by
  unfold Instance.arityOf
  rw [compileWord_symbols, List.getD_eq_getElem _ _ (by simpa using hf)]
  simp

theorem compileWord_nodes_length :
    (compileWord d rels w).nodes.length =
      2 + (chains 2 (laws d ++ rels)).1.length + w.length := by
  simp [compileWord, wordNodes_length]
  omega

theorem compileWord_nodes_zero : (compileWord d rels w).nodes[0]? = some (.src 0) := by
  simp [compileWord]

theorem compileWord_nodes_one : (compileWord d rels w).nodes[1]? = some (.src 1) := by
  simp [compileWord]

theorem compileWord_nodes_lr (p : ℕ) (hp : p < (chains 2 (laws d ++ rels)).1.length) :
    (compileWord d rels w).nodes[2 + p]? = some ((chains 2 (laws d ++ rels)).1[p]) := by
  show ([Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1 ++
    (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1)[2 + p]? = _
  exact List.getElem?_append_middle [Node.src 0, Node.src 1] _ _ p hp

theorem compileWord_nodes_w (p : ℕ)
    (hp : p < (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1.length) :
    (compileWord d rels w).nodes[2 + (chains 2 (laws d ++ rels)).1.length + p]? =
      some ((wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1[p]) := by
  show ([Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1 ++
    (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1)[2 + (chains 2 (laws d ++ rels)).1.length + p]? = _
  have h2 : ([Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1).length =
      2 + (chains 2 (laws d ++ rels)).1.length := by simp; omega
  have := List.getElem?_append_last ([Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1)
    (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1 p hp
  rw [h2] at this
  exact this

theorem compileWord_valid : (compileWord d rels w).Valid := by
  rw [valid_iff]
  have hlen := compileWord_nodes_length d rels w
  have hlr := chains_root_lt 2 (by norm_num) (laws d ++ rels)
  have hw := wordNodes_root_lt (2 + (chains 2 (laws d ++ rels)).1.length) (by omega) w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_rfl
  · show [0, 1].Nodup; decide
  · rw [compileWord_symbols]
    simp [List.map_map, Function.comp_def, List.nodup_range]
  · show (0 : ℕ) < 2; decide
  · show (1 : ℕ) < 2; decide
  · show (0 : ℕ) ≠ 1; decide
  · intro j hj
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · interval_cases j
      · have h := compileWord_nodes_zero d rels w
        rw [List.getElem?_eq_some_iff] at h
        obtain ⟨_, h⟩ := h
        rw [h, nodeOk_src]
        show (0 : ℕ) < 2; decide
      · have h := compileWord_nodes_one d rels w
        rw [List.getElem?_eq_some_iff] at h
        obtain ⟨_, h⟩ := h
        rw [h, nodeOk_src]
        show (1 : ℕ) < 2; decide
    · obtain ⟨p, rfl⟩ : ∃ p, j = 2 + p := ⟨j - 2, by omega⟩
      rcases Nat.lt_or_ge p (chains 2 (laws d ++ rels)).1.length with hp | hp
      · have h := compileWord_nodes_lr d rels w p hp
        rw [List.getElem?_eq_some_iff] at h
        obtain ⟨_, h⟩ := h
        rw [h]
        obtain ⟨l, a, he, ha⟩ := chains_getElem 2 (by norm_num) (laws d ++ rels) p hp
        rw [he, nodeOk_app, compileWord_m, compileWord_arityOf d rels w _ (letterCode_lt l)]
        refine ⟨letterCode_lt l, rfl, ?_⟩
        intro a' ha'
        simp only [List.mem_singleton] at ha'
        omega
      · obtain ⟨q, hq'⟩ : ∃ q, p = (chains 2 (laws d ++ rels)).1.length + q :=
          ⟨p - (chains 2 (laws d ++ rels)).1.length, by omega⟩
        have hq : q < (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1.length := by
          rw [wordNodes_length]; omega
        have h : (compileWord d rels w).nodes[2 + p]? =
            some ((wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1[q]) := by
          rw [hq', ← Nat.add_assoc]
          exact compileWord_nodes_w d rels w q hq
        rw [List.getElem?_eq_some_iff] at h
        obtain ⟨_, h⟩ := h
        rw [h]
        obtain ⟨l, a, he, ha⟩ :=
          wordNodes_getElem (2 + (chains 2 (laws d ++ rels)).1.length) (by omega) w q hq
        rw [he, nodeOk_app, compileWord_m, compileWord_arityOf d rels w _ (letterCode_lt l)]
        refine ⟨letterCode_lt l, rfl, ?_⟩
        intro a' ha'
        simp only [List.mem_singleton] at ha'
        omega
  · rw [hlen, compileWord_t]; omega
  · intro ij hij
    simp only [compileWord, List.mem_append, List.mem_singleton, List.mem_map] at hij
    rcases hij with (rfl | ⟨ρ, hρ, rfl⟩) | rfl
    · rw [hlen]; constructor <;> omega
    · have := hlr ρ hρ
      rw [hlen]; constructor <;> omega
    · rw [hlen]; constructor <;> omega
  · unfold guardOk
    rw [List.any_eq_true]
    refine ⟨(0, 1), by simp [compileWord], ?_⟩
    simp [compileWord]

end compiled

/-! ### Semantic agreement with `compilerTests` -/

/-- `false ↦ 0`, `true ↦ 1`. -/
def boolFin2 : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv := by decide
  right_inv := by decide

section semantics
variable (d : ℕ) (rels : List (List (Letter (Fin d)))) (w : List (Letter (Fin d)))

theorem compileWord_m' : d * 2 = (compileWord d rels w).m := by
  rw [compileWord_m, mul_comm]

/-- The signature equivalence from the abstract compiler signature to the encoded one. -/
def compileSig : SigEquiv Bool (Letter (Fin d)) (fun _ => 1)
    (Fin (compileWord d rels w).k) (Fin (compileWord d rels w).m) (compileWord d rels w).arity where
  eV := boolFin2
  eF := ((Equiv.prodCongr (Equiv.refl (Fin d)) boolFin2).trans finProdFinEquiv).trans
    (finCongr (compileWord_m' d rels w))
  har := by
    intro l
    show (compileWord d rels w).arityOf _ = 1
    apply compileWord_arityOf
    have : ((((Equiv.prodCongr (Equiv.refl (Fin d)) boolFin2).trans finProdFinEquiv).trans
        (finCongr (compileWord_m' d rels w))) l).1 = letterCode l := by
      simp [boolFin2, letterCode, finProdFinEquiv_apply_val]
      split <;> rfl
    rw [this]
    exact letterCode_lt l

theorem compileSig_eF_val (l : Letter (Fin d)) : ((compileSig d rels w).eF l).1 = letterCode l := by
  simp [compileSig, boolFin2, letterCode, finProdFinEquiv_apply_val]
  split <;> rfl

theorem compileSig_eV_false : ((compileSig d rels w).eV false).1 = 0 := rfl
theorem compileSig_eV_true : ((compileSig d rels w).eV true).1 = 1 := rfl

/-- A list of nodes sits at consecutive positions from `s`. -/
def Segment (γ : Instance) (ns : List Node) (s : ℕ) : Prop :=
  ∀ p (hp : p < ns.length), γ.nodes[s + p]? = some ns[p]

theorem Segment.append_left {γ : Instance} {ns ms : List Node} {s : ℕ}
    (h : Segment γ (ns ++ ms) s) : Segment γ ns s := by
  intro p hp
  have := h p (by simp; omega)
  rwa [List.getElem_append_left hp] at this

theorem Segment.append_right {γ : Instance} {ns ms : List Node} {s : ℕ}
    (h : Segment γ (ns ++ ms) s) : Segment γ ms (s + ns.length) := by
  intro p hp
  have := h (ns.length + p) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  rw [Nat.add_assoc]
  simpa using this

theorem compileWord_termD_zero (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).termD hv 0 = (compileSig d rels w).rename (.var false) := by
  have h := compileWord_nodes_zero d rels w
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨hi, hta⟩ := (compileWord d rels w).decode_src hv 0 0 h0 h
  rw [hta]
  exact congrArg Term.var (Fin.ext (compileSig_eV_false d rels w).symm)

theorem compileWord_termD_one (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).termD hv 1 = (compileSig d rels w).rename (.var true) := by
  have h := compileWord_nodes_one d rels w
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨h0, h⟩ := h
  obtain ⟨hi, hta⟩ := (compileWord d rels w).decode_src hv 1 1 h0 h
  rw [hta]
  exact congrArg Term.var (Fin.ext (compileSig_eV_true d rels w).symm)

theorem wordNodes_termD (hv : (compileWord d rels w).Valid) (s : ℕ)
    (v : List (Letter (Fin d))) (hseg : Segment (compileWord d rels w) (wordNodes s v).1 s) :
    (compileWord d rels w).termD hv (wordNodes s v).2 =
      (compileSig d rels w).rename (wordTerm v) := by
  induction v with
  | nil =>
      simp only [wordNodes, wordTerm]
      exact compileWord_termD_zero d rels w hv
  | cons l v ih =>
      have ih' := ih (by
        have := hseg
        simp only [wordNodes] at this
        exact this.append_left)
      have hlast := hseg (wordNodes s v).1.length (by simp [wordNodes])
      simp only [wordNodes] at hlast
      rw [List.getElem_append_right (le_refl _)] at hlast
      simp only [Nat.sub_self, List.getElem_singleton] at hlast
      rw [List.getElem?_eq_some_iff] at hlast
      obtain ⟨hj, hnd⟩ := hlast
      obtain ⟨hf, hlen, _, hta⟩ := (compileWord d rels w).decode_app hv _ _ _ hj hnd
      simp only [wordNodes]
      rw [hta]
      simp only [wordTerm, SigEquiv.rename]
      apply Term.app_congr
      · exact Fin.ext (compileSig_eF_val d rels w l).symm
      · intro i j _
        have hi : i.1 = 0 := by
          have := i.2
          simp only [List.length_singleton] at hlen
          omega
        simp only [hi, List.getD_cons_zero]
        exact ih'

theorem chains_termD (hv : (compileWord d rels w).Valid) (s : ℕ)
    (vs : List (List (Letter (Fin d))))
    (hseg : Segment (compileWord d rels w) (chains s vs).1 s) :
    (chains s vs).2.map ((compileWord d rels w).termD hv) =
      vs.map (fun v => (compileSig d rels w).rename (wordTerm v)) := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
      simp only [chains] at hseg ⊢
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨wordNodes_termD d rels w hv s v hseg.append_left,
        ih (s + (wordNodes s v).1.length) hseg.append_right⟩

theorem compileWord_segment_lr :
    Segment (compileWord d rels w) (chains 2 (laws d ++ rels)).1 2 :=
  fun p hp => compileWord_nodes_lr d rels w p hp

theorem compileWord_segment_w :
    Segment (compileWord d rels w)
      (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1
      (2 + (chains 2 (laws d ++ rels)).1.length) :=
  fun p hp => compileWord_nodes_w d rels w p hp

theorem compilerTests_eq :
    compilerTests d rels w =
      [(.var false, .var true)] ++ (laws d ++ rels).map (fun v => (wordTerm v, .var true)) ++
        [(wordTerm w, .var false)] := by
  simp [compilerTests, laws, List.map_map, Function.comp_def]

/-- The decoded tests are the renamed compiler tests, entry by entry. -/
theorem compileWord_testTerms (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).testTerms hv =
      (compilerTests d rels w).map
        (fun uv => ((compileSig d rels w).rename uv.1, (compileSig d rels w).rename uv.2)) := by
  rw [compilerTests_eq]
  unfold testTerms
  rw [compileWord_tests]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def]
  rw [compileWord_termD_zero, compileWord_termD_one,
    wordNodes_termD d rels w hv _ w (compileWord_segment_w d rels w)]
  congr 2
  have := chains_termD d rels w hv 2 (laws d ++ rels) (compileWord_segment_lr d rels w)
  have e1 : (chains 2 (laws d ++ rels)).2.map
      (fun x => ((compileWord d rels w).termD hv x, (compileSig d rels w).rename (.var true))) =
      ((chains 2 (laws d ++ rels)).2.map ((compileWord d rels w).termD hv)).map
        (fun u => (u, (compileSig d rels w).rename (.var true))) := by
    rw [List.map_map]; rfl
  rw [e1, this, List.map_map, ← List.map_append]
  rfl

theorem compileWord_outTerm (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).outTerm hv = (compileSig d rels w).rename (.var false) :=
  compileWord_termD_zero d rels w hv

theorem compileWord_xv (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).xv hv = (compileSig d rels w).eV false := Fin.ext rfl

theorem compileWord_yv (hv : (compileWord d rels w).Valid) :
    (compileWord d rels w).yv hv = (compileSig d rels w).eV true := Fin.ext rfl

/-- The decoded dispersion equals the existing hard instance's dispersion on every alphabet. -/
theorem compileWord_dispersion (hv : (compileWord d rels w).Valid) (n : ℕ) :
    (compileWord d rels w).dispersion hv n =
      dispersionOn (A := Fin n) false true (.var false) (compilerTests d rels w) := by
  unfold Instance.dispersion
  rw [compileWord_xv, compileWord_yv, compileWord_outTerm, compileWord_testTerms]
  exact (compileSig d rels w).dispersionOn_rename false true (.var false) (compilerTests d rels w)

/-- The common encoded hardness statement. -/
theorem Lower_compileWord_iff : (compileWord d rels w).Lower ↔ HardThreshold d rels w := by
  unfold Instance.Lower HardThreshold
  constructor
  · rintro ⟨hv, n, hn, h⟩
    rw [compileWord_dispersion] at h
    exact ⟨n, hn, h⟩
  · rintro ⟨n, hn, h⟩
    refine ⟨compileWord_valid d rels w, n, hn, ?_⟩
    rw [compileWord_dispersion]
    exact h

theorem Lower_compileWord_iff_quotient :
    (compileWord d rels w).Lower ↔ HasFiniteQuotient rels w :=
  (Lower_compileWord_iff d rels w).trans (hard_threshold_iff_quotient d rels w)

/-- Test count of the compiled instance. -/
theorem compileWord_tests_length :
    (compileWord d rels w).tests.length = 2 * d + rels.length + 2 := by
  rw [compileWord_tests]
  simp [chains_roots_length, laws]
  omega

/-- Node count of the compiled instance: two sources plus one node per letter. -/
theorem compileWord_nodes_length' :
    (compileWord d rels w).nodes.length = 2 + 4 * d + (rels.map List.length).sum + w.length := by
  rw [compileWord_nodes_length, chains_length]
  simp [laws, Function.comp_def, List.map_const', List.sum_replicate, List.length_finRange]
  omega

end semantics

end Encoded
end DisequalityDispersion
