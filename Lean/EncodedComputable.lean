import EncodedCompiler
import Mathlib.Computability.Halting

/-! # Computability of the hard compiler and noncomputability of `Lower` (T3)

`Instance` and `Node` are given `Primcodable` structures through explicit
equivalences with nested products, sums and lists of naturals; the compiler
`compileWord d rels` is shown primitive recursive under these encodings by
building it from mathlib's `Primrec` combinators.  Combined with the explicit
classical hypothesis (a fixed finite presentation with noncomputable finite-
quotient separation) this yields the noncomputability of `Lower` on the
general encoded C3 class. -/

namespace DisequalityDispersion.Encoded

/-- Nodes as a sum type. -/
def Node.equiv : Node ≃ ℕ ⊕ (ℕ × List ℕ) where
  toFun
    | .src i => .inl i
    | .app f args => .inr (f, args)
  invFun
    | .inl i => .src i
    | .inr p => .app p.1 p.2
  left_inv := by intro n; cases n <;> rfl
  right_inv := by intro s; rcases s with i | ⟨f, args⟩ <;> rfl

instance : Primcodable Node := Primcodable.ofEquiv _ Node.equiv

/-- Instances as nested tuples. -/
def Instance.equiv :
    Instance ≃ List ℕ × List (ℕ × ℕ) × List Node × ℕ × ℕ × ℕ × List (ℕ × ℕ) where
  toFun γ := (γ.sources, γ.symbols, γ.nodes, γ.x, γ.y, γ.t, γ.tests)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv := by intro γ; rfl
  right_inv := by intro p; rfl

instance : Primcodable Instance := Primcodable.ofEquiv _ Instance.equiv

theorem primrec_nodeApp : Primrec₂ Node.app := by
  have : Primrec fun p : ℕ × List ℕ => Node.equiv.symm (Sum.inr p) :=
    Primrec.of_equiv_symm.comp Primrec.sumInr
  exact this.of_eq (fun p => rfl)

theorem primrec_letterCode {d : ℕ} : Primrec (letterCode (d := d)) := by
  have h1 : Primrec fun l : Letter (Fin d) => bif l.2 then (1 : ℕ) else 0 :=
    Primrec.cond Primrec.snd (Primrec.const 1) (Primrec.const 0)
  have h2 : Primrec fun l : Letter (Fin d) => 2 * l.1.1 :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fin_val.comp Primrec.fst)
  have h3 := Primrec.nat_add.comp h1 h2
  refine h3.of_eq (fun l => ?_)
  unfold letterCode
  cases l.2 <;> rfl

section
variable (d : ℕ)

theorem wordNodes_eq_foldr (s : ℕ) (w : List (Letter (Fin d))) :
    wordNodes s w = w.foldr
      (fun l p => (p.1 ++ [Node.app (letterCode l) [p.2]], s + p.1.length)) ([], 0) := by
  induction w with
  | nil => rfl
  | cons l w ih => simp [wordNodes, ih]

theorem primrec_wordNodes (s : ℕ) : Primrec (wordNodes (d := d) s) := by
  have hl : Primrec fun p : List (Letter (Fin d)) × (Letter (Fin d) × (List Node × ℕ)) => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hns : Primrec fun p : List (Letter (Fin d)) × (Letter (Fin d) × (List Node × ℕ)) =>
      p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec fun p : List (Letter (Fin d)) × (Letter (Fin d) × (List Node × ℕ)) =>
      p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hnode : Primrec fun p : List (Letter (Fin d)) × (Letter (Fin d) × (List Node × ℕ)) =>
      Node.app (letterCode p.2.1) [p.2.2.2] :=
    primrec_nodeApp.comp (primrec_letterCode.comp hl)
      (Primrec.list_cons.comp hr (Primrec.const []))
  have h1 : Primrec fun p : List (Letter (Fin d)) × (Letter (Fin d) × (List Node × ℕ)) =>
      p.2.2.1 ++ [Node.app (letterCode p.2.1) [p.2.2.2]] :=
    Primrec.list_concat.comp hns hnode
  have h2 : Primrec fun p : List (Letter (Fin d)) × (Letter (Fin d) × (List Node × ℕ)) =>
      s + p.2.2.1.length :=
    Primrec.nat_add.comp (Primrec.const s) (Primrec.list_length.comp hns)
  have hstep : Primrec₂ fun (_ : List (Letter (Fin d))) (q : Letter (Fin d) × (List Node × ℕ)) =>
      (q.2.1 ++ [Node.app (letterCode q.1) [q.2.2]], s + q.2.1.length) :=
    Primrec₂.mk (Primrec.pair h1 h2)
  have := Primrec.list_foldr Primrec.id (Primrec.const (([] : List Node), (0 : ℕ))) hstep
  refine this.of_eq (fun w => ?_)
  rw [wordNodes_eq_foldr]
  rfl

theorem primrec_compileWord (rels : List (List (Letter (Fin d)))) :
    Primrec (compileWord d rels) := by
  have hwn := primrec_wordNodes d (2 + (chains 2 (laws d ++ rels)).1.length)
  have hnodes : Primrec fun w : List (Letter (Fin d)) =>
      [Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1 ++
        (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1 :=
    Primrec.list_append.comp
      (Primrec.const ([Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1))
      (Primrec.fst.comp hwn)
  have htests : Primrec fun w : List (Letter (Fin d)) =>
      [((0 : ℕ), (1 : ℕ))] ++ (chains 2 (laws d ++ rels)).2.map (fun ρ => (ρ, 1)) ++
        [((wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).2, 0)] :=
    Primrec.list_append.comp
      (Primrec.const ([((0 : ℕ), (1 : ℕ))] ++ (chains 2 (laws d ++ rels)).2.map (fun ρ => (ρ, 1))))
      (Primrec.list_cons.comp (Primrec.pair (Primrec.snd.comp hwn) (Primrec.const 0))
        (Primrec.const []))
  have htuple : Primrec fun w : List (Letter (Fin d)) => Instance.equiv.symm
      ([0, 1], (List.range (2 * d)).map (fun s => (s, 1)),
        [Node.src 0, Node.src 1] ++ (chains 2 (laws d ++ rels)).1 ++
          (wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).1,
        0, 1, 0,
        [((0 : ℕ), (1 : ℕ))] ++ (chains 2 (laws d ++ rels)).2.map (fun ρ => (ρ, 1)) ++
          [((wordNodes (2 + (chains 2 (laws d ++ rels)).1.length) w).2, 0)]) :=
    Primrec.of_equiv_symm.comp
      (Primrec.pair (Primrec.const _) (Primrec.pair (Primrec.const _) (Primrec.pair hnodes
        (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const 1)
          (Primrec.pair (Primrec.const 0) htests))))))
  exact htuple.of_eq (fun w => rfl)

theorem computable_compileWord (rels : List (List (Letter (Fin d)))) :
    Computable (compileWord d rels) :=
  (primrec_compileWord d rels).to_comp

/-- Under the explicit classical hypothesis for one fixed finite presentation,
`Lower` is not computable on general encoded C3 inputs. -/
theorem not_computablePred_Lower (rels : List (List (Letter (Fin d))))
    (slobodskoiBridsonWilton : ¬ ComputablePred (HasFiniteQuotient rels)) :
    ¬ ComputablePred Instance.Lower := by
  intro hL
  apply undecidable_hard_threshold d rels slobodskoiBridsonWilton
  obtain ⟨f, hf, hpf⟩ := ComputablePred.computable_iff.mp hL
  refine ComputablePred.computable_iff.mpr
    ⟨fun w => f (compileWord d rels w), hf.comp (computable_compileWord d rels), ?_⟩
  funext w
  rw [← Lower_compileWord_iff d rels w]
  exact congrFun hpf _

end

end DisequalityDispersion.Encoded
