import StrictAlgorithm
import Examples

/-! # Kernel-checked examples for the encoded syntax and the strict procedure

All checks below are closed by `decide` or `rfl` in the kernel (no
`native_decide`).  They supplement, and do not replace, the universal
theorems `strictDecide_iff`, `canonIds_eq_iff`, `usesOther_getD`. -/

namespace DisequalityDispersion.Encoded
open Instance

/-- Three sources, sole guard test, output the third source
(the positive three-source example of `Examples.lean`). -/
def exPos3 : Instance :=
  { sources := [0, 1, 2], symbols := [], nodes := [.src 0, .src 1, .src 2],
    x := 0, y := 1, t := 2, tests := [(0, 1)] }

/-- Three sources, sole guard test, output the retained source `x`
(the negative three-source example of `Examples.lean`). -/
def exNeg3 : Instance :=
  { sources := [0, 1, 2], symbols := [], nodes := [.src 0, .src 1, .src 2],
    x := 0, y := 1, t := 0, tests := [(0, 1)] }

/-- Duplicate DAG nodes denoting the same term `f(x)`, tested against each other:
rejected because the test is an identity. -/
def exDupIdentity : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 1)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [0], .app 0 [0], .app 0 [2]],
    x := 0, y := 1, t := 5, tests := [(0, 1), (3, 4)] }

/-- The same duplicated nodes, but tested against a genuinely different term. -/
def exDupDistinct : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 1)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [0], .app 0 [0], .app 0 [2]],
    x := 0, y := 1, t := 5, tests := [(0, 1), (3, 5)] }

/-- Nullary symbols: two copies of the constant `c` are the same term. -/
def exNullary : Instance :=
  { sources := [0, 1, 2], symbols := [(3, 0), (4, 2)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [], .app 0 [], .app 1 [3, 2]],
    x := 0, y := 1, t := 5, tests := [(0, 1), (3, 4)] }

/-- Nullary symbols tested against a different term; `t = g(c, z)` uses `z`. -/
def exNullaryPos : Instance :=
  { sources := [0, 1, 2], symbols := [(3, 0), (4, 2)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [], .app 0 [], .app 1 [3, 2]],
    x := 0, y := 1, t := 5, tests := [(0, 1), (3, 5)] }

/-- Repeated arguments `g(x, x)` and `g(z, z)`; `t = g(z, z)` uses `z`. -/
def exRepeatedArgs : Instance :=
  { sources := [0, 1, 2], symbols := [(4, 2)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [0, 0], .app 0 [2, 2]],
    x := 0, y := 1, t := 4, tests := [(0, 1), (3, 4)] }

/-- An extra source `z` appearing only in tests; `t = f(x)` uses no other source. -/
def exExtraSourceTestsOnly : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 1)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [0], .app 0 [2]],
    x := 0, y := 1, t := 3, tests := [(0, 1), (3, 4), (2, 0)] }

/-- An actual additional source inside a nontrivial output term `t = g(f(x), z)`. -/
def exAdditionalSourceInT : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 1), (8, 2)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [0], .app 1 [3, 2]],
    x := 0, y := 1, t := 4, tests := [(0, 1), (3, 4)] }

/-- Malformed: missing guard test. -/
def exNoGuard : Instance :=
  { sources := [0, 1, 2], symbols := [], nodes := [.src 0, .src 1, .src 2],
    x := 0, y := 1, t := 2, tests := [(0, 2)] }

/-- Malformed: arity mismatch. -/
def exArityMismatch : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 2)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [0]],
    x := 0, y := 1, t := 3, tests := [(0, 1)] }

/-- Malformed: forward reference (not topologically ordered). -/
def exForwardRef : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 1)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [4], .app 0 [2]],
    x := 0, y := 1, t := 3, tests := [(0, 1)] }

/-- Malformed: `x = y`. -/
def exXeqY : Instance :=
  { sources := [0, 1, 2], symbols := [], nodes := [.src 0, .src 1, .src 2],
    x := 0, y := 0, t := 2, tests := [(0, 0)] }

/-- Malformed: duplicate source names. -/
def exDupSources : Instance :=
  { sources := [0, 0, 2], symbols := [], nodes := [.src 0, .src 1, .src 2],
    x := 0, y := 1, t := 2, tests := [(0, 1)] }

/-- Malformed: a huge declared arity with a short argument list is rejected
without allocating that arity's universe. -/
def exHugeArity : Instance :=
  { sources := [0, 1, 2], symbols := [(7, 1000000000000)],
    nodes := [.src 0, .src 1, .src 2, .app 0 [2]],
    x := 0, y := 1, t := 3, tests := [(0, 1)] }

example : exPos3.strictDecide = true := by decide
example : exNeg3.strictDecide = false := by decide
example : exDupIdentity.strictDecide = false := by decide
example : exDupDistinct.strictDecide = true := by decide
example : exNullary.strictDecide = false := by decide
example : exNullaryPos.strictDecide = true := by decide
example : exRepeatedArgs.strictDecide = true := by decide
example : exExtraSourceTestsOnly.strictDecide = false := by decide
example : exAdditionalSourceInT.strictDecide = true := by decide
example : exNoGuard.strictDecide = false := by decide
example : exArityMismatch.strictDecide = false := by decide
example : exForwardRef.strictDecide = false := by decide
example : exXeqY.strictDecide = false := by decide
example : exDupSources.strictDecide = false := by decide
example : exHugeArity.strictDecide = false := by decide

example : exNoGuard.isValid = false := by decide
example : exArityMismatch.isValid = false := by decide
example : exForwardRef.isValid = false := by decide
example : exXeqY.isValid = false := by decide
example : exDupSources.isValid = false := by decide
example : exHugeArity.isValid = false := by decide
example : exDupIdentity.isValid = true := by decide

/-- Canonical identifiers: duplicate nodes 3 and 4 share an identifier. -/
example : exDupIdentity.canonIds = [0, 1, 2, 3, 3, 5] := by decide
example : exNullary.canonIds = [0, 1, 2, 3, 3, 5] := by decide
example : exRepeatedArgs.canonIds = [0, 1, 2, 3, 4] := by decide

/-- Occurrence flags. -/
example : exAdditionalSourceInT.usesOther = [false, false, true, false, true] := by decide
example : exExtraSourceTestsOnly.usesOther = [false, false, true, false, true] := by decide

theorem exPos3_valid : exPos3.Valid := by decide
theorem exNeg3_valid : exNeg3.Valid := by decide

/-- The decoded positive example is literally the three-source example of
`Examples.lean` (same sources, output and sole guard test). -/
theorem exPos3_decodes : exPos3.testTerms exPos3_valid = pairGuard ∧
    exPos3.outTerm exPos3_valid = .var ⟨2, by decide⟩ := ⟨rfl, rfl⟩

theorem exNeg3_decodes : exNeg3.testTerms exNeg3_valid = pairGuard ∧
    exNeg3.outTerm exNeg3_valid = .var ⟨0, by decide⟩ := ⟨rfl, rfl⟩

/-- Semantic cross-check with the existing examples through the universal
correctness theorem (not through `decide` alone). -/
theorem exPos3_Strict : exPos3.Strict := exPos3.strictDecide_iff.mp (by decide)
theorem exNeg3_not_Strict : ¬ exNeg3.Strict := fun h =>
  Bool.false_ne_true ((by decide : exNeg3.strictDecide = false).symm.trans
    (exNeg3.strictDecide_iff.mpr h))

end DisequalityDispersion.Encoded
