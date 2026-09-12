import ParsingExec
import FlowCutExec
import GeneralExamples

/-! # Regressions for the polynomial-time decision and the binary front end

Kernel-checked (`decide`/`rfl`) evaluations of the executable definitions on the shared
bottleneck instance, the duplicate-test instance and the parsing boundaries. -/

namespace DisequalityDispersion.Encoded

open GInstance

/-! ### The max-flow decision on the shared bottleneck `(x, y, f(z), g(f(z)))` -/

theorem bottleneckG_rhoFlow : bottleneckG.rhoFlow = 3 := by decide

theorem bottleneckG_strictDecideP2 : bottleneckG.strictDecideP 2 = true := by decide

theorem bottleneckG_strictDecideP3 : bottleneckG.strictDecideP 3 = false := by decide

theorem bottleneckG_strictDecideP1 : bottleneckG.strictDecideP 1 = false := by decide

/-- The flow decision agrees with the exhaustive one on the example (both directions of
`strictDecideP_eq`, evaluated). -/
theorem bottleneckG_agree : bottleneckG.strictDecideP 2 = bottleneckG.strictDecideG 2 ∧
    bottleneckG.strictDecideP 3 = bottleneckG.strictDecideG 3 := by decide

/-! ### The duplicate-test instance: two nodes computing `f(x)` tested against each other -/

theorem dupInstance_strictDecideP : dupInstance.strictDecideP 2 = false := by decide

theorem dupInstance_testsDistinct :
    dupInstance.base.testsDistinct dupInstance.base.canonIds = false := by decide

/-! ### Parsing boundaries -/

/-- A noncanonical zero (`[1,0,0]`, one digit `0`) is rejected; the canonical zero is `[0]`. -/
theorem decodeNat_noncanonical : decodeNat [true, false, false] = none := by decide

theorem decodeNat_zero : decodeNat [false] = some (0, []) := by decide

/-- A digit string with an unset most significant digit is rejected. -/
theorem decodeNat_noncanonical' : decodeNat [true, true, false, true, false] = none := by decide

theorem decodeNat_two : decodeNat [true, true, false, false, true] = some (2, []) := by decide

/-- Exhausted input while counting ones. -/
theorem decodeNat_exhausted : decodeNat (List.replicate 5 true) = none := by decide

/-- An announced count of `2^200` values on empty input fails at once. -/
theorem decodeList_huge_count : decodeList decodeNat (encodeNat (2 ^ 200)) = none := by
  unfold decodeList
  rw [← List.append_nil (encodeNat (2 ^ 200)), bindP_of_eq (decodeNat_encodeNat _ _)]
  rfl

/-- Trailing bits are rejected. -/
theorem decodeInput_trailing : decodeInput (encodeInput 2 bottleneckG ++ [true]) = none := by
  unfold decodeInput
  rw [decodePair'_encodeInput]

/-- The whole-language decision on the encoded bottleneck instance and on a malformed string. -/
theorem decideBits_bottleneck : decideBits (encodeInput 2 bottleneckG) = true := by
  rw [decideBits_encodeInput]; exact bottleneckG_strictDecideP2

theorem decideBits_malformed : decideBits (List.replicate 40 true) = false := by decide

theorem decideBits_empty : decideBits [] = false := by decide

/-- The instrumented parser agrees with the parser on the encoded instance (evaluated). -/
theorem decodeInputM_bottleneck :
    (decodeInputM (encodeInput 2 bottleneckG)).val = some (2, bottleneckG) := by
  rw [decodeInputM_val, decodeInput_encodeInput]

/-! ### The instrumented decision procedure, evaluated by the kernel -/

/-- The instrumented decision (`FlowCutExec.lean`) run on the shared bottleneck: accepts at
`k = 2`, rejects at `k = 3` (the flow value is `3`). -/
theorem strictDecidePM_bottleneck2 : (bottleneckG.strictDecidePM 2).val = true := by decide

theorem strictDecidePM_bottleneck3 : (bottleneckG.strictDecidePM 3).val = false := by decide

/-- The instrumented decision run on the duplicate-test instance rejects before the flow. -/
theorem strictDecidePM_dup : (dupInstance.strictDecidePM 2).val = false := by decide

/-- The instrumented whole-language program on a malformed string. -/
theorem decideBitsM_malformed : (decideBitsM (List.replicate 40 true)).val = false := by decide

/-- The instrumented flow value on the bottleneck (the network is built and the augmenting
paths are run by the kernel). -/
theorem rhoFlowM_bottleneck : (bottleneckG.rhoFlowM bottleneckG.base.canonIds).val = 3 := by decide

/-- The instrumented Phase-A procedures (`PhaseAExec.lean`) run on the bottleneck instance. -/
theorem isValidM_bottleneck : bottleneckG.base.isValidM.val = true := by decide

theorem canonIdsM_bottleneck :
    bottleneckG.base.canonIdsM.val = bottleneckG.base.canonIds := by decide

end DisequalityDispersion.Encoded
