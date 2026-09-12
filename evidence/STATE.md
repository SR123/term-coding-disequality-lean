# STATE — machine-runtime extension (2026-09-11)

## Status

**Complete.** `program_polynomial` and `program_accepts_iff` (`MMain.lean`) are proved and
compiled; the official `lake build` of the extension (original imports, pinned toolchain and
Mathlib) and all six audit/type commands exit 0 (`RETURN/logs/timeline.txt`).

## Chosen model

Deterministic RAM (AHU §1.2), logarithmic cost criterion (`Ram.lean`); structured layer `Cmd` with
an exact compiler (`Machine.lean`, `compile_correct`, same step count); conventions and library
(`MachineLib.lean`, `MLib.lean`, `MLib2.lean`, `MLib3.lean`).

## Theorem dependency chain

```
program_polynomial
├── program_run
│   ├── mainM_spec
│   │   ├── initM_spec                                   (MMain)
│   │   ├── decodeInputM_spec                            (MParseRec; MParse, MParseList)
│   │   ├── sized_of_decode ← decodeInput_sizes (Parsing), sized_sizeG (EncodingCost, FlowCost)
│   │   ├── goodRep_KG.mono                              (MParseRec)
│   │   └── decideM_spec
│   │       ├── loadInstM_spec                           (MValid)
│   │       ├── gValidM_spec                             (MValid)
│   │       ├── canonIdsM_spec, testsDistinctM_spec      (MCanon)
│   │       ├── netM_spec                                (MNet)
│   │       ├── rhoM_spec = ffM_spec ; countM_spec       (MFlow)
│   │       │   ├── ffBody_spec = layersM_spec ; seenTest_spec ; augPathM_spec ; stepsM_spec ; augmentM_spec
│   │       │   ├── maxflow_eq / ffAux_eq (ffStep iteration), iterate_length_le
│   │       │   └── layers_eq / layerState, augPath_eq / exStep, steps_eq_range, find?_eq_firstIndex
│   │       └── ltTest_spec ; (mov RES FLAG)
│   ├── compile_correct (Machine) with program_codeAt, program_halted
├── polyB_costB ← polyB_mainB ← polyB_decideB ← polyB_validB, polyB_canonB, polyB_netB, polyB_rhoB … (tactic `polyb`)
├── Run.cost_le, inputMem_bounded (Ram, MachineLib)
└── program_constBound ← constBound_compile, mainM_constMax (kernel evaluation of the program text)

program_accepts_iff ← program_run, Run.halted_unique, decideBits_iff_StrictBits (Parsing)
```

## Completed lemmas (by module; counts from `AuditMachineRuntime.lean`)

655 theorems, 454 definitions across `Ram`, `Machine`, `MachineLib`, `MParse`, `MParseList`,
`MParseRec`, `MLib`, `MLib2`, `MLib3`, `MValid`, `MCanon`, `MNet`, `MFlow`, `MMain`, `MExamples`
(about 15,600 lines). Every theorem audited: axioms `propext`, `Classical.choice`, `Quot.sound` only.

## Current failure

None.

## Next concrete lemma

None required for the task. Possible follow-ups (not requested): a multitape Turing-machine
simulation of the log-cost RAM (textbook, not formalised here); a smaller exponent.

## Session history (from the working `PROGRESS.md` checkpoints)

1. `Ram`, `Machine`, `MachineLib`, `MParse`, `MParseList` (parser for naturals and lists).
2. `MLib`, `MLib2` (scans, filters, maps, append, flatten, dedup, pair membership), `MParseRec`
   (records, node/instance/G/pair parsers, `decodeInputM_spec`).
3. `MLib3`, `MValid` (`gValidM_spec`), `MCanon` (`canonIdsM_spec`, `testsDistinctM_spec`), `MNet`
   (`netM_spec`).
4. `MFlow` (`rhoM_spec`; the register `MODE` was renamed `MDE` because `[MOD` is a Mathlib token).
5. `MMain` (`program_polynomial`, `program_accepts_iff`), `MExamples`, audits; official build.
