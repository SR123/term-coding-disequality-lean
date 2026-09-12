# Reproduction

Prerequisites: Lean `4.26.0` (`elan` will pick it up from `LEAN/lean-toolchain`), network access to
fetch the pinned Mathlib commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (or a matching
`.lake/packages` cache), and a full Mathlib build (from source, or the matching cache).

```sh
cd CLAUDE_WORK/MACHINE_RUNTIME_2026-09-10/LEAN
sha256sum -c ../STARTING_MANIFEST_SHA256SUMS.txt        # 63 OK: the checkpoint is intact
sha256sum -c ../RETURN/SHA256SUMS_LEAN.txt               # 80 OK: the returned sources
lake build                                               # all 71 default targets (56 original + 15 new)
lake env lean Audit.lean                                 # existing audits and type listing
lake env lean AuditClaude.lean
lake env lean AuditGeneral.lean
lake env lean TypesGeneral.lean
lake env lean AuditMachineRuntime.lean                   # #print axioms for all 655 new theorems
lake env lean TypesMachineRuntime.lean                   # #check for all 1109 new declarations
grep -nE "sorry|admit|native_decide|unsafe|^axiom" Ram.lean Machine.lean MachineLib.lean MParse.lean \
  MParseList.lean MParseRec.lean MLib.lean MLib2.lean MLib3.lean MValid.lean MCanon.lean MNet.lean \
  MFlow.lean MMain.lean MExamples.lean                   # expect no proof-relevant hits (see grep_forbidden.log)
```

Expected: every command exits 0; `AuditMachineRuntime.log` mentions only `propext`,
`Classical.choice`, `Quot.sound`; `lake build` prints the `#eval` results of `MExamples.lean`
(listed in `MACHINE_RUNTIME_REPORT.md` §6).

The final theorems to inspect: `DisequalityDispersion.Machine.program_polynomial`,
`program_run`, `program_accepts_iff` in `MMain.lean` (types in `TypesMachineRuntime.log`).

Timing (cloud run, one core per module): about 2–5 minutes per new module under `lake build` with
full `import Mathlib`; the whole extension build after a cached original build takes under an hour;
the audit files take a few minutes each.
