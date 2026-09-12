# Coverage: obligations of `CLAUDE/MACHINE_RUNTIME_PROMPT_2026-09-10.md` → compiled theorems

All names are in namespace `DisequalityDispersion.Machine` unless stated otherwise; the modules are
in `CLAUDE_WORK/MACHINE_RUNTIME_2026-09-10/LEAN/`. "Axioms" refers to
`RETURN/logs/AuditMachineRuntime.log`: every theorem below depends only on `propext`,
`Classical.choice`, `Quot.sound`.

## §2 Exact result required

| obligation | theorem(s) | module |
|---|---|---|
| One fixed finite program on a standard machine model | `program : List Instr := Cmd.compile mainM 0` (4122 instructions, fixed; `programSize`) | `MMain`, `MExamples` |
| Fixed constants `C ≥ 1`, `c`, independent of `bs`, `k`, `g`; halting on **every** `bs` with output `decideBits bs`; `≤ C (bs.length+1)^c` steps | `program_polynomial` (steps `n` and logarithmic cost `t` both `≤ C * (bs.length + 1) ^ c`) | `MMain` |
| Explicit step bound | `program_run` (`n ≤ mainB bs.length`), `mainM_spec`, `decideM_spec` | `MMain` |
| Acceptance ↔ `StrictBits bs` via `decideBits_iff_StrictBits` | `program_accepts_iff` | `MMain` |
| Variable `k` (binary) rather than one algorithm per degree | `k` is parsed from the input (`decodeInputM_spec`, `RepKG`), stored in cell `KV` (`loadInstM_spec`), used only in `1 < k` and `k < ρ` (`decideM`) | `MParseRec`, `MValid`, `MMain` |
| Malformed, truncated, noncanonical, trailing inputs | `decodeInputM_spec`/`InputResult` (`OK = 0` exactly when `decodeInput bs = none`), the `OK ≠ 1` branch of `mainM_spec`; examples `run_empty`, `run_one`, `run_zero` (kernel), trailing/malformed/`hugeCount` (`#eval`) | `MParseRec`, `MMain`, `MExamples` |
| I/O convention, initialisation, halting, what a step is | `inputMem`, `initCfg`, `initM`/`initM_spec`, `Halted`/`program_halted`, `step`/`Run` (one instruction = one step) | `MachineLib`, `Ram`, `MMain` |
| Preprocessing and representation conversion charged | `initM` (7 steps), `decodeInputM` (parse into records), `loadInstM` (42 steps) are parts of `mainM` and counted in `mainB` | `MMain` |
| No classical noncomputability hypothesis, no unproved simulation/cost/size/termination assumptions | `program_polynomial` has no hypotheses; audit shows standard axioms only | `MMain`, audit |

## §3 A genuine machine model

| obligation | where |
|---|---|
| Standard model with explicitly justified logarithmic/bit cost | `Ram.lean`: AHU-style RAM, `Instr`, `Prim.exec`, `Prim.cost`, `Cond.cost`, `step`, `Run`; module header documents the instruction set and the cost convention |
| Primitive transitions perform elementary operations only (no parser/flow/`decideBits` oracle) | `Prim` has `const, mov, load, store, add, sub`; `Instr` adds `jmp, jcond, halt`; `Prim.exec`/`Prim.cost` are the semantics |
| Large integer arithmetic, list equality, allocation, random access charged by representation | values are single cells charged by bit length (`Prim.cost`); lists are arrays scanned element by element (`anyM_spec`, `allM_spec`, `memPairM_spec`, `eqTest_spec` only on two cells); allocation is `add HP HP …` (charged); random access is `load`/`store` charged by the bits of the address value |
| Intermediate language with proved polynomial-overhead simulation | `Cmd` with `Cmd.Exec` counting RAM steps; `compile_correct` (same step count, exact simulation) — `Machine.lean` |
| Cost from step count | `Run.bounded`, `Run.cost_le` (`t ≤ n (1 + 2 (b₀ + n))`), `inputMem_bounded`, `mainM_constMax`, `program_constBound` — `Ram.lean`, `MachineLib.lean`, `MMain.lean` |

## §4 Building on the existing theorems

| existing result | how it is used |
|---|---|
| `decideBits_iff_StrictBits`, `decodeInput_eq_some_iff`, `decodeInput_sizes` (`Parsing.lean`) | `program_accepts_iff`; `sized_of_decode` (size bound `Sized bs.length g` from `decodeInput_sizes`) |
| `strictDecideP` (`FlowCut.lean`) | `decideM_spec` proves `RES = bitv (g.strictDecideP k)` by mirroring its case structure |
| `Instance.canonIds`, `firstIndex_spec` (`EncodedSyntax.lean`) | `canonIdsM_spec`, `firstIndexM_spec`, `find?_eq_firstIndex` |
| `GInstance.networkL`, `rhoFlowL` (`FlowCut.lean`) | `netM_spec` (`NetCtx`), `rhoM_spec` (`VAL = rhoFlowL ids`) |
| `Network.maxflow`, `layersAux`, `newFront`, `seen`, `extractR`/`descendR`, `augPath`, `steps`, `augment`, `ffAux` (`UnitFlow.lean`) | `layers_eq`/`layerState`, `layersM_spec`, `seenTest_spec`, `augPath_eq`/`exStep`, `augPathM_spec`, `steps_eq_range`/`stepsM_spec`, `augmentM_spec`, `ffAux_eq`/`maxflow_eq`, `ffM_spec` |
| size bounds (`EncodingCost.lean`, `FlowCost.lean`) | `sized_sizeG` (from `sources_length_le`, …, `nodeC_le_of_mem`, `outs_length_le`); machine-side bounds `arcs_length_le`, `netNodes_length_le`, `seen_length_le`, `augPath_length_le`, `ffStep_iterate_length` |
| charged-cost theorems (`decodeInputC_le`, `decideBitsC_le_all`, `strictDecidePC_le`, `decideBitsM_steps`) | **not** relabelled; the machine bounds are proved independently for the machine program (`mainB`); the `Costed` results are untouched |

Route actually taken (§4 list): (1) binary numerals in cells, arrays and records for lists/pairs/
nodes/instance (`MParseList.lean` `Rep*`, `MParseRec.lean`); (2) primitive routines with step
bounds (`MLib*.lean`: `anyM`, `allM`, `filterM`, `mapM`, `appendM`, `flattenM`, `dedupM`, `memPairM`,
`rangeM`, `eqTest`, `ltTest`, …); (3) bounds on all reachable representations through the
`RSpec`/`Agree`/`ArrIs`/`PArrIs`/`RecsIn` invariants and the explicit size bounds above; (4) the
phases `decodeInputM`, `gValidM`, `canonIdsM`, `testsDistinctM`, `netM`, `rhoM`; (5) `mainM_spec`,
`program_run`, `program_polynomial`, `program_accepts_iff`.

## §5 Points handled explicitly

| point | evidence |
|---|---|
| Large labels / binary `k`: bit lengths bounded, values not assumed polynomial | `Prim.cost` charges bit lengths; `Run.bounded`; the parser's step bound is in the number of input bits (`ParserSpec`); example `encodeInput (2^40) sharedG` runs in 139061 steps |
| Truncated list with enormous count fails after the supplied data | `decodeListM_pspec` (bound `S (remaining+1)^d`), `listLoop_spec`; example `hugeCount` (961 steps) |
| Canonical identities of equal subterms; shared symbols, repeated outputs/arguments, nullaries, unused sources, test-only terms | `canonIdsM_spec` computes exactly `Instance.canonIds`; `netM_spec` computes exactly `networkL ids`; example `sharedG` (accepted after identification), `dupInstance` (rejected) |
| Canonicalisation/network only after validation; degrees `< 2` and invalid records rejected as the language requires | `decideM` control structure; `decideM_spec` case analysis (`hk : 2 ≤ k`, `hv : g.isValid`, `hd : testsDistinct`) |
| Nested scans, comparisons, traversal, copying, counters, recomputed layers, path construction, repeated closures charged | every `RSpec`/`TestSpec` carries a step bound; loops via `forLoop_spec`/`loopR_spec`/`forEachM_spec`/`forEachRevM_spec`; the flow loop recomputes layers each round (`ffBody_spec`) |
| No loop to the value of `k`, no enumeration of interpretations, no `s^(k+1)` | the program text `mainM` (only list-length/arc-count loops; `k` appears only in two comparisons) |
| Bounds for all reachable executions including rejected inputs | `mainM_spec` (every `bs`), `decideM_spec` (every branch) |
| Not a theorem about an unrelated cost expression / instrumented charge | `program_polynomial` is about `Run program (initCfg bs) …` |

## §6 Verification and evidence

| item | evidence |
|---|---|
| Pinned Lean/dependency versions | `lean-toolchain` = `leanprover/lean4:v4.26.0`; `lake-manifest.json` unchanged (Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) |
| Machine-level examples: successful and unsuccessful decisions, malformed/noncanonical/trailing, huge truncated counts, large binary degrees, shared subterms | `MExamples.lean` (`run_empty`, `run_one`, `run_zero` kernel-checked; `pure_decisions` kernel-checked; `#eval` runs listed in the report §6, with the proved evaluation contract `runA_program`) |
| Full build, normal configuration, original imports | `lake build` in the extension (`RETURN/logs/lake_build.log`, `timeline.txt`) |
| Three existing audits + type listing, plus `AuditMachineRuntime.lean`, `TypesMachineRuntime.lean` | `RETURN/logs/Audit.log`, `AuditClaude.log`, `AuditGeneral.log`, `TypesGeneral.log`, `AuditMachineRuntime.log`, `TypesMachineRuntime.log` |
| No `sorry`/`admit`/`sorryAx`/custom axioms/`unsafe`/`native_decide` | audit log (no `sorryAx`); `RETURN/logs/grep_forbidden.log` |
| Progress checkpoint | `RETURN/STATE.md` (and the session's `PROGRESS.md` history summarised there) |

## What the paper may now claim

The Lean development proves, in addition to the existing correctness of the decision procedure,
that there is a single deterministic random-access machine program (logarithmic cost criterion) which,
on every input bit string `bs` of the existing encoding, halts with the answer `decideBits bs`, hence
accepts exactly the language `StrictBits`, within `C * (|bs| + 1)^c` machine steps and within
`C * (|bs| + 1)^c` total logarithmic cost, for fixed constants `C ≥ 1` and `c`
(`program_polynomial`, `program_accepts_iff`). The polynomial-time claim of Section 8 is therefore
machine-certified for this model; the constants are not optimised. Under the standard polynomial
simulations between the logarithmic-cost RAM and multitape Turing machines (a textbook result that
is *not* formalised here), this gives membership in P in the Turing-machine sense; if the paper wants
the statement in machine-certified form, it should state it for the log-cost RAM. The classical
finite-group noncomputability input to the undecidability results remains external, exactly as
before.
