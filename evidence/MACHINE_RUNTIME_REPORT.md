# Machine-model running time for Paper 3 — completion report

Extension: `CLAUDE_WORK/MACHINE_RUNTIME_2026-09-10/` (working copy `LEAN/`, return package `RETURN/`).
Date: 2026-09-11. Author of the extension: Claude (Cowork session), at the request of Søren Riis.
Status: **complete** — the standard-machine theorem applies to the existing language `StrictBits` on
every input bit string, every simulation and size lemma is proved, and the official build and all six
audit/type commands pass (see §7 and `RETURN/logs/`).

## 1. Final theorems (module `MMain.lean`, namespace `DisequalityDispersion.Machine`)

```lean
theorem program_polynomial :
    ∃ (C c : ℕ), 1 ≤ C ∧ ∀ bs : List Bool, ∃ (m' : Mem) (n t : ℕ),
      Run program (initCfg bs) ⟨Cmd.len mainM, m'⟩ n t ∧ Halted program ⟨Cmd.len mainM, m'⟩ ∧
      m' RES = bitv (decideBits bs) ∧ n ≤ C * (bs.length + 1) ^ c ∧ t ≤ C * (bs.length + 1) ^ c
```

`program : List Instr` is one fixed RAM program (`Cmd.compile mainM 0`, 4122 instructions),
`initCfg bs = ⟨0, inputMem bs⟩` is the initial configuration on input `bs`, `Run P c c' n t` is the
reflexive–transitive closure of the single-step relation recording the number of steps `n` and the
total logarithmic cost `t`, `Halted P c'` says the machine has stopped in `c'`, `RES` is the output
cell and `bitv b ∈ {0, 1}` the numeral of a Boolean. The constants `C ≥ 1` and `c` are fixed by the
proof (they come from the closure of polynomial bounds under `+`, `*` and composition with the
explicit step bound `mainB`), independent of `bs`, `k` and `g`. Both the number of machine steps
`n` and the logarithmic cost `t` are bounded by the same `C * (bs.length + 1) ^ c`.

```lean
theorem program_run (bs : List Bool) :
    ∃ (m' : Mem) (n t : ℕ), Run program (initCfg bs) ⟨Cmd.len mainM, m'⟩ n t ∧
      Halted program ⟨Cmd.len mainM, m'⟩ ∧ m' RES = bitv (decideBits bs) ∧ n ≤ mainB bs.length

theorem program_accepts_iff (bs : List Bool) (m' : Mem) (n t : ℕ)
    (r : Run program (initCfg bs) ⟨Cmd.len mainM, m'⟩ n t) : m' RES = 1 ↔ StrictBits bs
```

`program_run` gives the explicit step bound `mainB bs.length` (a closed polynomial expression, see
§5); `program_accepts_iff` derives acceptance (`RES = 1` at the halting configuration) if and only if
`StrictBits bs` from `decideBits_iff_StrictBits` and determinism of the machine
(`Run.halted_unique`). Both theorems quantify over **every** `bs : List Bool`: malformed, truncated,
noncanonical and trailing inputs are covered (they are rejected, `RES = 0`), and the degree `k` is the
binary number parsed from the input, not a parameter of the program.

Full printed types: `RETURN/logs/TypesMachineRuntime.log`. Axiom dependencies of every theorem in
the new modules: `RETURN/logs/AuditMachineRuntime.log` (655 theorems; only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`, no custom axioms).

## 2. The machine model (`Ram.lean`)

A deterministic random-access machine in the sense of Aho–Hopcroft–Ullman (§1.2) under the
**logarithmic cost criterion**.

* Memory `Mem := ℕ → ℕ`: an unbounded array of cells holding natural numbers; the program is a
  fixed finite list `List Instr`; the configuration `Cfg` is a program counter and a memory.
* Instructions (`Instr`), with direct addressing and one level of indirection:
  `const a c` (`M[a] := c`), `mov a b` (`M[a] := M[b]`), `load a b` (`M[a] := M[M[b]]`),
  `store a b` (`M[M[a]] := M[b]`), `add a b c` (`M[a] := M[b] + M[c]`), `sub a b c`
  (`M[a] := M[b] ∸ M[c]`, truncated), `jmp l`, `jcond (lt a b) l`, `jcond (eq a b) l`, `halt`.
  There are no list primitives, no multiplication, no equality test on structured data: every
  instruction reads and writes a bounded number of cells.
* Step: `step P c` executes the instruction at `c.pc` (`none` if `pc` points at `halt` or outside the
  program). `Run P c c' n t` counts steps `n` and cost `t`.
* Logarithmic cost of an instruction: `1` plus the binary length `bits v = Nat.size v` of every value
  it reads — the contents of the cells it accesses (including the cell whose contents serve as an
  indirect address), the immediate constant of `const`, and the two values compared by a
  conditional jump; `jmp` and `halt` cost `1`. Addresses written in the program and jump targets
  belong to the fixed program and are not charged (as in AHU).
* Cost versus steps (`Run.bounded`, `Run.cost_le`): since the only value-producing operations are
  addition, truncated subtraction, copying and loading constants, after `n` steps every value has
  at most `b₀ + n` bits, where `b₀` bounds the bits of the initial memory and of the program's
  constants; hence the logarithmic cost of a run of `n` steps is at most `n * (1 + 2 * (b₀ + n))`.
  This is how `program_polynomial` obtains the cost bound from the step bound: the input memory has
  values of at most `bits bs.length + 1` bits (`inputMem_bounded`), and the program's largest
  immediate constant is `201` (`mainM_constMax`, checked by kernel evaluation of the program text,
  `constBound_compile`).

**I/O convention.** `inputMem bs` holds `bs.length` in cell `IN = 200` and the bits of `bs` (as
`0`/`1`) in cells `IN + 1, …, IN + bs.length`; every other cell is `0` (in particular the heap
pointer, the constants and all variables are `0` and are initialised by the program itself,
`initM`). The machine starts at `pc = 0`. It halts when the program counter leaves the program
(`program_halted`: `pc = Cmd.len mainM = program.length`); the decision is the value of cell
`RES = 39` (`1` = accept, `0` = reject). Everything the program does — initialisation, parsing,
representation conversion, validation, canonicalisation, network construction, max-flow and the
final comparison — is charged in `n` and `t`.

## 3. The structured layer and the compiler (`Machine.lean`, `MachineLib.lean`)

Programs are written in a structured language `Cmd` (`prim p`, `seq`, `ite b c₁ c₂`, `loop b c`)
with a big-step semantics `Cmd.Exec c m m' k` counting machine steps `k`. `Cmd.compile c s` places
straight-line RAM code at position `s` (conditionals and loops become `jcond`/`jmp`), and
`compile_correct` proves that the compiled code runs exactly as the structured semantics prescribes,
with the same number of steps:

```lean
theorem compile_correct (h : Exec c m m' k) : ∀ P s, CodeAt P s (compile c s) → ∃ t, Run P ⟨s, m⟩ ⟨s + len c, m'⟩ k t
```

So the structured layer is not an intermediate machine with its own cost model: its step count *is*
the RAM step count, and the RAM cost is obtained afterwards by `Run.cost_le`. `MachineLib` fixes
the conventions (heap pointer `HP = 0`, constant `ONE = 1`, variables below `IN = 200`, arrays as
`[length, elements…]`, records as consecutive cells) and proves the counted loop `forLoop_spec` and
the `Pres`/`Arr` preservation lemmas.

## 4. Representation and the verified program (dependency chain)

`mainM := initM; decodeInputM; if OK = 1 then decideM else RES := 0`, where
`decideM := loadInstM; if 1 < k then gValidM; if FLAG then canonIdsM; testsDistinctM; if FLAG then netM; rhoM; ltTest KV VAL; RES := FLAG else RES := 0 …`.

| phase | program | specification | module |
|---|---|---|---|
| initialisation | `initM` | `initM_spec`: 7 steps, establishes the parser state `PState m bs` | `MMain` |
| parsing | `decodeInputM` | `decodeInputM_spec`: ≤ `2100 * (bs.length + 1)^3 + 5` steps; `InputResult`: `OK = 0` if `decodeInput bs = none`, else `OK = 1` and the record `(k, g)` at `VAL` (`RepKG`) | `MParse`, `MParseList`, `MParseRec` |
| loading | `loadInstM` | `loadInstM_spec`: 42 steps, the instance context `InstCtx k g` (globals `KV, SRCS, SYMS, NODES, XV, YV, TV, TESTS, OUTS, NN, KK, MM`) | `MValid` |
| validation | `gValidM` | `gValidM_spec`: `FLAG = g.isValid`, ≤ `validB n = 81 n² + 229 n + 141` steps | `MValid` |
| canonical identities | `canonIdsM` | `canonIdsM_spec`: array `IDS = g.base.canonIds`, ≤ `n (canonB n + 8) + 9` steps | `MCanon` |
| test scan | `testsDistinctM` | `testsDistinctM_spec`: `FLAG = g.base.testsDistinct ids`, ≤ `32 n + 11` steps | `MCanon` |
| network | `netM` | `netM_spec`: `NetCtx k g` — `NETS = netS`, `NETT = netT`, arrays `NETN = netNodesL ids`, `ARCS = (networkL ids).arcs`; ≤ `netB n` steps | `MNet` |
| max-flow and count | `rhoM = ffM; countM` | `rhoM_spec`: `VAL = g.rhoFlowL ids`, ≤ `rhoB n` steps | `MFlow` |
| degree comparison | `ltTest KV VAL; mov RES FLAG` | `k < ρ` i.e. `k + 1 ≤ ρ` | `MMain` |

Here `n` is any size bound `Sized n g` (all list lengths and arities of `g` are `≤ n`); for a
parsed input `Sized bs.length g` holds (`sized_of_decode`, from `decodeInput_sizes`). The
composition is `decideM_spec` (`RES = bitv (g.strictDecideP k)`, ≤ `decideB n` steps) and
`mainM_spec` (`RES = bitv (decideBits bs)`, ≤ `mainB bs.length` steps, for every `bs`). The pure
functions replicated step by step are exactly those of the existing development:
`decodeInput` (`Parsing.lean`), `GInstance.isValid`, `Instance.canonIds`, `Instance.testsDistinct`,
`GInstance.networkL`, `Network.maxflow` (`UnitFlow.lean`: layers `layersAux`/`newFront`, reachability
`seen`, path extraction `extractR`/`descendR`, `augment`, fuelled `ffAux`) and `GInstance.rhoFlowL`
(`FlowCut.lean`); no new pure algorithm was introduced, so `decideBits_iff_StrictBits` applies
unchanged.

Representations in memory. Naturals are single cells (values are charged by their bit length,
never assumed small); lists of naturals are arrays `[len, x₀, …]`; lists of pairs are arrays of
pointers to two-cell records; nodes are tagged records (`[0, i]` for a source, `[1, f, ptr-to-args]`
for an application); the parsed instance is a record of pointers (`RepInstance`, `RepG`, `RepKG` in
`MParseRec.lean`). All heap allocation is by bumping `HP`; every write below `HP` is to a declared
variable of the routine (`Agree m m' V`), and every routine's specification (`RSpec c V B Pre Post`)
records its written variables `V`, its step bound `B`, and the heap-growth invariant, so that data
built by earlier phases is provably intact when later phases read it.

Points required explicitly (all proved, not assumed):

* Large numeric labels and binary `k`: a numeral is one cell; the parser reads its code bit by bit
  (`decodeNatM_spec : ParserSpec decodeNatM decodeNat RepNat natVars 50 1`, i.e. at most
  `50 * (remaining bits + 1)` steps, canonicity check included), and no loop ever runs to the
  *value* of a numeral. The only uses of `k` are the two comparisons `1 < k` and `k < ρ`
  (each one `jcond`, charged `1 + bits k + bits ρ`). The logarithmic cost of large values is
  captured by `Run.cost_le` through the bit-growth argument.
* Huge truncated counts: `decodeListM` (`listLoop_spec`/`decodeListM_pspec`, step bound
  `S * (remaining bits + 1)^d`) reserves the announced array length by a single addition to the heap
  pointer (charged by the bit length of the count, itself bounded by the input length) and its loop
  stops at the first failing element, so a truncated list announcing `2^40` entries is rejected
  after examining the supplied data (example `hugeCount`, 88 bits, 961 steps).
* Canonical identities before the network: `canonIdsM` computes `canonIds` by the same
  first-index scan `firstIndex` as the pure definition (`firstIndexM_spec`), so equal subterms with
  different node names share one identity (example `sharedG`); shared symbols, repeated outputs and
  arguments, nullaries, unused sources and test-only terms are handled exactly as by the pure
  functions since the machine computes those functions.
* Validation before canonicalisation and network construction, degrees below two rejected: the
  control structure of `decideM` mirrors `strictDecideP` literally (`decideM_spec` is a case
  analysis on `2 ≤ k`, `g.isValid`, `testsDistinct`).
* Nested scans, comparisons, traversals, copies, counters, recomputed layers, path construction,
  repeated closures: every routine has an explicit step bound in its `RSpec`/`TestSpec`; loops are
  charged through `forLoop_spec` (`(N - j) * (B + 3) + 2`), scans through `anyM_spec`/`allM_spec`/
  `filterM_spec`/`mapM_spec`/`appendM_spec`/`flattenM_spec`/`dedupM_spec`/`memPairM_spec`, and the
  flow phase recomputes the layers from scratch in each of the `|arcs| + 1` rounds (`ffM_spec`,
  `layersM_spec`, `augPathM_spec`, `stepsM_spec`, `augmentM_spec`) with no assumed sharing.
* No loop to the value of `k`, no enumeration of interpreting functions, no witness alphabet: the
  program text is `mainM` and its only data-dependent loop bounds are list lengths and arc counts.
* Rejected inputs: `mainM_spec` covers `decodeInput bs = none` (the `OK = 0` branch) and every
  rejecting branch of `decideM`; the bound `mainB bs.length` applies to all of them.

## 5. The polynomial bound

The explicit step bound is

```
mainB n = 7 + (2100 (n+1)^3 + 5) + (decideB n + 3)
decideB n = 42 + (validB n + (n (canonB n + 8) + 9) + (32 n + 11) + (netB n + rhoB n + 4)) + 20
```

with `validB`, `canonB` (`MCanon`), `netB` (`MNet`) and `rhoB = ffB + countB` (`MFlow`) closed
polynomial expressions (products and sums of `n`, `arcBound n = n² + 3n + 2`, `nodeBound n = 2n + 2`,
`seenBound n`, `flowBound n = (arcBound n + 1)(2n + 3)`, …). `PolyB f := ∃ C c, 1 ≤ C ∧ ∀ n, f n ≤ C (n+1)^c`
is closed under constants, `n`, `+`, `*`, `∸` and `(n+1)^k` (`PolyB.add`, `PolyB.mul`, …); the tactic
`polyb` (an elaborator following the syntax of the bound) proves `PolyB mainB` and
`PolyB costB` where `costB n = mainB n * (1 + 2 (n + 9 + mainB n))` is the logarithmic-cost bound
obtained from `Run.cost_le` with `b = bits n + 9 ≥ bits (constBound program)`. The exponent is not
optimised (it is far above the paper's `O(N^6)`-type charge bound); the objective is a sound bound
with fixed constants, which is what `program_polynomial` states.

## 6. Machine-level examples (`MExamples.lean`)

* `runFuel` is an executable fuelled interpreter of the RAM, proved sound (`runFuel_sound`: a
  halting fuelled run is a `Run` ending in a `Halted` configuration with the same step count and
  cost). Kernel-checked runs (`decide +kernel`) of `program` on the inputs `[]`, `[1]` (a truncated
  code) and `[0]` (the code of `k = 0` followed by nothing): all halt with `RES = 0`
  (`run_empty`, `run_one`, `run_zero`).
* `runA` is an array-backed interpreter proved to simulate `runFuel` (`stepA_corr`, `runA_corr`,
  `runA_program`: a halting `runA` run on `inputArr bs` yields a `Run` of `program` from `initCfg bs`
  with the same steps, cost and `RES`). It is used with `#eval` (compiled evaluation, **not** a
  kernel check) on the regression instances of the pure development; the pure decisions on the
  same inputs are kernel-checked in `pure_decisions`. Results `(halted, RES, steps, cost, pc)`:

  | input | bits | result |
  |---|---|---|
  | `encodeInput 2 bottleneckG` | 108 | `(true, 1, 137578, 852402, 4122)` accepted |
  | `encodeInput 3 bottleneckG` | | `(true, 0, 137578, 852404, 4122)` rejected (`ρ = 3 < 4`) |
  | `encodeInput 1 bottleneckG` | | `(true, 0, 1910, 10071, 4122)` rejected (`k < 2`, before validation) |
  | `encodeInput 2 dupInstance` | | `(true, 0, 2603, 13561, 4122)` rejected (identical test sides) |
  | `encodeInput 2 sharedG` (duplicated `f(z)` node) | | `(true, 1, 138281, 859971, 4122)` accepted after canonicalisation |
  | `encodeInput (2^40) sharedG` (41-bit degree) | | `(true, 0, 139061, 875220, 4122)` rejected by the final comparison |
  | `encodeInput 2 bottleneckG ++ [1]` (trailing bit) | | `(true, 0, 1886, 9795, 4122)` rejected |
  | `List.replicate 40 true` (malformed) | | `(true, 0, 385, 2280, 4122)` rejected |
  | `hugeCount` (count `2^40`, no data) | 88 | `(true, 0, 961, 7299, 4122)` rejected |

  The `#eval` outputs are in `RETURN/logs/MExamples_eval.log` (dev build) and in the official
  `lake build` log.

## 7. Verification

* Toolchain: Lean `4.26.0` (`lean-toolchain`), Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`lake-manifest.json`, unchanged), all other pins unchanged.
* Official build: `lake build` in the extension project with the normal configuration and the
  original imports (`import Mathlib`), all 71 default targets (the 56 original modules and the 15
  new ones): `RETURN/logs/lake_build.log` (`Build completed successfully (7884 jobs)`), exit codes
  and timestamps in `RETURN/logs/timeline.txt`, details in `RETURN/logs/README.md`. (During
  implementation the modules were compiled one by one in a cloud scaffolding configuration against
  the same Mathlib oleans; that substitute build is not the evidence — the official `lake build`
  above is.)
* Audits and type listings, all run with `lake env lean` on the official build: `Audit.lean`,
  `AuditClaude.lean`, `AuditGeneral.lean`, `TypesGeneral.lean` (the existing four),
  `AuditMachineRuntime.lean` (`#print axioms` for all 655 theorems of the 15 new modules) and
  `TypesMachineRuntime.lean` (`#check` for all 1109 declarations). Logs in `RETURN/logs/`.
* No `sorry`, `admit`, `sorryAx`, custom axioms, `unsafe` or `native_decide` in the new modules
  (`grep` check in `RETURN/logs/grep_forbidden.log`; the kernel-checked examples use
  `decide +kernel`, which is ordinary kernel evaluation, not `native_decide`).
* SHA256 manifests: `RETURN/SHA256SUMS_LEAN_START.txt` (the immutable starting checkpoint, identical
  to `STARTING_MANIFEST_SHA256SUMS.txt`, 63 files) and `RETURN/SHA256SUMS_LEAN.txt` (returned
  sources, 80 files); `RETURN/DIFF_VS_START.md` lists the differences: 17 added files and one
  modified configuration file (`lakefile.toml`, new libraries registered). No original source was
  modified.

## 8. Remaining assumptions or obligations

None for the machine-time theorem: `program_polynomial` and `program_accepts_iff` are unconditional
theorems of the pinned Lean/Mathlib foundations (`propext`, `Classical.choice`, `Quot.sound` only).
The separate classical finite-group noncomputability input of the undecidability results is
untouched and remains explicitly external, as before. The `#eval` demonstrations in
`MExamples.lean` are evaluations, not proofs (the corresponding contract `runA_program` is proved);
the three kernel-checked runs and the general theorem are proofs.
