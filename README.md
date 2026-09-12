# Term coding: Lean verification and interactive paper

Companion to **One Unit Separates Polynomial Time from Undecidability in Term Coding**, by Søren Riis (Paper 3).

- [Read the interactive paper](https://sr123.github.io/term-coding-disequality-lean/).
- [Read the manuscript PDF](paper/paper3.pdf).
- [Browse the unchanged 71-module Lean development](Lean/).
- [Inspect the verification record](site/public/paper/verification.json).
- [Software releases](https://github.com/SR123/term-coding-disequality-lean/releases).

The interactive edition contains the complete paper and 154 authored explanations. Click a paragraph to follow its argument into formal statements, hypotheses, Lean source, recorded proof states and exported kernel expressions. Click the title or “How this paper developed” for the author’s account of the early-2016 Paris visit, the work with Sol Pro and Astra Pro, and the human conceptual contributions concerning disequality constraints and the family of values of k.

The current manuscript is revision 16 (11 September 2026), with the historical account added to the interactive edition on 12 September. The Zenodo DOI will be added after the first software release has been archived. Publication uses the existing verification evidence; it does not claim a new or independently implemented kernel check.

## What is checked

`Lean/` is Claude’s final 71-module development, copied without source edits from the machine-runtime return package. It includes `MMain.program_polynomial` and `MMain.program_accepts_iff`. The 80-file identity record is in `evidence/CLAUDE_SOURCE_IDENTITY.json`.

The companion separates three kinds of material:

- **The manuscript and authored explanations.** These explain the mathematics and the correspondence between notation and Lean. They remain subject to mathematical review.
- **Machine-exported evidence.** Exact types, declaration bodies, expression dependencies, source ranges, and before/after proof states are exported by Lean. English tactic descriptions explain the kind of operation; the recorded states and proof expressions supply the exact details.
- **Foundations and external input.** The fixed-presentation finite-group noncomputability theorem is an explicit hypothesis. The standard polynomial RAM-to-multitape-Turing-machine simulation is not formalised. Neither is disguised as a proved project theorem. The foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

An expression graph is a finite DAG of the actual Lean expressions. Implicit arguments and universe levels are retained. Nonsemantic metadata payloads are omitted, with the underlying expression preserved. Inductive-family references may recur; constructors and recursor computation rules explain these references without suggesting a circular theorem proof. No arbitrary depth limit cuts off the proof explorer. Repeated tactic goal states are stored once per declaration in `stepGoalPool`; each step refers to its before/after states by index. This is lossless sharing of repeated data, not removal of proof steps.

Proof-state text uses Lean’s goal pretty-printer: notation, implicit arguments and large local values may be abbreviated as they are in an editor. The kernel-expression view retains every mathematical expression node and argument, so the complete proof remains available below that readable presentation.

Lean checks an unnamed `example` without retaining it as a module declaration. Its temporary `_example` marker on the keyword is recorded as a checked command, with its source location and proof steps in the module view. It is not treated as a named theorem or a missing proof dependency. All references inside its proof still lead to the corresponding formal declarations.

The browser is an inspection aid, not a replacement kernel. A successful Lean proof establishes its formal statement; it does not by itself prove that a paragraph in English has been translated faithfully. Correspondence notes are provided precisely to make that additional inspection possible.

## Read locally

The prepared static site is in `site/dist/client/`. Serve that directory over HTTP; opening `index.html` as a `file:` URL will not allow the JSON fetches.

```sh
python3 -m http.server 8000 --directory site/dist/client
```

Then visit `http://localhost:8000/`. For editing the website, use:

```sh
cd site
npm ci
npm run dev
```

## Reproduce from source

Requirements: Python 3.11 or later, Node 22.13 or later, Lean via elan/Lake, and a TeX installation with latexmk and the packages used by the manuscript. `Lean/lean-toolchain` and `Lean/lake-manifest.json` pin Lean 4.26.0 and the dependency revisions. Mathlib is pinned to `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

```sh
python3 tools/rebuild.py
```

This builds Claude’s source, re-elaborates it with information trees, exports all project declarations and source-reference targets with their complete dependency closure, runs the six audit/type commands, typesets the paper, joins the correspondence data, checks links and source hashes, and builds the static website. The information-tree pass waits for elaboration tasks and resolves their lazy information trees, with an enlarged elaboration resource budget (`maxHeartbeats = 0`, `maxRecDepth = 100000`); this changes resource limits, not the proof rules. It rejects elaboration errors and unresolved information-tree holes. The documentation exporter is separate from the proof development and is never imported by it.

The first local export required a reset of the accumulated heartbeat counter before exporting Lean’s suggestion metadata. The exporter now performs that reset after proof checking and tracing. This affects documentation metadata, not theorem statements or proof bodies.

`build/trace-report.json`, `build/audits/`, `build/kernel-export.log`, `build/assembly-report.json`, `build/typesetting-report.json` and `build/check-report.json` record the checks. The public verification record is `site/public/paper/verification.json`. Returned Claude build/audit evidence is preserved in `evidence/` and is distinguished from the new local checks.

## GitHub Pages and archival releases

The live edition is served by GitHub Pages at the link above. The Pages workflow builds only the website and publishes its static output; it does not run Lean. The separate **Verify Lean (manual)** workflow is available for a deliberately requested fresh build and audit. The full local reproduction command above additionally regenerates the detailed proof export.

The website is built with `PAPER_BASE_PATH=/term-coding-disequality-lean`, so its assets work under this repository’s GitHub Pages address. A local root build should omit that variable.

Software releases are archived through Zenodo, following papers 1 and 2. A version DOI identifies an archived software snapshot; the live interactive page may subsequently receive editorial updates. The final manuscript cites the archived release and the live page separately.

## Licence and citation

The project software is Apache-2.0, as in papers 1 and 2. See `LICENSE`, `NOTICE.md` and the third-party notices. Manuscript and historical-account licensing is separate. Please cite the paper and software release; `CITATION.cff` supplies the citation metadata.

## File map

- `paper/`: revised manuscript, bibliography and review PDF.
- `Lean/`: unchanged Claude source and pinned configuration.
- `content/`: complete paper structure and authored explanation graph.
- `site/app/`: reader, source-step explorer and kernel-expression explorer.
- `site/public/proof/`: exact exported declarations and full module sources.
- `site/public/paper/`: PDF, source download, public verification record and notices.
- `tools/`: reproducible extractors, assembly, typesetting and checks.
- `evidence/`: Claude’s returned reports and the source identity manifest.

Earlier comments in `GeneralInterface.lean` describe the previous cost-monad result. They are preserved as part of Claude’s source. The interface points readers to the later theorem in `MMain.lean` for the completed machine result.
