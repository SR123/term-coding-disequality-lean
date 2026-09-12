# Proposed replacement for the running-time qualification in Section 8

Conditional on the proved result (`program_polynomial`, `program_accepts_iff` in `MMain.lean`,
official build and audits in `RETURN/logs/`). The canonical manuscript
(`MANUSCRIPT/paper3.tex`, revision 14, SHA256 `67b27dc7…`) is **not** modified; this is a proposal
for the author's review. Line references are to revision 14.

## Current text (lines 912–922)

```latex
For the strict decision algorithm, the development proves correctness
of parsing, rejection of malformed bit strings, and the decision by
max-flow. It also proves polynomial bounds on specified operation costs
and checks that instrumented functions accumulate those costs. A
simulation relating these charges to runtime on a standard Turing
machine or RAM has not been formalised. The ordinary bit-complexity
argument in Section~\ref{sec:mainproof} proves the paper's
polynomial-time claim; a complete machine-level certification of that
claim is not asserted. The source archive's \texttt{AUDIT/COVERAGE.md}
records the precise correspondence, external hypothesis, build evidence
and remaining formalisation limit.
```

## Proposed text

```latex
For the strict decision algorithm, the development proves correctness
of parsing, rejection of malformed bit strings, and the decision by
max-flow, together with polynomial bounds on specified operation costs
accumulated by instrumented functions. In addition, the extension
\texttt{CLAUDE\_WORK/MACHINE\_RUNTIME\_2026-09-10} certifies the
running time on a standard machine model. It formalises a
deterministic random-access machine in the sense of
Aho--Hopcroft--Ullman under the logarithmic cost criterion (memory
cells hold natural numbers; the instructions are constant, copy, load,
store, addition, truncated subtraction, conditional and unconditional
jumps and halt; each instruction is charged one plus the binary length
of every value it reads), and exhibits one fixed program of $4122$
instructions that, started on the binary input string $b$ of the
encoding of Section~\ref{sec:encoding}, halts on every $b$ with the
value of \texttt{decideBits}$(b)$ in its output cell. The theorem
\texttt{program\_polynomial} states that there are constants
$C \ge 1$ and $c$, independent of the input, the degree and the
instance, such that on every input $b$ the program halts within
$C\,(|b|+1)^{c}$ machine steps and within total logarithmic cost
$C\,(|b|+1)^{c}$; the theorem \texttt{program\_accepts\_iff} states
that the program accepts exactly the language \textsc{StrictBits}, by
the previously formalised correctness theorem
\texttt{decideBits\_iff\_StrictBits}. The step bound is obtained from
explicit step bounds for parsing, validation, canonicalisation,
network construction and the augmenting-path max-flow computation of
the same program, and the logarithmic cost is derived from the step
bound by the observation that the machine's values grow by at most
one bit per step. The degree $k$ is read in binary and used only in
two comparisons; no computation loops to its value. The exponent $c$
is not optimised. The passage from the logarithmic-cost RAM to a
multitape Turing machine is the standard polynomial simulation and is
not formalised. The undecidability results continue to assume the
classical finite-group noncomputability input as an external
hypothesis. The source archive's \texttt{AUDIT/COVERAGE.md} and the
extension's \texttt{RETURN/COVERAGE.md} record the precise
correspondence, the external hypothesis and the build evidence.
```

Also to update in the same section if the author wishes: the module count ("all 56 modules") becomes
71 with the extension, and the audits now include `AuditMachineRuntime.lean` and
`TypesMachineRuntime.lean`.
