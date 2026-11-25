# Mathematical software and research

Research notes and computational projects in geometry, linear algebra, automatic differentiation and formal verification.

## Latest NF-family machines

**R. Gutin and E. Glazer — 25 November 2026**

| Target theory | Working states | Literal table | Verification and scope |
| --- | ---: | --- | --- |
| NF | **173** | [NF_173.tm](nf-bb173/NF_173.tm) | [Portable certificates and proof scope](nf-bb173/) |
| NF + full Rosser Axiom of Counting | **182** | [machine.tm](nf-axcount-bb182/machine.tm) | [Portable certificates and calibration audit](nf-axcount-bb182/) |
| NF + full Cantorian Sets | **197** | [NF_CS_197.tm](nf-cs-bb197/NF_CS_197.tm) | [Phase certificate and inherited calibration](nf-cs-bb197/) |

These are the smallest verified implementations in this repository's
reduction series. The counts include blank-tape initialization and all
implementation machinery; the terminal halt state is separate. Each
release includes its original portable archive, exact hashes and
publication replay evidence. Its README distinguishes implementation
verification, inherited written theory calibrations and theory-internal
independence claims.

[Proposed Busy Beaver wiki page and exact insertion markup](wiki/).

## Earlier NF machines and interpretation proofs

[Browse the interpretability and equiconsistency proofs](nf-bb192/interpretations/) for NF, FunctionNF, CombNF, M, MAC, M+H and NFU + Infinity. The [theorem index](nf-bb192/SET-THEORY-PROOFS.md) identifies the statements and their formal scope.

The [192-state countdown machine](nf-bb192/) halts on a blank tape exactly when first-order NF proves a contradiction. The project includes the literal machine, Lean verification, informal proof and original set-theory archive.

## C₀ and 198-state Turing machines

**[Two 198-state machines, proof reports and complete reproducible checkpoints](c0-198/README.md)**

The 11 November 2026 C₀ research includes two binary Turing machines calibrated to inconsistency of C₀, the consistency bounds Con(NF) ⇒ nonhalting ⇒ Con(NFU + Infinity), and a later reverse-interpretation report. The project README states the exact proof and formalization scope.

## New Foundations and Busy Beaver

**[New Foundations and runtime Busy Beaver at 210 states](nf-bb210/README.md)**

A 210-state binary Turing machine and an external Lean 4 proof development about NF. The project includes the machine table, theorem declarations, recorded audit results and the complete source snapshot from 5 November 2026.

The project README states the consistency and soundness assumptions separately and explains how to reproduce the recorded checks.

## Selected software

| Project | Contents |
| --- | --- |
| [Laguerre transformations](https://github.com/wlad-svennik/laguerre_transformations) | Python code and animations for Laguerre geometry. |
| [Linear algebra visualisations](https://github.com/wlad-svennik/la-vis) | A Pygame demonstration of iterative matrix dynamics. |
| [Hyperbolic Laguerre transformations](https://github.com/wlad-svennik/hyperbolic_laguerre_transformations) | Python experiments with transformations of hyperbolic cycles. |
| [Bunch–Parlett factorisation](https://github.com/wlad-svennik/bunchparlett) | A SymPy implementation of LDL factorisation for Hermitian matrices. |
| [Memoized coduals](https://github.com/wlad-svennik/memoized_coduals) | A scalar automatic differentiation experiment using codual numbers. |
