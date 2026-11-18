# The 192-state NF machine and the set-theory proofs

The selected 192-state, two-symbol countdown machine halts on a blank tape exactly when first-order New Foundations proves a contradiction. Lean 4.35.0 checked the equivalence for the literal transition table. The proof also relates its machine calculus to FunctionNF and CombNF.

## The machine

- [Informal proof (PDF)](NF192_informal_proof.pdf) · [Read the proof on GitHub](COUNTDOWN-PROOF.md)
- [Transition table](NF_192_countdown.tm) · [Main Lean theorem](NF192Countdown.lean) · [Complete Lean sources and build instructions](NF192_Lean_sources.zip)
- [Full verification package with offline proof certificates](/wlad-svennik/notes/releases/tag/nf192-countdown)

## The seven theories

[Download the original Lean project](nf-interp.zip) or [consult the theorem-by-theorem index](SET-THEORY-PROOFS.md). The submitted development covers NF, FunctionNF, CombNF, M, MAC, M+H and NFU + Infinity. The index identifies the precise formulation of H used in the Lean development. The archive includes the original proof notes and recorded checks.

## NF consistency exposition

- [NF consistency exposition](nf_consistency_exposition.pdf) · [TeX source](nf_consistency_exposition.tex) · [Earlier supplied draft](nf_consistency_exposition_earlier_draft.pdf)

The expositions retain their own statements of scope, references, and attributions. The machine source archive records the provenance and licenses of code used in its verification.
