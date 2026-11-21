# A 187-state Turing machine for NF + Rosser’s Axiom of Counting

This binary Turing machine searches for a refutation in a nine-schema calculus. Subject to the written set-theoretic arguments below, it halts from a blank tape exactly when pure New Foundations with full Rosser Counting is inconsistent.

[Transition table](NF_AxCount_Guarded_187.tm) · [Verification archive](NF_AxCount_Guarded_187_Verification.zip) · [Independent replay](NF_AxCount_Guarded_187_Independent_Replay.zip) · [SHA-256 checksums](SHA256SUMS)

## Running the table

Start in `k:74` with a two-way infinite tape of zeros. Each row lists the current state, scanned bit, written bit, direction and next state. The table has 187 graph-reachable working states and 374 transitions. Its sole halting row reads 1 in `k:302`, writes 0 and moves left.

After 233,240 binary steps, the machine reaches register instruction 0 with counter 5 and its eight other registers zero. At this point the physical head is at −10. The earlier counter-2 checkpoint occurs at step 41,865. Both are equalities of complete tape configurations.

## What the verification establishes

The 3,642-instruction register program keeps the eight families of the pure NF machine and adds one guarded law. Let $S(b)$ be $(J(Jb))J=Jb$ and let $C(b,c,d)$ be $bc=bd$. The added schema is $(S(b)\to C(b,c,d))\to C(b,c,d)$. In classical logic, if two entries of the row of $b$ differ, this forces $S(b)$. The code searches for a finite derivation of its refutation goal $JJ=J$.

| Result | Evidence in the archive |
| --- | --- |
| Blank-tape startup and complete transition table | The reconstruction under `build.py`, the two complete configuration equalities in `boot/ScannerFrames.lean`, and the 189-to-187 state reduction under `reduction/`. |
| Register execution on the binary tape | Kernel proofs for 9,552 instruction cases over arbitrary register-field lengths, in 57 batches. Each proof specifies a complete successor configuration or a halting control. The batch hashes and kernel results are in `receipts/kernel.json`. The general positive-clock composition theorem is in `boot/PhysicalRefinement.lean`. Its application identifies the exported two-ray endpoints with the register frames on a two-way tape. |
| Halting of the register program | Lean proves that the literal counter-5 program halts if and only if the nine schemas derive the refutation goal. The theorem is `CountingRefill.GuardedBridge.guarded187_register_halts_iff_goal`. |
| Nonhalting of the register program | Lean proves that nonhalting is equivalent to existence of a guarded chart and implies existence of an NFU model with Dedekind Infinity and $T(n)=n$ for every natural number of that model. See `nonhalting_iff_guarded_chart` and `nonhalting_yields_counting_model` in the same namespace. |

Two written mathematical arguments connect these results to **pure NF + full AxCount**. First, `calculus/UPPER.md` constructs a guarded chart from a pure NF + AxCount model using the stated full-chart and completion hypotheses. Conversely, the NFU model gives consistency of pure NF + AxCount using Proposition 17.13 and the first row of Theorem 21.1 of Ran Gutin’s *Choice and Consistency Strength in NF and NFU*, v15, through their common comparison theory. The manuscript describes these results as self-audited and awaiting independent verification. The verification archive includes the relevant excerpt in `upstream/Jpoint_Calibration.zip`. The pure-theory equivalence depends on these written arguments.

## Independent replay

All 57 regenerated proof batches matched their recorded SHA-256 hashes and passed the Lean 4.35.0 reference kernel. A separate checker read the actual theorem statements and matched all 9,552 branch domains, destinations and symbolic clocks to the literal register program. The independent simulator also matched every tape and clock in 38,208 fixtures that collectively exercised all 374 binary transition rows.

The supplemental Lean theorem `Guarded187.ExportBinding.normalized_iterate_view` identifies an arbitrary finite run of the exported step function with the ordinary tape and control of this literal machine, viewed from its current head. The companion `terminal_iff` identifies its halt code. All 57 batches share the exact machine definitions used for those theorems. A clean Lean 4.35.0 build compiled all 197 project modules against the 14 pinned external packages. Seven endpoint statements and their axiom dependencies were rechecked from that build. The replay archive contains the source, the per-batch results and the commands to repeat the checks.

## Reproducing the checks

From this directory, run the following commands on a system with Python 3 and a C++17 compiler.

```sh
sha256sum -c SHA256SUMS
unzip -q NF_AxCount_Guarded_187_Verification.zip -d verify187
cd verify187
python3 verify.py --examples
```

The example suite compares 174,800 complete successor tapes and 16 halts over 116,048,774 binary transitions. With Lean 4.35.0 and its `leanchecker-paranoid` on the path, run `python3 verify.py --lean --physical --jobs 2` for the startup proof and all physical branches. Run `python3 verify.py --theory --jobs 2` inside the pinned Mathlib environment specified in the archive to rebuild the register and model proofs.
