# A 182-state binary Turing machine for pure NF

Starting on the all-zero tape, this machine halts if and only if pure Quine NF proves a contradiction. It has 182 graph-reachable working states and 364 transitions. The initial state is `k:64`. The terminal state `halt` is counted separately.

[Literal transition table](NF182.tm) · [Complete verification checkpoint](NF182_verification_checkpoint.zip) · [SHA-256 checksums](SHA256SUMS)

## Verification

Five transition changes to the [184-state machine](../nf-bb184/) eliminate `d:127` and `a:CD:1` while preserving the same 2,971-instruction register program. Lean checks that the literal machine reaches a covered register frame from the blank tape at step 51,157. Its default kernel accepted all 7,794 universal branch proofs. An independent C++ replay checked 142,608 complete tapes, including 23 halting cases and 25 continuations at the halt gate. [Kernel receipt](kernel.json) · [Independent replay receipt](frames48.json)

The checkpoint explains how the checked branches and blank-tape result combine with the upstream NF theorem. The final application of the branch family is given as a mathematical argument.

To reproduce the checks, extract the checkpoint and run `python3 verify.py`. Run `python3 verify.py --frames` for the independent tape simulation. The enclosed README gives commands to regenerate the symbolic traces and replay the Lean proofs.

The literal table has SHA-256 `27613930a4fb7365b761eb23624efa32f1990da0c2d7763e68ad48e0082cb7b7`.
