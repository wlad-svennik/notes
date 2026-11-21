# A 178-state binary Turing machine for pure NF

Starting on an all-zero, two-way infinite tape, this machine halts exactly when pure Quine New Foundations proves falsum. Its table has 178 working states, two symbols, and a separate halt state. All 178 states are reachable in the transition graph. Only the transition from `k:302` reading one enters halt.

[Transition table](NF178.tm) · [Verification archive](NF178_verification.zip) · [Audit](Audit178.log) · [Checksums](SHA256SUMS)

## What saved the second state

The search started from a 179-state decoder and allowed different instruction paths to share a physical state even when they returned to the same configuration after different numbers of steps. An initial 178-state table passed 7,790 of the 7,792 symbolic branches. At source instruction 2905 it jumped forward to 2910, while the program required a jump back to 2903 to continue subtracting. For example, on a warm frame with registers [5,0,0,0,0,1,1,0,0], the first table reached instruction 2910 in 256 steps. A search over pairs of transitions found a repair that reaches the correct instruction 2903 in 54 steps. Changing the transition from `aux:new:1` on one corrected the jump. Changing the transition from `d:165` on zero preserved the forward jump required at instruction 2911. The final table executes the same 2,970-instruction register source as the published 180-state machine.

## Halting criterion

At tick 240,354 the complete blank-tape configuration encodes register instruction zero, epoch counter five and the eight remaining registers all zero. Its head is at −10, its address gap is 97, and it has 78 spare cells. This is the same source checkpoint as for the 179- and 180-state machines. Lean checks the blank computation. The independent Lean reference kernel checks the 7,792 signed instruction simulations, including every terminal branch. Twenty induction rules cover arbitrary tape repetitions. Each live instruction reaches the prescribed successor frame. Together with the published pure NF proof search, these facts establish the standard halting criterion in both directions.

The independent concrete replay compared 142,544 full successor tapes and 16 halting fixtures over 100,654,682 binary transitions. The scope of this release is the ordinary blank-tape halting criterion. The archive includes both predecessor proof packages under `upstream/`.

Every pair of working states can also be distinguished by a finite binary tape in at most eight steps. The replay in `discovery/confirm_pairs.py` checks all 15,753 pairs for a difference in a write, move or halt. A further state saving will therefore need to exploit the tapes on which a state is actually entered, allow different-length paths, or change the program.

## Replay

Extract the verification archive and run `python3 verify.py --examples` with Python 3 and a C++17 compiler. With Lean 4.35.0 and `leanchecker-paranoid` on PATH, run `python3 verify.py --kernel --jobs 2` to regenerate and kernel-check the physical branch proofs. The archive also carries a self-contained blank-startup proof and the search and repair evidence.

**Literal table SHA-256** `46cde5a5de2b1ef86094baa9940cd61153c0c1cb45cdc9339fa642b3c7625efc`

[Verified 179-state predecessor](https://github.com/wlad-svennik/notes/tree/050296ab1fb91cfe3b46b167a545892d72a15b3e/nf-bb179)
