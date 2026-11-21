# A 199-state Turing machine for NF + CS

This binary, single-tape Turing machine starts on a blank tape and searches for a contradiction in a calculus equiconsistent with pure New Foundations plus the Axiom of Cantorian Sets (NF + CS). Here CS says that whenever a set is equinumerous with its singleton image, the function sending each of its elements to its singleton has a set graph. This includes sets for which no well-ordering is given.

[Transition table](NF_CS_199.tm) · [Verification package](NF_CS_199_Verification.zip) · [SHA-256 checksums](SHA256SUMS)

## The machine

Start in `k:64` on an all-zero, two-way infinite tape. Each of the 398 rows gives the current state, read bit, write bit, move direction and next state. There are 199 working states and a separate halt state. The only halting transition reads 1 in `k:302`.

The construction saves six states over the original 205-state Cantorian machine. It shortens the proof enumerator and reuses parts of the 178-state pure-NF decoder. The last state disappears because two decoder paths always rejoin with the same head position and tape after two or three transitions. The archive contains a Lean proof of this local equivalence.

## What is verified

The startup proof reaches the designated proof scanner after 75,040 transitions. All 4,377 register instructions are bound to the literal program. The kernel accepted all 11,470 symbolic instruction cases. An additional concrete replay checked 210,080 complete successor tapes and 16 halts.

The register program halts exactly when the original Cantorian calculus derives its refutation. Lean also proves that ordinary syntactic consistency of pure NF + CS implies nonhalting of this register program, and that nonhalting gives a model of NFU with Dedekind Infinity and full CS. For the reverse implication to consistency of pure NF + CS, the construction uses the written equiconsistency comparison in R. Gutin and E. Glazer, *Choice and Consistency Strength in NF and NFU*, v15, Proposition 17.37 and Theorem 21.1. Together these results give the blank-tape halting criterion.

## Replay

Unzip the verification package and run the following command from the extracted directory with Python 3.10 or later and a C++17 compiler.

```sh
python3 verify.py --examples
```

The package README gives commands for rebuilding the Lean proofs. Its calibration archive contains the first-order CS sentence, the two model constructions, their proof sources and the dependency versions used for replay.
