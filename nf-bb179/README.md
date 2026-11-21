# A 179-state binary Turing machine for pure NF

The machine starts in `k:74` on an all-zero, two-way infinite tape. It halts if and only if pure Quine New Foundations proves falsum. It has 179 working states and a separate halt state. All 179 are reachable in the transition graph. Exactly one of its 358 transitions enters halt.

[Transition table](NF179.tm) · [Verification archive](NF179_verification.zip) · [Audit](Audit179.log) · [SHA-256 checksums](SHA256SUMS)

## What saved a state

Two decoder states in the predecessor were always entered just after a right move. One incoming transition wrote 0 and the other wrote 1. The shared code reads that bit one cell to the left when it needs to distinguish the two continuations. Two old states disappear and one new state is added. The arithmetic proof-search program stays byte-for-byte identical to the published 180-state program.

## Why it has the same halting criterion

Lean checked the blank run through tick 230,892. At that point the entire tape encodes source instruction zero, epoch counter five and eight zero registers. The head is at −10, the gap is 97, and there are 78 spare cells. This is the same register checkpoint used in the predecessor proof. The independent Lean reference kernel accepted all 7,792 signed physical instruction branches, including the terminal cases. Their induction rules cover arbitrary register lengths. The unchanged source therefore transfers both directions of the published pure-NF halting criterion.

An independent simulator also checked 142,544 full successor tapes and 16 halting fixtures across 94,093,082 binary steps. The PA-format executable checker accepted all 7,792 witness integers. The separate end-to-end PA independence proof for this exact table is being rebuilt.

## Replay

Extract the verification archive and run `python3 verify.py --examples`. With Lean 4.35.0 and `leanchecker-paranoid` on PATH, run `python3 verify.py --kernel --jobs 2` to regenerate all signed proofs. The archive also includes the blank-startup Lean sources and a replay of the state-sharing search.

**Literal table SHA-256** `36c19b11e2b4c854ae41919cfd7cfc5be5a20f3846453da2e9099798e5edfee3`

[Published 180-state predecessor](https://github.com/wlad-svennik/notes/tree/87440d0dc4a281caa4a32dd4165838ae9a35a0b0/nf-bb180)
