# A 180-state binary Turing machine for pure NF

The machine starts in state `k:74` on an all-zero, two-way infinite tape. It halts if and only if pure Quine New Foundations proves a contradiction. All 180 working states are reachable in the transition graph. Exactly one of the 360 transitions enters the separate halt state.

[Transition table](NF180.tm) · [Physical verification](NF180_verification.zip) · [PA and Busy Beaver proofs](NF180_PA_verification.zip) · [Lean audit](Audit180.log) · [SHA-256 checksums](SHA256SUMS)

## Reduction from 181 states

Removing one refill instruction leaves the epoch counter one ahead of its previous value. Rotating four decoder transitions lets the machine enter this computation directly from blank tape. After 233,734 transitions, the head and the entire tape encode instruction zero with epoch counter five and the other eight registers zero. From there the computation agrees on halting with the 181-state source starting at epoch four. The physical simulation covers all 2,970 instruction addresses and 7,792 signed branch cases. [181-state predecessor](../nf-bb181)

## What PA proves

Let H be the arithmetic sentence asserting that this literal machine halts on blank tape. PA proves that H is equivalent to the corresponding 181-state sentence. The simulation covers nonstandard clocks and proof codes in arbitrary models of PA. PA also proves that ¬H implies its own standard consistency sentence.

If pure NF is consistent, the machine runs forever, PA decides neither H nor ¬H, and PA proves no numeral upper bound for the runtime Busy Beaver function at 180 states. For the true standard value of BB(180), both its equality to that numeral and the negation of that equality are unprovable in PA. The formal statements and their axiom dependencies are in the [audit](Audit180.log).

## Replay

Use Lean 4.35.0. Extract each archive into its own directory. From the physical verification directory, run the following commands.

```sh
python3 verify.py
python3 verify.py --lean --jobs 2
python3 verify.py --kernel --jobs 2
python3 verify.py --examples
```

From the PA verification directory, run the following commands.

```sh
python3 replay.py --jobs 2 --audit
```

The PA driver checks the literal table and its start state, obtains the pinned 181-state baseline, and checks both the direct proof and the transfer from the predecessor. The baseline can also be supplied with `--baseline /path/to/NF181_verification.zip`.
