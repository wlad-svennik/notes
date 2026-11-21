# A 186-state binary Turing machine for NF + AxCount

R. Gutin and E. Glazer

On a blank, two-way infinite binary tape, the machine halts exactly when the nine-schema guarded counting calculus derives formula 3. Under the same mathematical comparison as the [187-state predecessor](../nf-axcount-bb187), this is equivalent to inconsistency of Quine’s pure NF with Rosser’s full Axiom of Counting.

[Transition table](NF_AxCount_186.tm) · [Verification archive](NF_AxCount_186_Verification.zip) · [Checksums](SHA256SUMS)

The countdown saves ten register instructions and one working state. Start in `k:74`. The table has 372 transitions and a single halt arm. On blank tape it reaches the register scanner after 75,311 steps. All 9,526 signed instruction proofs were regenerated and kernel-checked. A separate verifier compared the 4,764 warm instruction cases with the literal source.

A batch can finish before the remaining counter reaches zero. The verification includes the six-command resynchronization proof for actual Cantor-coded cursors, the nine-row proof-word construction and a comparison with the published 187-state emitter. The external pure-theory comparison uses the full-chart construction and Proposition 17.13 and Theorem 21.1 of *Choice and Consistency Strength in NF and NFU*, v15, by R. Gutin and E. Glazer. The manuscript describes its results as self-audited and awaiting independent verification. The archive identifies the kernel-checked and written steps.

Extract the archive and run `python3 check.py` for the quick check. The README and `audit/Audit.md` give instructions for the mathematical and physical replays.
