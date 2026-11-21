# A 198-state binary Turing machine for NF + CS

R. Gutin and E. Glazer

On a blank two-way infinite binary tape, this machine searches for a contradiction in Quine’s pure NF with full CS. The register program enumerates proofs in a nine-schema numerical calculus and halts when it observes formula 3. The identification with pure NF + CS uses the written theory comparison described below.

[Transition table](NF_CS_198.tm) · [Verification archive](NF_CS_198_Verification.zip) · [Checksums](SHA256SUMS)

The table starts in `k:64`. It has 198 graph-reachable working states, 396 transitions and one halt arm. The blank-tape startup reaches the scanner at step 75,040. Lean checked all 11,442 signed instruction cases, and a separate checker matched every warm case to the literal source. The scanner uses a countdown and leaves the first coordinate unchanged after emitting the CS row. The latter change lets it enumerate the required extensionality instances.

The calibration proves in Lean that consistency of pure NF + CS gives a model of all the emitted rows with goal 3 false. It also proves that underivability of goal 3 gives a model of NFU with Dedekind Infinity and full CS. The remaining implication uses Proposition 17.37 and Theorem 21.1 of *Choice and Consistency Strength in NF and NFU*, v15, by R. Gutin and E. Glazer, as in the [199-state release](../nf-cs-bb199). The manuscript describes its results as self-audited and awaiting independent verification.

For a quick replay, extract the archive and run `python3 check.py`. The archive contains the source, the physical and logical proof files, and instructions for the full replay.
