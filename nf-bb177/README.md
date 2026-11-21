# A 177-state binary Turing machine for pure NF

R. Gutin and E. Glazer

On a blank, two-way infinite binary tape, this machine halts if and only if Quine’s New Foundations proves a contradiction. Start in `k:74`. The table has 177 working states and one separate halt state.

[Transition table](NF_177.tm) · [Verification archive](NF_177_Verification.zip) · [SHA-256 checksums](SHA256SUMS)

## The state reduction

The [178-state predecessor](../nf-bb178) decoded two fields per batch of eight axioms. This version decodes one field and supplies the second parameter by counting down its cache. That saves ten register instructions. In the resulting decoder two states can share a single pair of binary transitions, bringing the table down to 177 working states.

## The proof

On blank tape the machine reaches register instruction zero after 74,071 steps, with epoch counter 3 and all eight remaining registers zero. The archive includes the Lean proof of that computation and the universal simulations of all 7,766 signed register-instruction cases. A separate byte-level check compares the transition tables and the complete tape at the point where these proofs meet.

Soundness and completeness use different facts. Every formula the machine can use has a derivation in the parent calculus for pure NF. Conversely, every axiom needed for a refutation in the reduced calculus can be retrieved by a fixed sequence of commands. A six-command prefix ensures that, for every such proof, the scanner eventually reads the right command boundaries, even if an earlier batch stopped early. Lean also checks that derivability of the numerical goal 3 in that calculus is equivalent to derivability of falsity in pure NF.

The archive gives the written argument connecting the literal register code to those mathematical results. The individual Lean theorems and the remaining written steps are identified in its README and proof notes. The result concerns ordinary blank-tape halting.

Extract the archive and run `python3 check.py` for the quick check. The README inside the archive describes how to rebuild the proof certificates.
