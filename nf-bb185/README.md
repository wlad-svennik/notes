# A 185-state Turing machine for pure NF

This deterministic two-symbol machine halts on the blank tape **if and only if Quine’s New Foundations proves a contradiction**. It has 185 working states, 370 transitions, a separate halt and start state `k:64`. In the eight-schema calculus it searches for a derivation of `(JJ) = J`, formula code 3. The register program has 2,959 instructions.

| File | Contents |
|---|---|
| [NF185.tm](NF185.tm) | Literal binary transition table |
| [NF185Exact.lean](NF185Exact.lean) | The statement and final proof linking this table to pure NF |
| [NF_Eight_Row_185_Verification.zip](NF_Eight_Row_185_Verification.zip) | All 268 Lean project modules, pinned external dependencies, executable checks and verification receipts |
| [WORK_NOTES.md](WORK_NOTES.md) | What produced 185 states, which 184-state shortcuts failed, and how to resume |
| [NF185_Research_Handoff.zip](NF185_Research_Handoff.zip) | Runnable state-reduction search, tested layouts, counterexamples, alternative programs and research notes |
| [Calculus.wiki](Calculus.wiki) | The eight schemas in their emitted order |
| [source.sites.json](source.sites.json) | Source program with all binary instruction addresses |
| [physical-replay.json](physical-replay.json) and [theorem-axioms.txt](theorem-axioms.txt) | Independent tape replay and Lean axiom audit |

The table’s SHA-256 is `5504746071e10a0555754b55efc2da348ebfb1f8e8ab5bc7af474eaad81f60fe`. Independent simulation exercised 142,032 tape frames and 86,806,365 literal transitions. The unbounded result is the Lean theorem `NFMachine185.halts_iff_nf_refutation`. Its recorded audit includes three standard Lean axioms and eleven finite checks performed by native evaluation.

## Reproduce the result

With Python 3, a C++17 compiler, and the Lean 4.35.0 toolchain in the archive, run

```sh
unzip NF_Eight_Row_185_Verification.zip
cd NF_Eight_Row_185
sha256sum -c SHA256SUMS
python3 verify.py
python3 descent/replay.py
python3 independent/run.py candidate.tm source.sites.json reference/counting196.tm --fixtures 48 --output /tmp/nf185-frames.json
lake exe cache get
lake env python3 replay.py --jobs 3 --build /tmp/nf185-proof
```

To search for 184, extract the research handoff and start with its README. It contains the verified inputs and an independent example of a smaller table that passed physical fixtures and failed at the level of proof commands.
