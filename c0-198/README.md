# C₀: two 198-state Turing machines

Research checkpoint from 11 November 2026.

The supplied mathematical report and replayable certificates establish, for each of the two supplied binary machines:

- the machine halts on the blank tape if and only if the exact theory C₀ is inconsistent;
- Con(NF) implies nonhalting, and nonhalting implies Con(NFU + Infinity).

Both tables have 198 nonhalting working states and 396 transition rows. They use symbols 0 and 1, an all-zero tape unbounded in both directions, only left/right moves, initial state `k:64`, and a separate uncounted `halt` outcome.

## Files

The PDF reports and ZIP archives are downloads from the [C₀ research release](https://github.com/wlad-svennik/notes/releases/tag/c0-198-2026-11-11). The machine tables and verification receipts are stored in this directory.

| File | Contents |
| --- | --- |
| [Proof report](https://github.com/wlad-svennik/notes/releases/download/c0-198-2026-11-11/C0_198_proofs_2026-11-11.pdf) | Exact axioms, interpretations, Infinity, machine calibration, and both reductions. |
| [Primary machine](C0_198.tm) | First 198-state construction. |
| [Direct machine](C0_198_direct.tm) | Independent reduction of the sealed 199-state table. |
| [Complete verified checkpoint](https://github.com/wlad-svennik/notes/releases/download/c0-198-2026-11-11/C0_198_verified_checkpoint_2026-11-11.zip) | Source, proof text, compilers, tables, certificates, recorded checks, and pinned dependencies. |
| [Reverse-interpretation report](https://github.com/wlad-svennik/notes/releases/download/c0-198-2026-11-11/C0_reverse_interpretation_2026-11-11.pdf) | Further results and obstructions concerning an interpretation in NFU + Infinity. |
| [Reverse-interpretation sources](https://github.com/wlad-svennik/notes/releases/download/c0-198-2026-11-11/C0_reverse_interpretation_2026-11-11.zip) | Report source and independent mathematical audits. |
| [Recorded full replay](verification/portable_replay_receipt.json) | Successful recorded replay of the primary construction. |
| [Recorded direct-reduction replay](verification/portable_direct198_receipt.json) | Successful recorded check of the optional direct reduction. |
| [SHA-256 checksums](SHA256SUMS) | Exact digests of the published files. |

## Scope of the result

These are conventional mathematical arguments in ZF, with explicit unbounded inductions and replayable finite certificates. They do not constitute a new end-to-end Lean or PA formalization of a 198-state machine. Finite runtime tests are supplementary to the uniform arguments. No optimality claim is made.

The calibration concerns the exact unrestricted C₀ theory. It does not identify C₀ with NF. The reverse interpretation of C₀ in NFU + Infinity remains unresolved in the later report. These checkpoints do not establish an NF–Mac Lane equiconsistency theorem; they precede the separate audit of the v15 manuscript.

The earlier [NF BB(210) development](../nf-bb210/README.md) remains available with its own theorem statements and verification scope.

## Reproduction

Extract the complete verified checkpoint ZIP and change into its `C0_198_verified_checkpoint_2026-11-11` directory. With Python 3, run:

```sh
python3 replay.py --output-root /path/to/a/new/replay-output-directory
```

The full source and pinned dependencies are included, so this replay needs no network access. The supplied README explains the complete proof chain and distinguishes the primary construction from the optional direct reduction. The recorded full replay took about 178 seconds in its original environment; runtime elsewhere may differ.

The archive's `MANIFEST.sha256` binds its 4,115 included files. All manifest entries were checked again when preparing this upload. Both literal machine tables were independently counted again as 198 states and 396 rows. The saved replay receipts are published unchanged; a new full replay was not run solely for this upload.

The standalone proof PDF and the copy frozen inside the complete checkpoint are retained as originally saved. Their byte hashes differ; the standalone report is supplied alongside the unchanged archive.
