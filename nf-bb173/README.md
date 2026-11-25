# Pure NF: a 173-state binary machine

**R. Gutin and E. Glazer — 25 November 2026**

[NF_173.tm](NF_173.tm) is the 173-state implementation of the pure-NF
proof-search source. It has **173 working states and 346 binary transition
arms**, with a separate halting state. The start state is `k:74`, the blank
symbol is `0`, and the tape is two-way infinite.

This is a one-state reduction from the 174-state predecessor included in the
verification archive. The literal proof-search source is unchanged. The
reduction introduces no Axiom of Counting.

## Result and proof scope

The implementation reduction preserves blank-tape halting of the unchanged
pure-NF source and its 174-state predecessor. It inherits the predecessor's
calibration to the existence of a finite first-order NF contradiction.

The portable package checks the literal table, all natural-input physical
phase domains, the complete blank startup, source guards and interfaces, and
generic transfer-loop arithmetic. The whole-program composition is given
in [Composition_Proof.txt](Composition_Proof.txt). The inherited numerical
enumeration and NF calibration include written proofs; this package does
not claim a new single end-to-end Lean theorem connecting the entire literal
machine to Quine's NF. See [Verification_Scope.txt](Verification_Scope.txt)
for the precise boundary.

## Exact reduction

Only two successor targets change relative to the supplied 174-state table:

| State and read symbol | Previous target | New target |
| --- | --- | --- |
| `d:163`, reading `1` | `d:39` | `d:17` |
| `d:79`, reading `1` | `d:39` | `d:160` |

The writes and head moves stay the same. The unused `d:39` state is removed.
The comparison is proved at complete source operations using the source
invariant; it is not an assertion that the redirected states are equivalent
on arbitrary tapes.

## Verification contents

| Check | Coverage |
| --- | --- |
| Literal machine | 173 graph-reachable working states; all 346 binary arms |
| Source | 2,976 primitive leaves, unchanged byte for byte |
| Physical proof domains | 3,932 exact unbounded natural-input domains |
| Pump laws | 20 one-unit laws with natural-number iteration |
| Source invariant | 694 closed arithmetic loops; 1,603 checked successor images |
| Rotated loops | 28 loops, plus one borrowed-increment loop |
| Generic arithmetic | 16 kernel-checked natural-induction theorems |
| Blank startup | 67,998 transitions to the full canonical source-PC0 frame |
| Stored complete kernel replay | 3,932 physical theorems and 34 startup segments |

The blank endpoint has head position `-4`, gap `55`, 30 spare zero fields,
`R1 = 1`, and all other registers zero. The independent publication check
compares the complete marked-cell set, not just a local tape window.

## Reproduction

Download [NF173_Portable_Verification.zip](NF173_Portable_Verification.zip),
then run on Linux x86-64 with Python 3.10 or newer:

```sh
unzip NF173_Portable_Verification.zip
cd NF173_Portable_Verification
chmod +x kernel/bin/leanchecker-paranoid
python3 verify.py
```

The default check independently replays physical and source obligations,
regenerates the physical certificate byte for byte, and freshly checks the
16 arithmetic theorems in the bundled, hash-pinned standalone Lean kernel.
It needs no third-party Python packages, Lean frontend, or network access.

For a fresh complete physical and startup kernel replay, use:

```sh
python3 verify.py --kernel
```

The archived acceptance record is [Original_ADMISSION.json](Original_ADMISSION.json).
[table-and-startup-check.json](table-and-startup-check.json) records the
separate structural count and literal startup simulation performed for
publication. The original ZIP is supplied unchanged.

The fresh publication run of `python3 verify.py` passed on 25 November 2026;
its [receipt](publication-verification.json) and
[output](publication-verification.log) are included. This run freshly checked
all default obligations, including the 16 arithmetic kernel theorems.
The complete physical/startup kernel receipts remain those in the original
same-day archive; no second completed `--kernel` replay is claimed here.

## Identities

Machine table SHA-256:

```text
ca0c0924b4f4008b19fd2b63f5c07b244c4573ad338dcd5b8267cf2e7a02990a
```

Portable archive SHA-256:

```text
7395a3beec371b0970c872ec224c70422183d4c3351eb8c60e4cd66c3fdc8200
```

Unchanged source SHA-256:

```text
ce0fb9873e0546d3c691c50ed7f1ec1f04729e5fc961bc6e24f825a35e1cb702
```

The complete per-file checksums for this publication directory are in
[SHA256SUMS](SHA256SUMS). Existing upstream notices in the archive continue
to apply.
