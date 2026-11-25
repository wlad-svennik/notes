# NF + CS: a 197-state binary Turing machine

**R. Gutin and E. Glazer**  
Machine certificate: 24 November 2026. Publication replay: 25 November 2026.

This release reduces the [198-state implementation](../nf-cs-bb198/) by one
working state. The table has **197 working states**, **394 binary transition
rows**, and a separate halting target. It starts on an all-zero tape in
state `k:64`.

The complete physical certificate verifies that the table implements the
same numerical refutation search as the earlier NF + CS machine. Its
calibration to NF + CS uses the inherited checked endpoints and written
theory comparison described below. This release does not claim a new
end-to-end Lean theorem or a proof that 197 is minimal.

## Files

| File | Contents |
| --- | --- |
| [NF_CS_197.tm](NF_CS_197.tm) | Complete binary transition table; initial state is recorded in its first line. |
| [NFCS_197_Certificate_2026-11-24.zip](NFCS_197_Certificate_2026-11-24.zip) | Original portable certificate archive, unchanged; Python 3 standard library only. |
| [Rotated197.md](Rotated197.md) | Universal phase contracts, loop induction and whole-program composition. Its relative paths refer to the extracted certificate archive. |
| [calibration/Ground-calibration.md](calibration/Ground-calibration.md) | Ground-calculus calibration inherited from the 198-state machine. |
| [calibration/Parent-calibration.md](calibration/Parent-calibration.md) | Definition of full CS, checked model endpoints and written consistency comparison. |
| [verification/](verification/) | Fresh publication replay receipts and an independent structural table check. |
| [SHA256SUMS](SHA256SUMS) | SHA-256 checksums for the files in this release. |

Each noncomment table row is `state read write direction next-state`.
Symbols are `0` and `1`; directions are `L` and `R`. `halt` is the only
target without outgoing rows and is not counted among the 197 working
states. Every working state has exactly one transition for each read
symbol. The initial head position is an arbitrary origin on the blank
two-way tape.

## Verification

The original archive's 26 manifest entries passed their byte-size and
SHA-256 checks before replay. The following checks were rerun successfully
on 25 November 2026:

- Independent reconstruction of all 29 source-loop replacements, all
  5,634 source control edges, and the 5,621 nonhalting edges of the source
  invariant.
- Literal blank-tape startup: exactly **72,014 transitions**, reaching
  source PC 0 in state `d:0`, head position -6, registers
  `[3,0,0,0,0,0,0,0,0]`, gap 49 and 31 zero spare fields.
- **5,605 ordinary natural-input domains** and **145 guarded phase
  domains**, using **20 checked pumping lemmas**, 2,749,573 literal
  transitions and 139,136 pumping applications.
- Coverage of all **197 states** and **394 transition arms**, including
  startup and pumping interiors. The unique source-halting branch is
  included.
- A separate table parser confirmed the state count, complete binary
  transition domain, unique halting target and graph reachability of every
  working state. A separate literal simulator reproduced the startup
  control state and head position.

The symbolic domains quantify over arbitrary natural register values and
unbounded gap/spare extensions. Their phase contracts compose with the
written induction on the donor register in [Rotated197.md](Rotated197.md).
They are not merely bounded execution samples.

## What changed

The original `CD6; CI5; CC2` transfer loops are interpreted as complete
operations. A deferred increment and a repeated tail phase preserve
`R5 := R5 + R6; R6 := 0`. This lets decoder state `d:160` share `d:39`.
The source invariant supplies the guards needed at all 29 loop locations.
The result has 4,307 macro-source sites corresponding to 4,365 primitive
sites. All initialization, decoding, arithmetic and return control are
included in the 197-state count.

## Theory and calibration scope

Here **CS is the unrestricted assertion that every Cantorian set is
strongly Cantorian**. No well-orderability restriction is substituted.

The inherited ground-calculus certificate has checked endpoints from
syntactic consistency of pure NF + CS to numerical nonderivability, and
from numerical nonderivability to a model of A0, where A0 is bare NFU with
Dedekind Infinity and full CS. The return consistency comparison from A0
to pure NF + CS uses the written results in **R. Gutin and E. Glazer,
*Choice and Consistency Strength in NF and NFU*, v15, Proposition 17.37
and Theorem 21.1**. Together with the physical simulation, that calibration
gives the claimed equivalence between blank-tape halting and inconsistency
of NF + CS.

This 197-state reduction preserves that calibration. The compact archive
contains its scope notes, but does not contain or rerun the complete Lean
calibration development; see the [198-state release](../nf-cs-bb198/) for
that material. No new PA-internal or ZFC-internal unprovability proof is
claimed by this state reduction.

## Reproduce

Extract the ZIP and enter `NFCS_197_Certificate_2026-11-24/`. Then run:

```sh
python3 deliverables/verify_bundle.py ../NFCS_197_Certificate_2026-11-24.zip
python3 sprint_20261124_1155/root_audit197/check_source_startup.py
python3 sprint_20261124_1155/audit/check_rotated197.py
```

Adjust the archive path in the first command if it is stored elsewhere.
Run the manifest check first: the next two commands regenerate receipts,
including elapsed-time fields. They require Python 3 and its standard
library, with no network, Lean installation or external package.

The table SHA-256 is:

```text
948492f1d299acb09b0d3464c5de7ef6e5d510bc09398324a9610c65f52cbbf3
```

The unchanged original archive SHA-256 is:

```text
aba1d0d0fd80502e3bb353ecd8c122c827c35d90b8d3b6276f294914ea415459
```
