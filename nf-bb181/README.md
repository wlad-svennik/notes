# A 181-state binary Turing machine for pure NF

The machine in `NF181.tm` starts in `k:64` on an all-zero, two-way infinite tape. It halts exactly when pure Quine NF proves a contradiction. It has 181 graph-reachable working states and 362 transitions. The halting state is separate. Its SHA-256 is `82285467b36c5024038aeac32abd911d9db251143f98452b29cbbb2d2617e67c`.

[Literal transition table](NF181.tm) · [Complete verification archive](NF181_verification.zip) · [Lean theorem checks](lean-receipts.json) · [SHA-256 checksums](SHA256SUMS)

## Where the state went

Two transitions of the 182-state table change. Together they remove every reachable incoming edge to `d:51`.

| State and symbol | Original action | New action |
|---|---|---|
| `d:50` on 0 | `0 R d:51` | `0 R d:7` |
| `d:7` on 1 | `1 R d:8` | `1 R d:52` |

The register program still has 2,971 instructions. Only instruction 4 changes. During a refill it increments register 7 in place of register 8. The following reader transfers the saved candidate number to register 8, giving each fresh candidate a command with outer tag zero. Commands within its continuation keep their original encoding.

If NF proves a contradiction, the proof compiler supplies a finite command word that detects it from any incoming proof-search state. Encode that word with a trailing numeral to obtain a number E. A refill value of pair(0, E + 1) supplies the forced first command with parameter zero and leaves the continuation E + 1. The next command reader decrements that continuation and reads E. For example, pair(0, 3) = 9 leaves continuation 3, so the reader resumes at code 2. If this first command leaves the machine running, the continuation runs the detecting word. Increasing the trailing numeral makes such a refill available beyond any starting counter. For the converse, each command preserves the invariant that the saved proof data are derivable in the eight-row calculus. A detection therefore witnesses a derivation of the distinguished contradiction.

## Checks on the literal machine

- Starting from a blank tape, the literal first reaches the signed PC38 configuration after 16,439 transitions. It reaches the proof-search entry at PC40 after 17,319. After 80 register instructions it reaches PC111 at physical step 51,111. The head is at −1, the header is at +50, and the tape contains 32 unused unary blocks. The register vector in numerical order is (−1, 0, 0, 2, 0, 0, 0, 1, 0). The signed initial register is part of the proved startup encoding.
- The raw transition certificate covers all 7,794 enabled combinations of instruction, register encoding and decrement outcome. Each live case checks the entire successor frame with arbitrary register magnitudes and padding parameters. The zero branch of PC2954 reaches the unique halting transition, `k:302` reading 1.
- An independent replay checked 142,608 concrete cases across varied register values and padding widths. In 142,592 cases it compared the complete successor tape. In the other 16 cases it checked the halt transition. Together these cases cover 95,344,106 literal transitions.
- The PA development uses an independently arithmetized tape checker, the exact signed startup and the modified enumerator. The source binding checker decodes every register instruction and compares it with the Lean literal.

## Reproduction

Extract `NF181_verification.zip` and run the quick checks from the extracted directory with Python 3.10 or later.

```sh
python3 verify.py
```

To repeat all 142,608 concrete tape checks, run `python3 physical/replay_examples.py` with a C++17 compiler installed.

To regenerate and check the raw transition proof terms, use Lean 4.35.0's reference checker.

```sh
python3 verify.py --kernel /path/to/leanchecker-paranoid -j 2
```

The verification archive includes the 182-state PA development and its pinned Lake manifest. Its baseline archive is byte-identical to the one in Git commit `135905bd1f09d36311f489f193c86d8ee0c1fe1e`. [Published 182-state baseline](https://github.com/wlad-svennik/notes/blob/135905bd1f09d36311f489f193c86d8ee0c1fe1e/nf-bb182/NF182_PA_verification.zip)

To rebuild the end-to-end 181-state Lean theorems, install the pinned Lean toolchain through elan and run the following command with Lake available.

```sh
python3 verify.py --pa -j 2
```

The PA build directory is created inside the unpacked checkpoint. Its first build obtains the pinned dependencies and their caches. The checkpoint's manifest covers the proof source, table, register program, certificates and receipts.

## Mathematical endpoints

| Theorem | Statement |
|---|---|
| `NFMachine181.halts_iff_nf_refutation` | The literal machine halts from blank tape exactly when pure NF proves falsum. |
| `NF181PA.halting_equivalence` | First-order PA proves the biconditional between the literal 181- and 182-state blank-tape halting sentences. |
| `NF181PA.internal_consistency` | First-order PA proves that nonhalting of the 181-state machine implies the standard consistency statement for PA. |
| `NF181PA.pa_independence` | Assuming NF is consistent, PA decides neither sign of this halting sentence and proves no individual numerical upper bound on the 181-state runtime Busy Beaver value. |

The transfer proof works in an arbitrary model of PA. A halting time, a coded computation and a proof-search counter can each be nonstandard in that model. The proof relates both literal machines to the same arithmetical proof predicate at those model-internal times. First-order completeness then gives the PA proof of their halting equivalence.
