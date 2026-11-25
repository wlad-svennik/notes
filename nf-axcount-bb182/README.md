# NF + full AxCount: 182-state binary machine

**R. Gutin and E. Glazer — 25 November 2026**

This release reduces the NF + full Axiom of Counting implementation from
183 to **182 working states**, with a separate halt state. The literal table
has 364 binary transition rows and starts on an all-zero, two-way infinite
tape in state `k:74`. The 3,397-instruction proof-enumeration source is
unchanged.

The target theory is NF with full Rosser Counting: `T(n) = n` for every
internal Frege natural number. The inherited calibration and its precise
formalization boundary are described below.

## Files

- [Literal transition table](machine.tm).
- [Unchanged register-machine source](source.sites.json).
- [Complete portable verification package](NF_AxCount_182_verified.zip).
- [Reduction proof](Reduction_proof.txt).
- [Inherited theory-calibration audit](Calibration_Audit.txt).
- [Fresh publication verification receipt](verification.json) and
  [replay log](verification.log).
- [Independent table and startup audit](independent-table-audit.json).
- [SHA-256 checksums](SHA256SUMS).

The ZIP is the original release, preserved byte for byte. The other source
and proof files are extracted copies; the publication receipts record the
fresh checks performed for this repository update.

## What changed

Two transitions of the authenticated 183-state baseline are redirected:

| State and read symbol | Write and move | Old target | New target |
| --- | --- | --- | --- |
| `d:163`, `1` | `1`, right | `d:39` | `d:17` |
| `d:79`, `1` | `1`, right | `d:39` | `d:160` |

State `d:39` then has no outside predecessor and its two rows are removed.
The proof treats 30 complete register-transfer loops and one borrowed
increment. It supplies inductive entry guards; it does not assume the
merged physical states behave identically on arbitrary tapes.

## Verification

For this publication, `python3 verify.py --kernel --jobs 2` completed
successfully on 25 November 2026. The fresh receipt matches the archived
full verification result.

The portable verifier checks the exact rebuild and unchanged source, all
4,485 unbounded physical phase domains, all 364 transition rows, deterministic
trace regeneration, source control flow and loop-entry guards. It also
regenerates and checks 16 arithmetic induction theorems with the included
standalone Lean kernel.

The `--kernel` replay additionally regenerates and kernel-checks the
physical phase proofs in 71 batches and all 67,998 blank-start transitions
in 34 contiguous segments. Startup reaches source PC 0 with `R1 = 1`, the
other eight registers zero, frame head `-4`, gap 55 and 30 spare fields.

An independent publication audit also parses the literal table, checks
totality and target closure, counts all 182 syntactically reachable states,
and simulates the complete startup to compare every marked tape cell with
the recorded frame.

## Reproduce

On Linux, with Python 3 and the standard library:

```sh
unzip NF_AxCount_182_verified.zip
cd NF_AxCount_182
chmod +x kernel/bin/leanchecker-paranoid
python3 verify.py
python3 verify.py --kernel --jobs 2
```

No Lean frontend, Mathlib installation or network access is required by
these replay commands. The verifier authenticates the included checker
and release files by SHA-256. `--output PATH` writes a verification receipt.

## Theory and proof scope

The implementation reduction preserves the earlier source and its full
internal counting law. The written composition of startup, ordinary phases,
guarded loop inductions and the borrowed increment establishes the same
blank-tape halting behavior as the 183-state baseline.

The intended calibration identifies this halting behavior with
inconsistency of NF + full AxCount. The inherited special full-chart
construction and the complete numerical proof-enumeration/model comparison
remain written components of that argument. The uploaded counting
interpretations and their historical check reports are retained in the
archive; their complete frontend/dependency build is not a fresh result of
this release, and the new interpretation adapter sources were not freshly
built. See [Calibration_Audit.txt](Calibration_Audit.txt).

Accordingly, this package does **not** claim a single end-to-end Lean theorem
from the usual NF + AxCount axioms to this literal table's halting behavior.
It does not establish a lower bound ruling out a smaller implementation.

## Identity

```text
table  d99fe0163acc608b1bed679e9c72a941bd05d37c285e6db0a12cb111eca25e7b
source 222bb33545c28307c2a358760ed9857f6897d43ef1bae010919a0abca7e2b8f4
ZIP    4e2ab88ed5027ff4bcef425b11a0f41db778c1914930c7a4e578c56f5262f452
```
