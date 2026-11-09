# New Foundations and the runtime Busy Beaver function at 210 states

**Research source snapshot — 5 November 2026.** An external Lean 4 proof development for a 210-working-state, 2-symbol Turing machine related to the consistency of Quine's New Foundations (NF).

## Mathematical statements

The frozen machine is intended to halt exactly when the specified syntactic first-order NF theory has a contradiction proof. The recorded Lean development states:

1. **Value unprovability (conditional on consistency):** If NF is consistent, NF proves no statement `BB(210) ≤ k` for a particular natural number `k`, and hence no exact numeral equation `BB(210) = k`.
2. **Two-sided independence (stronger assumption):** If NF is arithmetically Σ₁-sound, then the *true* exact-value equation for `BB(210)` is neither provable nor refutable in NF.

Here `BB` is the **maximum runtime** (number of steps before halting), not the maximum printed-ones function. Machines are binary, with a two-way blank tape, L/R moves, and the transition into halt counted; the 210 states exclude the halt marker. The true numerical value is **not** computed. No NF–Mac Lane set theory equiconsistency assumption is used.

## Verification status

The source snapshot contains 764 local Lean modules and receipts reporting compilation of the final theorems with only `propext`, `Classical.choice`, and `Quot.sound` in the transitive axiom report. It contains no `sorry` or `admit` tokens. These are **recorded checks from 5 November 2026**, not an independent clean rebuild performed for this GitHub publication. The metatheorem is formalized **externally in Lean**, not as a completed PA-internal formalization; the separate unfinished PA follow-up is intentionally excluded.

The [final theorem declarations](NF210/ProofBB210ExactFinal.lean), [consolidated audit module](NF210/ProofBB210Audit.lean), [machine table](data/selected210.tm), [certificate provenance](CERTIFICATE_PROVENANCE.md), and [final audit log](verification/final_exact_audit.log) are directly browsable here. The complete dependency-closed Lean source snapshot is recoverable as described below.

## Complete source archive

The source ZIP is stored as 17 **binary pieces** in [`archive/`](archive/) solely to accommodate the available authenticated upload interface. They represent one unmodified 5,125,753-byte ZIP, not 17 independent proofs.

From this directory after cloning:

```sh
sh restore-archive.sh
cd nf210_formal
python3 tools/build_project_module.py --plan NF210.ProofBB210Audit
python3 tools/build_project_module.py --force NF210.ProofBB210Audit --receipt verification/clean_final_rebuild.json
```

The script joins the pieces in their numbered order and verifies SHA-256 before accepting the ZIP. It then extracts `nf210_formal/` without overwriting existing files. The full build requires **Lean 4.35.0**, Foundation commit `63bfd1b2e821dc2367b08f68d379303d08631f83`, and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, together with the supplied dependency patches and build instructions. A clean rebuild can require considerable memory and time.

**Source ZIP SHA-256:** `502afdde1bdaac727531d5f22fa8f24828b37a09c2df9a66b657bb3c8f0faec8`  
**210-state machine SHA-256:** `129fc1fe44f609c18c2dfbc6df367835bbee7d6a02bbda3480b93d3c2c52646a`  
**Machine:** [`data/selected210.tm`](data/selected210.tm); 210 working states, 420 transition rows.

## Review and attribution

This is a public, inspectable research artifact; independent rebuilds and mathematical criticism are welcome. The development was prepared with AI assistance. A public wiki entry should distinguish the consistency-based result from the stronger soundness-based two-sided statement, and should not treat the result as externally reproduced until a fresh independent check is reported.
