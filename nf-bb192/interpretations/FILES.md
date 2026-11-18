# Files in this directory

The 64 Lean files and 11 Markdown proofs here preserve the bytes of the submitted `nf-interp.zip`. They are gathered in one directory for reading on GitHub. The ZIP preserves the original project layout, Lake build files, checker outputs, and working notes.

| Files | Original location inside `nf-interp.zip` |
| --- | --- |
| The 54 main Lean modules, including `NFConsistentViaConNF.lean` | `nf-interp/` |
| The ten additional Lean modules listed below | `nf-interp/standalone/ConNF/NF/` |
| The eleven dated Markdown proofs | `nf-interp/docs/` |

The ten additional modules are `Generic.lean`, `Hailperin.lean`, `NFModel.lean`, `NFUArith.lean`, `NFUConstr.lean`, `NFUCut.lean`, `NFUHartogs.lean`, `NFULadder.lean`, `NFUSat.lean`, and `NFUSound.lean`. They contain the underlying NF and NFU constructions used by the standalone proof. The other 53 standalone Lean files are byte-identical to their counterparts in the project root. The remaining top-level file, `NFConsistentViaConNF.lean`, gives the earlier proof using the external con-nf model.
