# Guide to the submitted set-theory proofs

`nf-interp.zip` contains the original Lean 4.35.0 development, eleven written proofs and expositions under `nf-interp/docs/`, two earlier working notes, and the recorded checker results under `nf-interp/check/`. The standalone project contains 63 Lean source files. Filenames in the table are relative to `nf-interp/`. A declaration that one theory *interprets* another gives a translation of the latter theory into the former.

| Theory | Formal definitions and proofs | Selected declarations |
| --- | --- | --- |
| New Foundations (NF) | `NFTheories.lean`, `NFInterpretations.lean`, `NFConsistentViaNFU.lean` | `nf_provable_universeInfinite`, `nf_provable_not_choice`, `nf_provable_not_zorn`, `consistent_nf_of_jensen` |
| FunctionNF (FNF) | `FnTheory.lean`, `NFInterpretsFn.lean`, `FnInterpretsNFU.lean`, `FnNF.lean` | `nfInterpretsFn`, `fnInterpretsNFUI`, `fnInterpretsNF`, `consistent_fn_iff_consistent_nf` |
| CombNF | `CombTheory.lean`, `NFInterpretsComb.lean`, `CombFn.lean`, `CombAll.lean` | `nfInterpretsComb`, `combInterpretsFn`, `fnInterpretsComb`, `consistent_comb_iff_consistent_nf` |
| M | `MacTheories.lean`, `NFInterpretsMac.lean`, `MInterpretsTST.lean`, `TSTJensen.lean`, `MacNFU.lean` | `interpretsM`, `mInterpretsTSTI`, `TST.exists_nfui_model`, `exists_nfui_model_of_m`, `consistent_m_iff_consistent_nf` |
| M+H (written `𝗠𝗛` in Lean) | `MHTheory.lean`, `NFInterpretsMH.lean`, `MHInterpretsMAC.lean`, `MacChoiceAll.lean` | `Axiom.collapse`, `nfInterpretsMH`, `mhInterpretsMAC`, `consistent_mh` |
| MAC | `MacTheories.lean`, `MHInterpretsMAC.lean`, `MacChoiceAll.lean` | `nfInterpretsMAC`, `nfuInterpretsMAC`, `consistent_mac_of_consistent_mh`, `consistent_mac` |
| NFU + Infinity | `NFTheories.lean`, `NFUJensenModel.lean`, `NFUConsistent.lean`, `NFUJensen.lean` | `Jensen.consistent_nfuInfinity`, `nfuInterpretsNF`, `nfInterpretsNFU`, `nfuMutualNF`, `consistent_nfuInfinity_iff_consistent_nf` |

The M in these proofs is Mathias’s Mac Lane set theory with transitive containment and bounded separation. MAC adds Choice. The proof from M to NFU + Infinity interprets simple type theory with Infinity in M, then constructs an NFU + Infinity model from each model of that type theory. For M+H, the formal axiom gives each set a single transitive bound for the collapses of all well-founded relations on it. The archive leaves open within its formalization the equivalence of this formulation with Mathias’s cardinal-bound statement of H.

The original `docs/README.md` indexes all the informal proofs and identifies the two historical plans. Its self-contained NFU + Infinity interpretation is `nfu_inf_interprets_nf_selfcontained_2026-11-16.md`. The corresponding guides for the function and combinator theories are `function_nf_2026-11-17.md` and `comb_nf_2026-11-18.md`. For the Mac Lane theories, read `nf_interprets_mac_2026-11-17.md`, `m_tsti_nfui_2026-11-17.md`, and `mac_choice_2026-11-18.md`.

SHA-256 of the submitted `nf-interp.zip` is `0d840316c347b659bcd20008450387e0f5d0191ff0ebd5bb700a6f04f2363a90`.
