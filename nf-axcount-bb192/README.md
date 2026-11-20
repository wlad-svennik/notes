# The 192-state J-point machine for Rosser Counting

This two-symbol Turing machine halts on the blank tape **if and only if the ten-schema J-point calculus derives the equation `Q = J`**, where `Q = JJ` and application associates to the left. Lean checks this equivalence for the literal transition table. A second Lean theorem shows that **if the machine runs forever, there is a model of NFU with Dedekind Infinity and full Rosser Counting**. In that model, `T(n) = n` holds for every natural number of the model.

The proposed equivalence with inconsistency of **pure NF + AxCount** also uses two written mathematical arguments. Their respective roles are given below.

## What the machine recognizes

The machine has 192 working states, a separate halt, and 384 transitions. It starts in `k:64` on an all-zero tape. Its 3,351-instruction register program searches for a finite derivation of formula code 3, the equation `Q = J`.

| Claim | Evidence |
| --- | --- |
| The machine halts exactly when there is a J-point derivation of code 3. | `Counting192J.halts_iff_jpoint_goal` |
| It runs forever exactly when the ten schemata have a nondegenerate J-point model, in which `Q ≠ J`. | `Counting192J.nonhalting_iff_jpoint_chart` |
| If it runs forever, there is an NFU model with Dedekind Infinity and full Rosser Counting. | `Counting192J.nonhalting_implies_counting_model` |

The last result gives a one-sided set-theoretic guarantee. If NFU with Dedekind Infinity and full Rosser Counting is inconsistent, this machine halts. NFU allows urelements. The construction uses a represented proper self-injection on a strongly Cantorian set.

## Where pure NF enters

| Direction for pure NF + AxCount | Additional argument |
| --- | --- |
| Consistency implies nonhalting. | Starting from a model of pure NF + AxCount, prescribe the rows of an applicative model along its internal natural numbers. Each successor row returns its predecessor at every argument. The construction and completion of the represented graph are given on paper. Lean checks that the resulting data give the required J-point model, in `NF193.Upper.Splice.Operations.chart`. |
| Nonhalting implies consistency. | Start with the NFU model constructed in Lean. Proposition 17.13 and the first row of Theorem 21.1 in Ran Gutin’s *Choice and Consistency Strength in NF and NFU*, v15, compare this NFU theory and pure NF + AxCount to the same first-order theory. These relative-consistency results are claims in a research draft awaiting independent verification. |

Taken together, the written arguments give the proposed “halts iff pure NF + AxCount is inconsistent” conclusion. The proof of each Lean theorem in the first table is independent of both written arguments. The companion archive includes the detailed graph construction in `Calibration.md` and the relevant manuscript pages in `references/Counting_comparisons_v15_excerpt.pdf`.

## Files and reproduction

| File | Contents |
| --- | --- |
| [NF_AxCount_Jpoint_192.tm](NF_AxCount_Jpoint_192.tm) | Literal transition table |
| [Counting192J.lean](Counting192J.lean) | Formal halting and model equivalences |
| [Counting192JCalibration.lean](Counting192JCalibration.lean) | Formal implication from blank-tape nonhalting to the NFU model |
| [NF_AxCount_Jpoint_192_Verification.zip](NF_AxCount_Jpoint_192_Verification.zip) | Machine proof sources, all ten schemata, table reconstruction, independent simulator and verification receipts |
| [Jpoint_Calibration.zip](Jpoint_Calibration.zip) | Model-construction proofs, pinned dependencies, written comparisons and replay instructions |
| [SHA256SUMS](SHA256SUMS) | SHA-256 checksums for the files in this directory |

To check the table against the formalization, use Python 3. For the independent tape simulation, also install a C++17 compiler.

```sh
sha256sum -c SHA256SUMS
unzip NF_AxCount_Jpoint_192_Verification.zip
unzip Jpoint_Calibration.zip
cd NF_AxCount_Jpoint_192
cmp candidate.tm ../NF_AxCount_Jpoint_192.tm
python3 verify.py
python3 independent/run.py candidate.tm source.sites.json reference/counting196.tm --output replay.json
```

The two archived READMEs give the Lean 4.35.0 rebuild commands. Build the machine and the companion, then run the companion’s **Link the literal 192-state machine** command to check their composition. The machine theorem uses Lean’s propositional extensionality, classical choice, quotient soundness and eleven finite checks performed by native evaluation. The mathematical NFU interpretation adds no further axioms to that list.

The table’s SHA-256 is `34698929dc83de04608eabd889ca898f34a23800c483b03386922ca51e8f25ee`.
