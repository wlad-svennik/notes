# Peano arithmetic and the 185-state pure NF machine

Let $H_{185}$ be the arithmetic sentence saying that the [published 185-state table](../NF185.tm) halts from a blank tape. Let $H_{192}$ refer to the original [**pure NF countdown** machine](../../nf-bb192/). The [192-state Rosser Counting machine](../../nf-axcount-bb192/) is a separate release. The two first-order arithmetic theorems are

$$
\mathrm{PA}\vdash H_{192}\to H_{185},
\qquad
\mathrm{PA}\vdash\neg H_{185}\to\mathrm{Con}(\mathrm{PA}).
$$

The first claim says that a halt of the 192-state machine forces a halt of the 185-state machine, even inside a nonstandard model of PA. A different sequence of commands can realize the proof on the smaller machine. The second claim has a separate proof from the 185-state machine alone. Both input tables are identified by their SHA-256 digests.

| Blank-tape machine | SHA-256 |
| --- | --- |
| [185-state eight-row machine](../NF185.tm) | `5504746071e10a0555754b55efc2da348ebfb1f8e8ab5bc7af474eaad81f60fe` |
| [192-state pure NF countdown](../../nf-bb192/NF_192_countdown.tm) | `ee1391964b35c7ad2f0db90305a84e09c6523f73f3dce6c4f31a182aa270d565` |

## Consequences

| Hypothesis | Conclusion |
| --- | --- |
| PA is consistent | PA cannot prove that this particular 185-state machine runs forever. |
| Pure NF is consistent | The machine runs forever on an ordinary blank tape. PA proves neither sign of its halting sentence. For every standard numeral $k$, PA cannot prove $\mathrm{BB}(185)\le k$. |
| Pure NF is consistent | For the actual value $k=\mathrm{BB}(185)$, PA proves neither $\mathrm{BB}(185)=k$ nor its negation. |

Here $\mathrm{BB}$ is the maximum running time among the halting blank-tape two-symbol machines of the stated size. The two claims excluding a proof of a false arithmetic sentence use soundness of PA in the standard natural numbers, established in the ambient Lean development. NF consistency is their only explicit assumption. The exact-value assertion singles out the actual numeral. The upper-bound assertion covers **every** numeral. No value of $\mathrm{BB}(185)$ is computed.

For the upper bound argument, fix any numeral $k$. Under NF consistency the machine survives its first $k$ steps, and PA verifies that finite computation. A PA proof of the proposed upper bound would then yield a PA proof that the machine runs forever, contradicting the second incompleteness theorem. This is where actual nonhalting enters the argument.

## How the proofs fit together

The published machine has 185 working states and two symbols. From blank, it takes 59,905 binary steps to reach the verified register configuration. Its register program has 2,959 instruction addresses and searches an eight-row calculus.

The direct proof works in an arbitrary model of PA. A coded refutation in the eight-row calculus forces a successful cache test in the arithmetic scanner. The register proof follows it through the precise signed startup and all axiom batches to the terminal address. The tape proof turns that execution into a trace of the published table. If the ambient model has no coded halting trace, the scanner implication rules out an eight-row refutation there. The resulting definable countermodel provides a truth predicate that validates the ambient model's own coded PA derivations. This rules out an internally coded PA derivation of falsity. First-order completeness then gives the displayed PA theorem.

The machine-to-machine argument must also transport the calculus. A halt of the original machine produces an internally coded nine-row proof of its goal. If the eight-row search failed, its countermodel would give a model of the old rows in which that goal is false. Numerical term and formula evaluation in that model validates modus ponens even for nonstandard proof lengths. In particular, formula code zero denotes truth and the self-collision $\mathrm{imp}(0,0)=0$ respects the implication truth condition. See the [transfer proof](TRANSFER.md).

## What “proved in PA” means

The Lean statements assert provability in the first-order theory `M6.PA.theory`. They refer to the actual machines' arithmetic halting formulas and the ordinary arithmetized PA consistency sentence. They cover models with nonstandard computation times and proof codes. Lean establishes the existence of a first-order PA derivation by arithmetic completeness. The archive contains this argument and its finite verification inputs. The transfer's base theory here is PA. The older paper also analyzes several intermediate proof transformations in primitive recursive arithmetic.

## Lean entry points

| Claim | Declaration |
| --- | --- |
| PA proves that halting transfers from 192 to 185 | `NF185PA.machine_transfer` |
| PA proves nonhalting at 185 implies PA consistency | `NF185PA.internal_consistency` |
| Assuming PA consistency, PA cannot prove this machine runs forever | `NF185PA.pa_cannot_prove_nonhalting_of_consistent` |
| Assuming NF consistency, every numerical upper bound at 185 is unprovable in PA | `NF185PA.pa_independence` |
| PA proves neither sign of equality to the actual value, assuming NF consistency | `NF185PA.true_value_independent` |

The [Lean entry file](NF185_PA.lean) states both arithmetic theorems. Its [axiom report](AXIOMS.txt) lists the dependencies printed for each endpoint. The earlier [NF192 arithmetic paper](https://github.com/wlad-svennik/notes/releases/tag/nf192-pa) documents the original countdown machine.

## What the axiom audit measures

The direct 185-state consistency theorem and the Gödel consequence use `propext`, `Classical.choice` and `Quot.sound`. The 185-state tape certificate is split across 93 files, so each closed calculation can be reduced in the Lean kernel. The underlying rule for lifting a validated register step to a tape trace applies to register values of any length in the PA model.

The 192-to-185 theorem also uses 65 native decisions from the published 192-state tape certificates. Each decides a particular closed Boolean on the archived transcript and its address index. The Busy Beaver results under NF consistency use the earlier external 185-state calibration, which has eleven native decisions. The numerical upper-bound argument for an individually verified live prefix uses the direct 185-state theorem. The axiom report names every decision appearing in each public theorem.

The release check compiled the new proofs against previously built, pinned dependencies. Each of the 93 new tape batches was reduced in the Lean kernel. The archive includes the sources for rebuilding the complete dependency graph and records which checks were performed for this release.

## Reproduce the verification

The [complete verification download](NF185_PA_verification.tar.xz) is **1,549,656 bytes**. It includes all 844 Lean sources, the 93 tape proof batches, the literal machine tables, the proof notes and the original NF192 certificate generator. Python reconstructs the 65 historical transcripts and 65 address indexes locally from the included inputs and checks each against its published SHA-256. No additional download is needed for certificate reconstruction. The full Lean build still needs its pinned compiler and Mathlib dependencies.

Download the archive, [replay script](replay_archive.py) and [checksums](SHA256SUMS). From the download directory, verify the downloaded files and run the full proof replay. It checks the numerical inputs, builds both PA theorems and the Busy Beaver corollaries, and audits the resulting declarations.

```sh
sha256sum --check --ignore-missing SHA256SUMS
python3 replay_archive.py NF185_PA_verification.tar.xz --work nf185-replay --target NF185_PA --jobs 2
```

The full build needs Python 3 and elan with access to the pinned Lean 4.35.0 and Mathlib dependencies. The argument `--work` names a new directory. To check the archive manifest and the connection between the published transition table and the Lean literals using Python alone, add `--verify-only`. Inside the extracted directory, `REGISTER-PROOF.md` describes the compiler and startup proofs, `COMPARISON-PROOF.md` explains the interpretation between the proof pools, and `sources.json` identifies the source of each Lean module.

The earlier [22,355,600-byte archive](https://github.com/wlad-svennik/notes/blob/bfc960b0725ecab9be07518cc35954662f2592e7/nf-bb185/pa/NF185_PA_verification.tar.xz) contains the transcripts already expanded. The compact package reproduces every original file, including its original packaging files in `nf192_generator/original-packaging/`.
