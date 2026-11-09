# NF certificate and consistency calibration

## Checked result

The following declarations compile under the unchanged official Lean 4.35.0
compiler and depend exactly on `propext`, `Classical.choice`, and `Quot.sound`:

- `NF210.ProofMM.mm_peano4`: the replayed finite-cardinal successor-injectivity theorem.
- `NF210.NFFrege.peano4`: successor injectivity for this project's explicit Frege natural-number class.
- `NF210.NFModel.toCore`: the pair-free combinatory core in every model of the original NF axioms.
- `NF210.Proof.nf_consistency_iff_ground_consistency`: actual first-order NF consistency iff the exact numerical ground calculus does not derive its displayed goal.
- `NF210.Proof.ground_goal_iff_nf_refutation`: the corresponding refutation equivalence.

`NF210.ProofCalibration` composes this equivalence with the frozen register
source's proved simulation. Its endpoints are
`source_halting_iff_nf_refutation`, `nf_consistency_iff_source_nonhalting`, and
`source_halting_iff_nf_inconsistent`.

The NF proof predicate in these statements is Foundation's finite first-order
LK derivability from equality, extensionality, and every stratified
comprehension instance. It is not defined as semantic validity. Stratification
witnesses are finite integer lists; the syntax module proves that this includes
every instance allowed by the project's original NFModel definition.

## Source certificate

The input is the public-domain/CC0 Metamath NF database, originally created by
Scott Fenton from set.mm. Its attribution and license are retained in the
original file.

- Source URL: https://raw.githubusercontent.com/metamath/set.mm/develop/nf.mm
- Source SHA256: `3298459d03635e5cdb9d8505d13919eff014b65a5bece1825b0c4f754a0554d1`
- Target label: `peano4`.
- Dependency slice: 1,901 Metamath proved assertions, including two syntax assertions.
- Logical theorem replay: 974 logic lemmas and 925 set-theory lemmas.
- The source slice contains 40,934 rule applications, including syntax construction.
- Logical/nonlogical assertion leaves: 93, all proved in Lean.

The leaves are split among ProofMMLogicLeaves (28), ProofMMClassLeaves (42),
ProofMMArithmeticLeaves (13), and ProofMMNFLeaves (10). The ten nonlogical
set-existence leaves are actual stratified-comprehension consequences in
NFHailperin. No Infinity axiom, successor-injectivity axiom, global model
existence assumption, or imported Metamath assertion is declared as a Lean axiom.

## Replay and trust

`tools/nf_metamath_certificate.py` reads scopes, floating/essential hypotheses,
compressed proofs, substitutions, and distinct-variable conditions. Its
verification result is diagnostic and is never imported as a trusted fact.
`tools/nf_metamath_lean.py` parses syntax, and `tools/nf_metamath_replay.py`
generates ordinary Lean theorem applications.

The semantic prelude uses expressions with finite name supports, named binders,
and a proved environment-dependence bound. Distinct-variable conditions become
actual disjointness/freshness premises. Every proof-local set variable is chosen
above the maximum input support, with checked freshness and distinctness lemmas.
This handles repeated names, identified metavariables, and capture conditions;
no freshness premise is silently dropped.

Lean checks every generated theorem application. The Python parser and proof
reader are not in the trusted base. The final Frege statement is separately
connected to the project's explicit sets and operations in ProofNFCertificate.

## Reproduction

Use the project's scoped compiler-launch compatibility wrapper; the original
compiler binary and kernel are unchanged. The helper
`tools/check_nf_proof_module.py` computes the local project/Foundation package
paths and launches the compiler with `autoImplicit=false`.

The pinned Foundation commit is
`63bfd1b2e821dc2367b08f68d379303d08631f83`; its mathlib commit is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. These use Lean 4.35.0.

The generated proof modules can be checked directly without running Python.
To regenerate the two replay modules from the exact source file:

```sh
python3 tools/nf_metamath_replay.py /path/to/nf.mm \
  --out NF210/ProofMMLogicReplay.lean
python3 tools/nf_metamath_replay.py /path/to/nf.mm \
  --out NF210/ProofMMPeano4.lean --set-theory-suffix
```

Compile the prelude/leaves/support modules first, then the two replay modules,
ProofNFCertificate, and ProofCalibration. `ProofCertificateAxioms.lean` reproduces
the printed axiom audit. The complete project build configuration owns the
portable dependency setup.

## Scope still outstanding

These are external Lean proofs. They do not themselves supply an NF derivation
of an encoded machine/consistency implication, a completed arithmetic
interpretation and proof-code bridge, or the requested Busy Beaver
unprovability theorem. The exact binary-machine simulation is another project
component and must be composed explicitly. No PA-internal proof object is
claimed by these modules.
