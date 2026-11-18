# NFU + Infinity and NF: the interpretations as statements about derivations

15–16 November 2026, fourth version (16 November, 00:05). Companion to `nfu_inf_interprets_nf_proof_2026-11-13.md` and `nf_infinity_not_choice_2026-11-15.md`.

**Added in the fourth version:** the files that do not need con-nf now build without it, as a lake project of their own (§12). Three consistency theorems moved to a new file, `NFConsistentViaConNF.lean`; no statement or proof changed.

**Added in the third version:** a direct proof that NFU + Infinity is consistent, by a model built in the manner of Jensen, and from it a second proof that NF is consistent which does not use con-nf's model (§11). Nothing else changed.

The first version of this note (21:00) had the theorems for NFU with a predicate "is a set". This version adds Jensen's NFU in the language of ∈ and = alone, two more forms of Choice, a single lake project, and the results of two checkers. **Notation changed:** `𝗡𝗙𝗨`, `𝗜𝗡𝗙`, `𝗡𝗙𝗨𝗜` now denote the theories in the bare language; the versions with the predicate are `𝗡𝗙𝗨ₛ`, `𝗜𝗡𝗙ₛ`, `𝗡𝗙𝗨𝗜ₛ`.

## 0. Result

The completeness theorem for first-order logic is proved in Lean 4 in the library Foundation (FormalizedFormalLogic/Foundation), not in Mathlib. Foundation also has a class for interpretations between theories, with a lemma that an interpretation carries derivations to derivations. The interpretations are instances of that class, between theories stated in Foundation's own formula type.

Ten Lean files, 4,008 lines, no `sorry`:

| File | Lines | Content |
|---|---|---|
| `NFTheories.lean` | 315 | stratification; the theories `𝗡𝗙`, `𝗡𝗙𝗨`, `𝗜𝗡𝗙`, `𝗡𝗙𝗨𝗜`; the language with "is a set" and `𝗡𝗙𝗨ₛ`, `𝗜𝗡𝗙ₛ`, `𝗡𝗙𝗨𝗜ₛ`. Imports only Foundation. |
| `NFUInterpretsNFEq.lean` | 262 | the interpretation of NF with equality interpreted by equality |
| `NFChoiceForms.lean` | 152 | Zorn's lemma and choice functions imply the form of Choice that NF refutes |
| `NFInterpretations.lean` | 1,196 | `𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙`, `𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜ₛ`, theorems of `𝗡𝗙` |
| `NFUShift.lean` | 393 | inside NFU: a second membership relation, defined from ∈ alone |
| `NFUJensen.lean` | 734 | `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙𝗨𝗜ₛ`, hence `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`; `𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜`; `𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙` |
| `NFUJensenModel.lean` | 673 | a model of NFU in which the universe is not finite (§11). Imports Mathlib and `ConNF.NF.Generic` only. |
| `NFUConsistent.lean` | 229 | `Consistent 𝗡𝗙𝗨𝗜` from that model. Imports `NFTheories` and `NFUJensenModel` only. |
| `NFConsistentViaNFU.lean` | 20 | `Consistent 𝗡𝗙` from the line above and `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙` |
| `NFConsistentViaConNF.lean` | 34 | the earlier consistency proofs, from con-nf's model. The only one of the ten that needs con-nf (§12). |

The statements, as Lean prints them. `⊢` is derivability in Foundation's calculus for classical first-order logic, `T ⊳ U` is "T interprets U", `⋈` is "interpret each other", `T ⪯ U` is "every theorem of T is a theorem of U". All are in the namespace `FFL.FirstOrder.SetTheory`.

```lean
-- NFU + Infinity (Jensen's, language ∈ and =) and NF
instance nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙
instance nfInterpretsNFU : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜
instance nfuMutualNF     : 𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙
instance nfui_weakerThan_nf : 𝗡𝗙𝗨𝗜 ⪯ 𝗡𝗙
theorem nfu_provable_translate_of_nf {σ : Sentence ℒₛₑₜ} : 𝗡𝗙 ⊢ σ → 𝗡𝗙𝗨𝗜 ⊢ nfuInterpretsNF σ
theorem consistent_nfuInfinity_iff_consistent_nf :
    Entailment.Consistent 𝗡𝗙𝗨𝗜 ↔ Entailment.Consistent 𝗡𝗙

-- the two formulations of NFU + Infinity
instance interpretsNFUs : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙𝗨𝗜ₛ
instance nfuMutualNFUs  : 𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙𝗨𝗜ₛ

-- theorems of NF
theorem nf_provable_universeInfinite : 𝗡𝗙 ⊢ Axiom.universeInfinite
theorem nf_provable_not_choice       : 𝗡𝗙 ⊢ ∼Axiom.choice
theorem nf_provable_not_zorn         : 𝗡𝗙 ⊢ ∼Axiom.zorn

-- consistency
-- consistency, from con-nf's model (NFConsistentViaConNF.lean)
theorem consistent_nf           : Entailment.Consistent 𝗡𝗙
theorem consistent_nfuInfinity  : Entailment.Consistent 𝗡𝗙𝗨𝗜    -- from the line above

-- consistency again, without con-nf's model (§11)
theorem Jensen.consistent_nfuInfinity : Entailment.Consistent 𝗡𝗙𝗨𝗜   -- from a model of NFU + Infinity
theorem consistent_nf_of_jensen       : Entailment.Consistent 𝗡𝗙     -- from the line above and 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙
```

`Axiom.choice` is Foundation's own sentence (a choice set for every family of pairwise disjoint sets with members). `consistent_nf` uses the model `ConNF.NF.exists_nf` that the development already had; `consistent_nf_of_jensen` does not. For the predicate version the corresponding statements are `SetTheoryU.interpretsNF : 𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙`, `SetTheory.interpretsNFUI : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜ₛ`, `SetTheoryU.mutualInterpretation`, `SetTheory.provable_unset_of_nfui`.

Every statement depends only on `propext`, `Classical.choice`, `Quot.sound`.

## 1. What existed

- **Mathlib.** `Mathlib/ModelTheory` has syntax, semantics, satisfiability, and compactness by ultraproducts. It has no proof calculus, so no completeness theorem. I checked the copy our build uses.
- **Foundation.** `Theory.Proof.complete_on_eq_models`: if a sentence holds in every structure with true equality that satisfies `T`, then `T ⊢ φ`. `SetTheory.complete` is the same for the language `ℒₛₑₜ` with structures given by a membership relation. `Foundation/FirstOrder/LK/Interpretation.lean` defines `DirectTranslation` (a domain formula and a formula for each symbol), `DirectInterpretation T U`, written `T ⊳ U` (a translation together with derivations in `T` of the translated axioms of `U`), `T ⋈ U`, composition, and proves

  ```lean
  lemma DirectInterpretation.sound : U ⊢ σ → T ⊢ π σ
  ```

- **Versions.** Foundation at commit `fbcfee52` (12 November 2026) uses Lean 4.35.0 and pins Mathlib at `56a00585`. Both are the versions of our con-nf build.

## 2. The theories (`NFTheories.lean`)

This file is what has to be read to know what the theorems say.

**Stratification.** One definition for all languages without function symbols. A class says how each relation symbol relates the types of its arguments:

```lean
class Language.Stratification (L : Language) where
  lv {k : ℕ} : L.Rel k → Fin k → ℕ        -- for ∈ : ![0, 1];  for = : ![0, 0];  for "is a set" : ![0]

def Semiformula.Stratified (σ : ξ → ℕ) {n : ℕ} (τ : Fin n → ℕ) : Semiformula L ξ n → Prop
  | .rel r v  => ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i
  | .nrel r v => ∃ t, ∀ i, (v i).lv σ τ = t + Language.Stratification.lv r i
  | ⊤ => True
  | ⊥ => True
  | φ ⋏ ψ => φ.Stratified σ τ ∧ ψ.Stratified σ τ
  | φ ⋎ ψ => φ.Stratified σ τ ∧ ψ.Stratified σ τ
  | ∀¹ φ => ∃ t, φ.Stratified σ (t :> τ)
  | ∃¹ φ => ∃ t, φ.Stratified σ (t :> τ)

def Semiformula.IsStratified (φ : Semiformula L ξ n) : Prop := ∃ σ τ, φ.Stratified σ τ
```

`σ` types the free variables, `τ` the bound variables in scope, and each quantifier chooses a type for its variable.

**NF and NFU**, both in `ℒₛₑₜ`:

```lean
def Axiom.comprehensionSchema (φ : SetTheorySemiproposition 1) : SetTheorySentence :=
  .univCl “∃ y, ∀ x, x ∈ y ↔ !φ x”

inductive NewFoundations : SetTheory                         -- 𝗡𝗙
  | equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, NewFoundations φ
  | extensionality : NewFoundations “∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y”
  | comprehension (φ : SetTheorySemiproposition 1) :
      φ.IsStratified → NewFoundations (Axiom.comprehensionSchema φ)

inductive NewFoundationsWithUrelements : SetTheory           -- 𝗡𝗙𝗨
  | equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, NewFoundationsWithUrelements φ
  | extensionality :
      NewFoundationsWithUrelements “∀ x y, (∃ z, z ∈ x) → (∀ z, z ∈ x ↔ z ∈ y) → x = y”
  | comprehension (φ : SetTheorySemiproposition 1) :
      φ.IsStratified → NewFoundationsWithUrelements (Axiom.comprehensionSchema φ)
```

The two differ only in extensionality: `𝗡𝗙𝗨` has it for objects with members. This is Jensen's NFU.

**Infinity.**

```lean
def Axiom.universeInfinite : SetTheorySentence :=
  “∃ F, (∀ e, (∀ z, z ∉ e) → e ∈ F) ∧
    (∀ s ∈ F, ∀ b s', (∀ z, z ∈ s' ↔ z ∈ s ∨ z = b) → s' ∈ F) ∧
    (∀ u, (∀ z, z ∈ u) → u ∉ F)”
```

Some family contains every object without members and is closed under adjoining one element, but contains no universal set. `𝗜𝗡𝗙` is this one sentence and `𝗡𝗙𝗨𝗜 := 𝗡𝗙𝗨 ∪ 𝗜𝗡𝗙`. Over `𝗡𝗙𝗨` it gives `NFUCut.Model.Infinity` ("the universe belongs to no natural number"): `modelOfJensenNFU_infinity`.

**The versions with a predicate.** `ℒₛₑₜᵤ` has a third relation symbol "is a set". `𝗡𝗙𝗨ₛ` says: only sets have members, sets with the same members are equal, and stratified comprehension gives a set. `𝗜𝗡𝗙ₛ` is Infinity with "empty set" in place of "object without members". These are the theories that correspond to `NFUCut.Model`; they are now intermediate.

Checks on the definitions, in Lean: `x ∉ x` is not stratified (`not_isStratified_not_mem_self`), `𝗡𝗙` proves that a universal set exists (`nf_provable_exists_universal`), `𝗡𝗙𝗨𝗜 ⪯ 𝗡𝗙`, and both theories are consistent.

## 3. Jensen's NFU: why it needed work, and what was done

In `𝗡𝗙𝗨ₛ` there is one empty set and the other objects without members are urelements. In `𝗡𝗙𝗨` nothing distinguishes one object without members from another, and in general none of them is definable. (That remark is the reason for the construction and is not itself proved in Lean.) So "let the empty set be this one" needs a parameter, and Foundation's interpretations have no parameters. Since no object without members can be named, the empty set of the interpreted structure has to be an object *with* members, and then its old role has to be taken over by something else, and so on. That is a Hilbert hotel, and it needs an infinite definable sequence. With Infinity there is one: the Frege numbers.

**The construction** (`NFUShift.lean`, for any `NFUCut.Model` with Infinity; every definition uses ∈ alone).

- `OneW w`: the members of `w` are the singletons. `SuccW s k`: `s` has the members of the successor of `k`. `InP u`: `u` belongs to every family that contains the number one and is closed under successor. So `InP` picks out the positive numbers 1, 2, 3, … (`inP_iff`).
- The new membership:

  ```lean
  def MemS (x y : V) : Prop :=
    (∃ k, M.InP k ∧ M.SuccW y k ∧ M.mem x k) ∨ (¬ M.InP y ∧ M.mem x y)
  ```

  The number 1 has no new members (`not_memS_one`): it is the new empty set. The number k+1, for k ≥ 1, has the old members of k (`memS_succ_succ`). Every other object keeps its members (`memS_of_not`). "Is a set" is read as "has a member in the old sense".
- `exists_codeS`: every collection has a code, that is, for every `z` some object with members has exactly the members of `z` as its new members. `memS_ext`: extensionality for the new membership among objects with old members. `memS_nonempty`: only those have new members. `shift_infinity`: Infinity holds in the new sense; the witness is the code of the set of codes of finite sets.

The proofs use the arithmetic of the Frege numbers that the library already had (`succ_inj`, `nat_nonempty`, `nat_cases`, `zero_ne_succ`).

**In Foundation's syntax** (`NFUJensen.lean`).

- `modelOfJensenNFU`: a model of `𝗡𝗙𝗨`, with *any* object without members chosen as the empty set, is a `NFUCut.Model`. The choice is made inside the proof, in each model. It appears in no formula. One point needed care: in comprehension the chosen object is a parameter, and a parameter has one type, while "is a set" is applied to variables of several types. The translation uses a separate free variable for each type, all given the same value.
- `memStarF t u`: the formula `MemS`, translated from the named-variable formula `fMemS`, whose stratification is checked by `decide`. `Semiformula.star` replaces `∈` by `memStarF` and "is a set" by "has a member". It preserves stratification with every type raised by one (`stratified_star`), because `MemS x y` mentions objects one type below `x`.
- `setTranslation` and `setModel_models_nfus`: in every model of `𝗡𝗙𝗨𝗜` the structure with the new membership is a model of `𝗡𝗙𝗨𝗜ₛ`. Hence `interpretsNFUs : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙𝗨𝗜ₛ`, and by composition with `𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙`, `nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`.
- The other direction is immediate: each axiom of `𝗡𝗙𝗨𝗜` is an axiom or a theorem of `𝗡𝗙`, so `𝗡𝗙𝗨𝗜 ⪯ 𝗡𝗙` and the identity interprets.

## 4. The other transformations

**From NF to `𝗡𝗙𝗨𝗜ₛ`** (`SetTheoryU.interpretsNF`): the domain is `nfDomain` (the formula `nfDom`, the least code in each class of the term model), `∈` becomes `nfMem` (the formula `nfEps`), `=` stays `=`, quantifiers are restricted to the domain. Both formulas are closed by their type, so there are no parameters.

**From `𝗡𝗙𝗨𝗜ₛ` to NF** (`SetTheory.interpretsNFUI`): the domain is everything and "is a set" is true. `provable_unset_of_nfui` states the same with the map `unset`, which replaces each atomic formula "is a set" by `⊤`.

**Equality.** Foundation requires equality to be interpreted by equality. `nfu_inf_interprets_nf` interprets it by a formula η. `NFUInterpretsNFEq.lean` removes the difference by taking the least code in each η-class as the domain (`MinTm`, `exists_minTm`, `minTm_unique`, `dom_isNF`).

## 5. How the derivations are obtained

Every derivation `T ⊢ φ` in these files comes from completeness: it is enough that `φ` holds in every model of `T`. The models are connected to the earlier theorems by these bridges.

| Bridge | Statement |
|---|---|
| `SetTheoryU.modelOfNFU` | a model of `𝗡𝗙𝗨ₛ` gives a `NFUCut.Model` (`ofFml`, `stratified_ofFml`, `eval_ofFml`) |
| `SetTheoryU.modelOfNFU_infinity_iff` | `𝗜𝗡𝗙ₛ` holds iff the `NFUCut.Model` has `Infinity` |
| `SetTheory.modelOfJensenNFU` | a model of `𝗡𝗙𝗨` and an object without members give a `NFUCut.Model` (`ofFmlS`) |
| `SetTheory.models_nf_of_isNF` | a structure with `ConNF.NF.IsNF` is a model of `𝗡𝗙` (`exists_fm`) |
| `Semiformula.eval_unset`, `Semiformula.eval_star` | the two translations of formulas preserve meaning |

## 6. Other forms of Choice (`NFChoiceForms.lean`)

`NFSpecker.lean` refutes Choice in the form `Model.AC` (choice sets for disjoint families) and proves directly that the universe has no well-ordering. Now also, in every model of NFU:

```lean
theorem zorn_ac            : M.ZornLemma → M.AC
theorem choiceFunctions_ac : M.ChoiceFunctions → M.AC
```

`ZornLemma`: a family in which every chain (for inclusion) has an upper bound has a maximal member. `ChoiceFunctions`: every set of sets with members has a choice function; the function sends a set to the *singleton* of the chosen member, which is what makes the statement stratified. So NF refutes both (`nf_not_zorn`, `nf_not_choiceFunctions`, `IsNF.not_zorn` with membership alone), and `𝗡𝗙 ⊢ ∼Axiom.zorn` as a statement about derivations. The choice-function form is proved at the level of models only: as a sentence of `ℒₛₑₜ` it would need ordered pairs written out.

## 7. Style: what I did and why

1. **Use the library's notion, not a new one.** "There is a syntactic transformation that preserves provability" is the content of `T ⊳ U` together with `sound`. Stating it as instances made the passage to Jensen's NFU a one-line composition (`DirectInterpretation.comp`).
2. **State the theories in the library's formula type**, in its idiom: a theory is an inductive set of sentences with an `equality` constructor and an instance `𝗘𝗤 _ ⪯ T`; a schema is a function on `Semiproposition 1` built with `univCl “…”`; the side condition is a hypothesis of the constructor; notation in bold sans-serif. The unadorned names go to the standard theories (`𝗡𝗙𝗨` is Jensen's).
3. **Stratification as a recursive predicate on formulas**, with a `@[simp]` lemma per constructor and `stratified_neg`. The class `Language.Stratification` keeps one definition for both languages.
4. **Derivations by completeness, in the library's pattern**: `apply Theory.Proof.complete_on_eq_models.{_, 0}; intro M _ _ _ hT; …`, as in its `DirectTranslation.id`; `SetTheory.complete` where Foundation's simp lemmas for its defined predicates are wanted.
5. **One meaning lemma per axiom** (`models_extensionality_iff`, `models_comprehension_iff`, `models_universeInfinite_iff`, …), each proved by `simp [models_iff, …]`. No other proof depends on how `simp` normalises a formula.
6. **Write complicated formulas with named variables and translate them.** `fMemS` is a `NFUCut.Fml`; its stratification is `by decide` and its meaning is computed with the existing lemmas. `ofFmlS` turns it into a formula of Foundation, and two general lemmas carry stratification and meaning across.
7. **Split by dependency.** `NFTheories.lean` imports only Foundation.

Where the files depart from Foundation's house style, to change before proposing anything upstream: Foundation's files use Lean's module system (`module`, `public import`, `@[expose] public section`) and ours are plain files; `NFInterpretations.lean` and `NFUJensen.lean` would each be several files; structures are in `Type`, not universe polymorphic; the names `ℒₛₑₜᵤ`, `SetTheoryU`, `𝗜𝗡𝗙`, `𝗡𝗙𝗨𝗜`, `𝗡𝗙𝗨ₛ` are mine.

## 8. Building and checking

**One lake project.** All twelve of our files (`Host`, `HostTerm`, `NFUTerm`, `NFUInterpretsNF`, `NFSpecker`, `MutualInterpretability` and the six of §0) are now the library `NFInterp` of a lake project that requires con-nf and the Foundation build as path dependencies. `lake build` built them (3,299 jobs, no errors; linter warnings in the older files) and reported con-nf, Foundation and Mathlib up to date. `nf-interp-2026-11-15.tar.gz` contains the project: the files, `lakefile.toml`, the manifest, `con-nf.patch`, and a README with the steps.

**`con-nf.patch`.** Our changes to con-nf relative to upstream commit `edbce7eb` (23 October 2026): 16 new files and 13 modified ones. Applied to a fresh clone at that commit, it reproduces the `ConNF/` directory that was built, file for file.

**Replay in Lean's kernel.** `leanchecker`, one module per call, on each of the twelve files and each of the fourteen `ConNF.NF.*` files: 26 runs, all with exit status 0 and no output.

**An independent checker.** `nanoda` 0.4.19, a type checker for Lean written in Rust, on files produced by `lean4export` 3.1.0:

| Export | Declarations | Result |
|---|---|---|
| twelve main theorems and everything they depend on (`nfuMutualNF`, `consistent_nfuInfinity_iff_consistent_nf`, `nfu_provable_translate_of_nf`, `nfuMutualNFUs`, `SetTheoryU.mutualInterpretation`, `nf_provable_not_choice`, `nf_provable_not_zorn`, `nf_provable_universeInfinite`, `provable_unset_of_nfui`, `NFUCut.nf_nfu_inf_mutually_interpretable`, `nf_not_choiceFunctions`, `IsNF.not_zorn`) | 15,313 | no errors, 50 s |
| `consistent_nfuInfinity`, `consistent_nf`, `consistent_nfui` and everything they depend on, which includes the con-nf model | 21,624 | no errors, 56 s |

In both runs the only axioms were `propext`, `Quot.sound`, `Classical.choice`, and any other axiom was set to be a hard error. nanoda prints back what it read; for example

```
theorem FFL.FirstOrder.SetTheory.consistent_nfuInfinity_iff_consistent_nf :
  Iff (FFL.Entailment.Consistent FFL.FirstOrder.SetTheory.NFUInfinity)
    (FFL.Entailment.Consistent FFL.FirstOrder.SetTheory.NewFoundations) := _
```

**Tried and not usable.** `lean4lean`, the other independent kernel in the toolchain directory, rejects every compiled file, including Lean's own, with "incompatible header". The binary does not match this Lean version.

## 9. What is still not checked

1. That `NFTheories.lean` states the intended theories. For the headline statements this means `Stratified`, `𝗡𝗙`, `𝗡𝗙𝗨`, `Axiom.universeInfinite`, about sixty lines, and Foundation's definitions of `⊢`, `⊳` and `Consistent`. This cannot be a Lean theorem.
2. No derivation is constructed. Completeness is proved classically, so the theorems say that derivations exist. The maps on formulas (`translate`, `unset`, `star`, `ofFml`) are explicit definitions.
3. Foundation is built from a copy of its `Foundation/` directory under a lakefile of mine, not under its own lakefile, which also requires a package (`Forgive`) that the 69 modules used here do not import.
4. con-nf was not rebuilt from the fresh clone; the build that was used is the working tree's, and the patch was shown to reproduce that tree.
5. `leanchecker --fresh`, which would replay Mathlib as well, was not run. nanoda did check everything the listed theorems depend on, Mathlib declarations included.
6. The choice-function form of Choice is refuted for models, not as a sentence of `ℒₛₑₜ` (§6).

## 10. Not attempted

- §8 item 2 of the main document: that the equiconsistency is provable in PRA. It needs arithmetised syntax and an interpretation whose correctness is proved by explicit derivations, not through models.
- §8 item 3: the chain through C₀ and M198. It needs those two implications in Lean.
- §8 item 4: Mac Lane set theory. It rests on Jensen 1969 and Mathias 2001.
- The steps of the original plan (Transfer Lemma, cut-elimination bound, shortening of cuts). The theorem does not use them.

## 11. A direct consistency proof of NFU + Infinity (added 15 November, 23:30)

Until now `consistent_nfuInfinity` was obtained from `consistent_nf`, that is, from con-nf's model of NF. This section describes a proof that builds a model of NFU + Infinity directly, in the manner of Jensen 1969, and uses nothing about NF.

### 11.1 Statements

```lean
-- NFUJensenModel.lean  (namespace JensenNFU; imports Mathlib and ConNF.NF.Generic)
structure IsNFU (V : Type) (mem : V → V → Prop) : Prop where
  ext : ∀ x y, (∃ z, mem z x) → (∀ z, mem z x ↔ mem z y) → x = y
  comprehension : ∀ (t : ℕ) (Γ : List ℕ) (φ : TFm), TFm.Strat (t :: Γ) φ →
    ∀ params : List V, params.length = Γ.length → ∃ y, ∀ x, mem x y ↔ TFm.Sat mem φ (x :: params)

def UnivInfinite {V : Type} (mem : V → V → Prop) : Prop :=
  ∃ F : V, (∀ e, (∀ z, ¬mem z e) → mem e F) ∧
    (∀ a, mem a F → ∀ b a', (∀ z, mem z a' ↔ mem z a ∨ z = b) → mem a' F) ∧
    ∀ u, (∀ z, mem z u) → ¬mem u F

theorem exists_model : ∃ (V : Type) (mem : V → V → Prop), IsNFU V mem ∧ UnivInfinite mem

-- NFUConsistent.lean  (imports NFTheories and NFUJensenModel)
theorem Jensen.models_nfui_of_isNFU {N : Type} [Nonempty N] [SetStructure N]
    (h : IsNFU N (fun a b : N ↦ a ∈ b)) (hinf : UnivInfinite (fun a b : N ↦ a ∈ b)) :
    N↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜
theorem Jensen.consistent_nfuInfinity : Entailment.Consistent 𝗡𝗙𝗨𝗜

-- NFConsistentViaNFU.lean  (imports NFUJensen and NFUConsistent)
theorem consistent_nf_of_jensen : Entailment.Consistent 𝗡𝗙 :=
  consistent_nfuInfinity_iff_consistent_nf.mp Jensen.consistent_nfuInfinity
```

`TFm` is a type of formulas with de Bruijn indices whose quantifiers carry a type, with `TFm.Strat` and `TFm.Sat` defined as for `ConNF.NF.Fm`. It is a separate copy so that `NFUJensenModel.lean` does not import the NF development. `UnivInfinite` is `Axiom.universeInfinite` read in a structure.

### 11.2 The construction

**The base** (`Lvl`, `code`, `E`). Put L₀ = ℕ and Lₙ₊₁ = 𝒫(Lₙ), and let C be the disjoint union of the levels. For a < b fix an injection code₍a,b₎ : 𝒫(L_a) → L_b; one exists because 𝒫(L_a) = L_{a+1} maps into L_b by iterated singletons. For x of level a and y of level b put x E y iff a < b, y = code₍a,b₎(S) for some S ⊆ L_a, and x ∈ S. Three facts about each pair of levels a < b are all that is used later:

- `comp_base`: every collection of objects of level a is the set of level-a members of some object of level b;
- `ext_base`: two objects of level b with the same level-a members are equal, provided one of them has a level-a member;
- `inf_base`: level a is infinite.

An object of level b that is not a code, and the code of the empty set, have no members of level a. These are the urelements. Nothing requires L_b to be the power set of L_a, which is why the construction gives NFU and not NF.

**Generic points** (`ConNF/NF/Generic.lean`, 384 lines, Mathlib only; written earlier in this project). A point is a pair (v, D) with v a ℤ-indexed sequence of natural numbers; D is not used here. `genW` is an ultrafilter on points, defined by iterating a nonprincipal ultrafilter on ℕ over the coordinates in increasing order. Two properties are used: a predicate that depends on finitely many coordinates holds almost everywhere iff its shift does (`ev_sh`), and v_i < v_j almost everywhere for i < j (`ev_lt`). Jensen's argument has two parts: a variant of Specker's theorem, by which a model of type theory with atoms that admits a type-shifting automorphism yields a model of NFU, and the construction of such a model. Here the shift invariance of `genW` supplies the symmetry, and the model of NFU is built in one step.

**Pre-elements** (`PreE`). Functions from points to C that depend on finitely many coordinates. The shift of F by m is p ↦ F(v shifted by m, D). F *has level index k* if the level of F(p) is v_k almost everywhere; shifting by m moves level index k to k + m (`IsLev_shift`).

**The model** (`V`, `memV`). V is the set of pre-elements of level index 0, up to equality almost everywhere. x ∈ y means that almost everywhere x(p) E y′(p), where y′ is y shifted by 1. By shift invariance this is the same as: x shifted by m is almost everywhere a member of y shifted by m + 1, for any m (`mem₀_iff`).

**Łoś's theorem** (`los`). Let φ be stratified with free variables of types t₁, …, tₙ. Then φ holds in V at x₁, …, xₙ iff, for almost every p, φ holds in the base at the values at p of xᵢ shifted by tᵢ, with each quantifier of type t ranging over the level v_t. The proof is by induction on φ. Stratification is used only at x ∈ y, where the types are t and t + 1 and the claim is `mem₀_iff`. Negation uses that `genW` is an ultrafilter. The quantifier uses a lemma on witnesses (`exists_wit`): if R(p, a) depends on finitely many coordinates of p, there is a pre-element w with R(p, w(p)) wherever some a has R(p, a). The witness is chosen pointwise by `Classical.epsilon`, so it has the support of R.

**The axioms.**
- *Comprehension* (`comp_V`). Given φ stratified with its first variable of type t, take at each p an object of level v_{t+1} whose members of level v_t are the a at which φ holds in the base (`comp_base`, since v_t < v_{t+1} almost everywhere). This has level index t + 1; shift it down to index 0 and apply Łoś's theorem.
- *Extensionality for objects with members* (`ext_V`). If x and y are not equal almost everywhere and x has a member, then by `ext_base` almost everywhere some object of level v₀ is a member of exactly one of the two shifts. A witness for that is an element of V in exactly one of x and y.
- *Infinity* (`inf_V`). F is, at each p, an object of level v₂ whose members of level v₁ are the objects with finitely many members of level v₀. An object without members is in F; adjoining one element keeps the members finite; an object with every object as a member has all of level v₀ as members, and level v₀ is infinite. Each of the three clauses is transferred to V with a witness.

**From the structure to the theory** (`NFUConsistent.lean`). `exists_tfm` gives, for a stratified formula of `ℒₛₑₜ`, a `TFm` with the same meaning and a stratification. It is `exists_fm` of §2 with the names changed. Then `models_nfui_of_isNFU` checks the axioms of `𝗡𝗙𝗨𝗜` one by one, and Foundation's `consistent_of_model` gives the consistency.

### 11.3 What the two consistency theorems depend on

Counted by a Lean command that follows the constants a theorem depends on and groups them by defining module (`check/ModuleCensus.lean` in the tarball):

| Theorem | Constants | From `ConNF` modules outside `ConNF/NF/` | From `ConNF/NF/*.lean` (ours) |
|---|---|---|---|
| `Jensen.consistent_nfuInfinity` | 8,504 | 0 | 78, all in `Generic` |
| `consistent_nf_of_jensen` | 15,980 | 0 | 1,842, in `Generic`, `Hailperin`, `NFModel`, `NFUArith`, `NFUConstr`, `NFUCut`, `NFUHartogs`, `NFULadder`, `NFUSat`, `NFUSound` |
| `consistent_nf` (the earlier proof) | 14,822 | 2,683, in 61 modules | 590, in `ExistsNF`, `Flat`, `Generic`, `Hailperin`, `Model`, `NFModel` |

So the development now has two proofs of `Entailment.Consistent 𝗡𝗙`. The earlier one takes con-nf's models of finite height and collapses them. The new one takes the model of this section and the interpretation `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`; no constant of con-nf's construction occurs in it. It does depend on `Host.lean`, `HostTerm.lean`, `NFUTerm.lean` and `NFUInterpretsNF.lean`, which is where the interpretation is proved.

The proof of `Consistent 𝗡𝗙𝗨𝗜` needs four files, 1,601 lines: `Generic.lean` (384), `NFTheories.lean` (315), `NFUJensenModel.lean` (673), `NFUConsistent.lean` (229), with Mathlib and Foundation. The tarball has them as a lake project of their own (`nfu-consistent/`) that does not require con-nf.

### 11.4 Checks

- `lake build` of the main project with the three files added: 9,208 jobs, no errors. The job count rose from 3,299 because `NFUJensenModel.lean` imports all of Mathlib.
- `lake build` of `nfu-consistent/` in the distribution layout: 9,118 jobs, no errors.
- `leanchecker` on `NFUJensenModel`, `NFUConsistent`, `NFConsistentViaNFU`: exit status 0, no output.
- nanoda on the export of `Jensen.consistent_nfuInfinity` and `JensenNFU.exists_model`: 8,506 declarations, no errors. On the export of `consistent_nf_of_jensen`: 15,982 declarations, no errors. Axioms `propext`, `Quot.sound`, `Classical.choice` only. nanoda's counts exceed the census by two auxiliary recursors of `Lean.Syntax` that the export includes.
- `#print axioms` on the three theorems: `propext`, `Classical.choice`, `Quot.sound`.

### 11.5 What this does not show

1. Item 1 of §9 is unchanged and now carries more weight: `consistent_nf_of_jensen` says that NF is consistent only if `NFTheories.lean` states NF and NFU + Infinity correctly and Foundation's `Consistent` means consistency. The checks of this section are about proofs, not about those definitions.
2. The proof is in Lean's logic. I did not determine how much of it is needed. The objects used are iterated power sets of ℕ of finite height, an ultrafilter on ℕ, and choice.
3. It follows Jensen's idea but is not a formalisation of his paper: there is no model of type theory with atoms, no shifting automorphism and no ambiguity theorem as separate statements.
4. Infinity is `Axiom.universeInfinite`, the form used throughout these notes. Jensen also proves consistency with Choice; that is not done here.

## 12. Building without con-nf (added 16 November, 00:05)

Section 11.3 showed that no constant of con-nf's construction occurs in `consistent_nf_of_jensen`. One import still tied the files to con-nf: `ConNF/NF/Hailperin.lean` imported `ConNF/NF/Model.lean` for the definition of `NFModel`, and `Model.lean` imports con-nf, because it builds an `NFModel` from con-nf's models. That tie is now cut.

**What moved.**

| Declaration | From | To |
|---|---|---|
| `NFData`, `NFData.op`, `NFModel` (the 27-line definition), and the two checks `NFModel.exists_univ`, `NFModel.exists_memRel` | `ConNF/NF/Model.lean` | new file `ConNF/NF/NFModel.lean` (106 lines, imports only Mathlib) |
| `ConNF.NF.exists_nf` (NF has a model, from con-nf's models) | `ConNF/NF/Hailperin.lean` | new file `ConNF/NF/ExistsNF.lean` (26 lines; imports `Model` and `Hailperin`) |
| `consistent_nf`, `consistent_nfui` | `NFInterpretations.lean` | new file `NFConsistentViaConNF.lean` (34 lines) |
| `consistent_nfuInfinity` (the proof through `consistent_nf`) | `NFUJensen.lean` | `NFConsistentViaConNF.lean` |

No statement or proof was changed. `Hailperin.lean` now imports `NFModel.lean` and nothing else. `NFModel.lean` imports the same 28 Mathlib modules that reached the dependent files through con-nf before, so those files compile unchanged. `Tangle.lean` got one more import line (`Model`), which it used to receive through `Hailperin`.

After the move, the files of ours that need con-nf are `NFConsistentViaConNF.lean` and, in `ConNF/NF/`, the four files `Flat`, `Model`, `ExistsNF` and `Tangle`. (`Crabbe` and `MainLemma` import only Mathlib, but no theorem of §0 uses them; they belong to the original plan and are not in the project of this section.) Line counts in §0 change accordingly: `NFInterpretations.lean` 1,196, `NFUJensen.lean` 734.

**The project without con-nf.** The directory `standalone/` of the tarball is a lake project that requires only the Foundation wrapper, and through it Mathlib. It contains copies of 25 files, 49,167 lines:

- ten files under `ConNF/NF/`: `Generic`, `NFModel`, `Hailperin`, `NFUCut`, `NFUArith`, `NFULadder`, `NFUSat`, `NFUSound`, `NFUHartogs`, `NFUConstr`. The directory name is kept so that module names do not change; none of them imports con-nf.
- fifteen files at the top: `Host`, `HostTerm`, `NFUTerm`, `NFUInterpretsNF`, `NFSpecker`, `MutualInterpretability`, `NFChoiceForms`, `NFTheories`, `NFUInterpretsNFEq`, `NFInterpretations`, `NFUShift`, `NFUJensen`, `NFUJensenModel`, `NFUConsistent`, `NFConsistentViaNFU`.

It proves everything in §0 except the three theorems that moved to `NFConsistentViaConNF.lean`: the interpretations in both directions, `𝗡𝗙 ⊢ ∼Axiom.choice`, `𝗡𝗙 ⊢ Axiom.universeInfinite`, `Jensen.consistent_nfuInfinity` and `consistent_nf_of_jensen`.

**Checks.**

- **Main project** (`lake build`, with con-nf): 9,211 jobs, no errors. `ConNF.NF.Tangle` and `ConNF.NF.ExistsNF` were built as well. The same in the distribution layout.
- **`standalone/`** (`lake build`, in the distribution layout, from an empty build directory): 9,142 jobs, no errors, about 7 minutes with Mathlib and Foundation already compiled. The build directory then held the 25 compiled modules and nothing else of ours, and the lake workspace has no con-nf package.
- **Axioms** (`#print axioms` inside `standalone/`): `propext`, `Classical.choice`, `Quot.sound` for `nfuMutualNF`, `consistent_nf_of_jensen`, `Jensen.consistent_nfuInfinity`, `nf_provable_not_choice`, `nf_provable_universeInfinite`.
- **Module census** inside `standalone/`: the same counts as in §11.3 (8,504 and 15,980 constants), with `NFModel` in place of `Model`; `nfuMutualNF` depends on 15,140 constants.
- **`leanchecker`**: each of the 25 modules of `standalone/`, and each of the 16 modules of the main project that were recompiled: exit status 0, no output.
- **nanoda**, on an export made from `standalone/` of `consistent_nf_of_jensen`, `nfuMutualNF`, `nfu_provable_translate_of_nf`, `nf_provable_not_choice`, `nf_provable_universeInfinite`, `Jensen.consistent_nfuInfinity`: 16,093 declarations, no errors, the same three axioms.
- **`con-nf.patch`** was regenerated (18 new files, 13 modified). Applied to a fresh clone at the upstream commit it reproduces the `ConNF/` directory that was built, file for file.

**Not done.** The two nanoda runs of §8 (the twelve main theorems; the consistency theorems through con-nf) were not repeated after the move. The modules they cover were recompiled and passed `leanchecker`. The ten files keep the module prefix `ConNF.NF`; renaming them would touch every import. `NFUJensenModel.lean` still imports all of Mathlib.

## Sources

- [Foundation: Formalizing mathematical logic in Lean 4](https://reservoir.lean-lang.org/@FormalizedFormalLogic/Foundation)
- [Zulip archive: Completeness theorem for first-order logic](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Completeness.20theorem.20for.20first-order.20logic.html)
- [Mathlib.ModelTheory.Satisfiability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Satisfiability)
- [nanoda_lib](https://github.com/ammkrn/nanoda_lib)
- [R. B. Jensen, On the consistency of a slight (?) modification of Quine's New Foundations, Synthese 19 (1968/69), 250–263](https://link.springer.com/doi/10.1007/BF00568059)
- [M. R. Holmes, NF is consistent (arXiv:1503.01406v1), introduction: Jensen's use of Specker's technique for NFU](https://arxiv.org/pdf/1503.01406v1)
