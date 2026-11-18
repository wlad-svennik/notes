# From Mac Lane set theory without Choice to NFU + Infinity, through type theory

17 November 2026. Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Foundation `fbcfee52`.

## 0. Result

```lean
instance mInterpretsTSTI : 𝗠 ⊳ 𝗧𝗦𝗧𝗜                                   -- MInterpretsTST.lean

theorem TST.exists_nfui_model                                          -- TSTJensen.lean
    {M : Type} [Tarski.Structure ℒₜₛₜ M] [Tarski.Structure.Eq ℒₜₛₜ M] [Nonempty M]
    [M↓[ℒₜₛₜ] ⊧* 𝗧𝗦𝗧𝗜] :
    ∃ (N : Type) (_ : SetStructure N) (_ : Nonempty N), N↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 ∧
      ∀ φ : TFm, TFm.Strat [] φ → TFm.Sat (fun a b : N => a ∈ b) φ [] →
        ∃ ℓ : ℕ → ℕ, StrictMono ℓ ∧ ∀ v : ℕ → M, Holds (skip ℓ [] φ) v

theorem exists_nfui_model_of_m ...                                     -- MacNFU.lean
theorem consistent_m_iff_consistent_nfui : Consistent 𝗠 ↔ Consistent 𝗡𝗙𝗨𝗜
theorem consistent_m_iff_consistent_nf   : Consistent 𝗠 ↔ Consistent 𝗡𝗙
```

- **`𝗠 ⊳ 𝗧𝗦𝗧𝗜`** is an interpretation in the same sense as `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙` and `𝗡𝗙 ⊳ 𝗠`.
- **`TST.exists_nfui_model`** is Jensen's step. It is not an interpretation. From any model `M` of `𝗧𝗦𝗧𝗜` it gives a model `N` of `𝗡𝗙𝗨𝗜`. The last clause ties `N` to `M`: every well typed sentence true in `N` is true in `M` when read along some increasing sequence of levels (§3.4).
- **`exists_nfui_model_of_m`** is the composition: from any model of `𝗠`, a model of `𝗡𝗙𝗨𝗜`, tied to the sets Pⁿ(ω) of the given model.

Seven files, 2,425 lines, no `sorry`. The theorems above depend on `propext`, `Classical.choice`, `Quot.sound` only.

| File | Lines | Content | Uses |
|---|---|---|---|
| `TFmExtra.lean` | 192 | typed satisfaction; `infFm k`: "type k is not finite" | `NFUJensenModel` (for `TFm`) |
| `TSTTheories.lean` | 335 | the language `ℒₜₛₜ`, the theory `𝗧𝗦𝗧𝗜`, what its axioms mean in a model | `NFTheories`, `TFmExtra` |
| `JensenGeneric.lean` | 560 | Jensen's model over an arbitrary base | `TFmExtra`; Mathlib only |
| `TSTJensen.lean` | 507 | a model of `𝗧𝗦𝗧𝗜` is a base; `TST.exists_nfui_model` | the three above, `NFUConsistent` |
| `MDefs.lean` | 253 | bounded formulas with their meaning; separation inside a model of `𝗠` | `MacModel` |
| `MInterpretsTST.lean` | 484 | ω, Pⁿ(ω), finite ordinals, `𝗠 ⊳ 𝗧𝗦𝗧𝗜` | `MDefs`, `TSTTheories` |
| `MacNFU.lean` | 94 | composition and the consistency statements | all, `NFInterpretsMac` |

## 1. What the consistency statements do and do not say

Lean proves `Consistent 𝗡𝗙𝗨𝗜` outright (`Jensen.consistent_nfuInfinity`, from the iterated power sets of ℕ in Lean's own logic). So `Consistent 𝗠 → Consistent 𝗡𝗙𝗨𝗜` is true in Lean for a trivial reason, and the statement alone carries no information. The same holds for the two equivalences.

What carries information:

- `𝗠 ⊳ 𝗧𝗦𝗧𝗜`, which is a statement about derivations;
- `TST.exists_nfui_model` and `exists_nfui_model_of_m`, which start from an arbitrary model and tie the new model to it;
- the fact that the proofs of the consistency statements go through these and not through the outright theorem. Lean's statement cannot show that. A census of the constants each proof depends on can: `check/module_census_mac_output.txt`. None of `mInterpretsTSTI`, `TST.exists_nfui_model`, `exists_nfui_model_of_m`, `consistent_nfui_of_consistent_m`, `consistent_m_iff_consistent_nf` depends on `Jensen.consistent_nfuInfinity`, `JensenNFU.exists_model`, or the base `JensenNFU.Lvl` built from ℕ.

**Not established:** equiconsistency over a weak base theory such as PA. The proofs are in Lean's logic. `𝗠 ⊳ 𝗧𝗦𝗧𝗜` is proved through the completeness theorem, so Lean certifies that the derivations exist, not a procedure for them. Jensen's step uses an ultrafilter where Jensen used Ramsey's theorem and compactness.

## 2. `𝗧𝗦𝗧𝗜` as stated

`TSTTheories.lean`. One sort. The language `ℒₜₛₜ` has equality, membership, and a predicate `ty n` ("has type n") for each n.

**Typed formulas.** The syntax is `JensenNFU.TFm` (five constructors: `mem i j`, `eq i j`, `neg`, `and`, `all t φ`, with de Bruijn indices; the quantifier carries its type). `TFm.Strat Γ φ` says φ is well typed when its free variables have the types listed in Γ: in `x ∈ y` the type of y is one more than that of x, in `x = y` the types are equal. `TST.toFm` turns a typed formula into a formula of `ℒₜₛₜ` in which each quantifier is restricted to its type.

**Axioms.**

| Axiom | Statement |
|---|---|
| equality | the axioms of equality for `ℒₜₛₜ` |
| `extensionality n` | two objects of type n + 1 with the same members of type n are equal |
| `comprehension t Γ φ`, when `Strat (t :: Γ) φ` | for all parameters of the types Γ there is y of type t + 1 such that for all x of type t, x ∈ y ↔ φ(x, parameters) |
| `infinity` | type 0 is not finite: `infFm 0` |

`infFm k` is `Axiom.universeInfinite` with the types k, k + 1, k + 2: some family contains every object of type k + 1 without members and is closed under adjoining one element, but contains no universal set.

Points where a reader might expect something else:

- **The types are not required to be disjoint**, and nothing says that the members of an object of type n + 1 have type n. No axiom needs it: every axiom reaches objects only through quantifiers restricted to a type. Under the interpretation in `𝗠` the types do overlap (ω ⊆ P(ω)).
- **Infinity is the Tarski form** (no finite family argument reaches the universe), not "there is an injection that is not onto".
- **Comprehension has typed parameters**, as a guard on the parameters, and the instance is stated for all x of type t only.

## 3. Jensen's step: `𝗧𝗦𝗧𝗜` to `𝗡𝗙𝗨𝗜`

### 3.1 The construction over a base

`NFUJensenModel.lean` (15 November) builds a model of NFU + Infinity from the iterated power sets of ℕ. It uses that base through three facts. `JensenGeneric.lean` repeats the construction with the base as a parameter (`JBase C`): a carrier `C`, a level for each object, and a relation `E`, such that for every strictly increasing sequence of levels ℓ the structure "type t is level ℓ t, membership is E" has

| Field | Content | Change from 15 November |
|---|---|---|
| `ext_base` | extensionality for objects with members | none |
| `comp_base` | comprehension for typed formulas | was: every collection has a code |
| `inf_base` | `infFm 0` holds | was: every level is infinite, as a Lean set |

The model `V C` is as before: functions of finite support from generic points to `C`, of the level of index 0, up to equality almost everywhere. The text from `PreE` to `ext_V`, including Łoś's theorem `los`, is that of the earlier file with `C` as a parameter.

Two proofs are new.

- **`comp_V`.** At a generic point the levels of the indices below a bound K are increasing (`ev_incr`). The sequence is extended to a strictly increasing one (`monoExt`) and `comp_base` is applied to the collection defined by the formula. A witness of finite support exists by `exists_wit`, as before.
- **`inf_V`.** By Łoś's theorem the sentence `infFm 0` holds in the model iff it holds almost everywhere in the base, which is `inf_base`.

`exists_levels` is Łoś's theorem for sentences in the direction needed for the tie: a well typed sentence true in the model is true in the base along some strictly increasing ℓ.

### 3.2 A model of `𝗧𝗦𝗧𝗜` is a base

`TSTJensen.lean`. Fix a model `M` of `𝗧𝗦𝗧𝗜`.

- **Carrier**: pairs (n, x) with x of type n. The level is n.
- **Codes.** For a < b, an object y of type b is the *code* of S, of type a + 1, if y is the iterated singleton {{…{S}…}} (`Iota`). Every S has a code at each level b > a (`exists_code`), a code codes one object (`iota_inj`), and an object has one code at each level (`iota_fun`).
- **Membership**: x E y, for x of type a and y of type b > a, if y is the code of some S with x ∈ S (`SMem`). An object of type b that is not a code has no members of type a. These are the urelements.
- **Extensionality** (`ext_base'`): two codes with the same members code the same S, by extensionality in `M`.

### 3.3 Comprehension and infinity in the base

In `M`, comprehension holds for formulas only, so the relation E has to be definable.

- **`iotaF`, `smemF`**: typed formulas of `M` for `Iota` and `SMem`, by recursion on the distance between the levels, with their meaning (`holds_iotaF`, `holds_smemF`) and their typing (`strat_iotaF`, `strat_smemF`).
- **`skip ℓ Γ φ`**: a typed formula about the levels ℓ 0 < ℓ 1 < … rewritten as a typed formula of `M`. A quantifier of type t becomes one of type ℓ t; `x ∈ y` with x of type t becomes `smemF` between ℓ t and ℓ (t + 1). `strat_skip`: the result is well typed. `holds_skip`: it holds in `M` iff the original holds in the base along ℓ.
- **`comp_base'`**: comprehension in `M` for `skip ℓ (t :: Γ) φ` gives S of type ℓ t + 1; its code at level ℓ (t + 1) is the object required.
- **`inf_all`**: type k is not finite, for every k. From a family G for type k, the family for type k + 1 consists of the B whose preimage under x ↦ {x} is in G.
- **`inf_base'`**: let G be such a family for type ℓ 0. The objects of level ℓ 1 whose extension (in the sense of E) is in G form an object S, and the code of S at level ℓ 2 is the family required.

Comprehension in `M` is used for five explicit formulas (singleton, empty set, adjoining an element, and the two families above) and for `skip ℓ Γ φ`.

### 3.4 The tie

`TST.exists_nfui_model` says: if a well typed sentence φ is true in `N`, there is a strictly increasing ℓ such that `skip ℓ [] φ` holds in `M`. In words: φ is true in `M` when a variable of type t ranges over the type ℓ t and membership between consecutive types of φ is membership through codes.

The statement goes one way. It is enough to rule out a model unrelated to `M`: for example, an arithmetical sentence about the natural numbers of `N` is then true of the natural numbers of some type of `M`.

It is stated for `TFm` sentences. `NFUConsistent.exists_tfm` relates these to the stratified formulas of `ℒₛₑₜ`, but the tie is not restated for `ℒₛₑₜ` sentences.

## 4. `𝗠` interprets `𝗧𝗦𝗧𝗜`

`MDefs.lean`, `MInterpretsTST.lean`. Type n is Pⁿ(ω); membership is membership; equality is equality; the domain is everything. The translation has no parameters.

- **Using bounded separation.** `BDef R` is a bounded formula together with the relation it defines in every structure, built by combinators (`mem`, `eq`, `and`, `or`, `not`, `imp`, `iff`, `ball`, `bex`, `comp`). `BDef.sep`: in a model of `𝗠`, {z ∈ a | R(z, p)} is a set.
- **ω.** `IndR J`: J has a member without members and, with each x, a member x ∪ {x}. `NatR x`: x belongs to every inductive set. In a model of `𝗠` these x form a set (`exists_omega`): separate from an inductive set I, with P(I) as a parameter.
- **Levels.** `lvl 0` is ω and `lvl (n + 1)` is the power set of `lvl n`. The formula for "has type n" is `(tyF' n).φ`: there is p with `IsLvl n p` and x ∈ p, where `IsLvl` is defined by recursion on n.
- **Extensionality** (`ty_ext`): from extensionality in the model.
- **Comprehension** (`ty_comp`): `toBdd` turns a typed formula into a bounded formula with the levels as parameters; then bounded separation.
- **Infinity** (`ty_inf`): the family of the subsets of ω that are included in a member of ω. It does not contain ω, by foundation. It is closed under adjoining one element by three facts, each proved by induction on ω (`nat_induction`):

| Lemma | Statement, for n, b in ω |
|---|---|
| `nat_trans` | the members of members of n are members of n |
| `nat_D` | n ⊆ b → n = b ∨ n ∈ b |
| `nat_C` | b ∈ n ∨ n ⊆ b |

`tstModel_models` shows that in every model of `𝗠` the interpreted structure is a model of `𝗧𝗦𝗧𝗜`; `mInterpretsTSTI` follows by the completeness theorem of the library.

## 5. Checked and not checked

Checked on 17 November 2026:

- `lake build` of `standalone/` with the seven files added, in the layout of the tarball and from an empty build directory: 9,156 jobs, no errors. The build directory then held the 38 compiled modules.
- `#print axioms` for `mInterpretsTSTI`, `TST.exists_nfui_model`, `exists_nfui_model_of_m`, `consistent_m_iff_consistent_nfui`: `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker` on each of the seven new modules: exit status 0 (`check/leanchecker_results_2026-11-17.txt`).
- nanoda on an export of `mInterpretsTSTI`, `TST.exists_nfui_model`, `exists_nfui_model_of_m`, `consistent_nfui_of_consistent_m`, `consistent_m_iff_consistent_nfui`, `consistent_m_iff_consistent_nf` with everything they depend on: 17,111 declarations, no errors, the same three axioms (`check/nanoda_mac_nfu.json`, `check/nanoda_mac_nfu_output.txt`).
- The census of §1 (`check/ModuleCensusMac.lean`, `check/module_census_mac_output.txt`).

Not checked by Lean:

- That `𝗧𝗦𝗧𝗜` as stated is the theory the literature calls TSTI (§2 lists the choices), and that `𝗠` is Mathias's M. The files to read are `TSTTheories.lean` down to `inductive TSTI`, `infFm` in `TFmExtra.lean`, `TFm` and `TFm.Strat` in `NFUJensenModel.lean`, and `MacTheories.lean`.
- Anything about Choice. `𝗧𝗦𝗧𝗜` and `𝗠` have none, and `𝗡𝗙𝗨𝗜` is NFU + Infinity without Choice.
- Equiconsistency over a weak base theory (§1).

Not run this time: the main project with con-nf. The seven files are in its directory and in its `lakefile.toml`, but only `standalone/` was built. They are the same in both places and import nothing from con-nf.
