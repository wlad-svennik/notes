# FunctionNF: interpreted in NF, and interprets NFU + Infinity

17 November 2026. Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Foundation `fbcfee52`.

## 0. Result

```lean
instance NFFn.nfInterpretsFn : 𝗡𝗙 ⊳ 𝗙𝗡𝗙          -- NFInterpretsFn.lean
instance FNF.fnInterpretsNFUI : 𝗙𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜       -- FnInterpretsNFU.lean

instance FNF.fnInterpretsNF   : 𝗙𝗡𝗙 ⊳ 𝗡𝗙         -- through 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙
instance nfuiInterpretsFn     : 𝗡𝗙𝗨𝗜 ⊳ 𝗙𝗡𝗙       -- through 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙   (FnNF.lean)
def nfInterpretsNFUIviaFn     : 𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜        -- through FunctionNF   (FnNF.lean)

theorem FNF.isNFU        : IsNFU M Mem            -- in every model M of 𝗙𝗡𝗙   (FnBool.lean)
theorem FNF.univInfinite : UnivInfinite Mem       -- in every model M of 𝗙𝗡𝗙   (FnInfinity.lean)
```

`𝗙𝗡𝗙` is FunctionNF: the stratified λ-calculus with full extensionality and without pairing (§1). So NF, FunctionNF and NFU + Infinity interpret each other. `⊳` is the same notion of interpretation as in `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙` and `𝗡𝗙 ⊳ 𝗠`: the domain is a formula, each symbol is a formula, no parameters. In both new interpretations the domain is everything and equality is equality.

Eight files, 3,475 lines, no `sorry`. The theorems above depend on `propext`, `Classical.choice`, `Quot.sound` only.

| File | Lines | Content | Uses |
|---|---|---|---|
| `FnTheory.lean` | 377 | the language `ℒλ`, λ-terms, stratification, the theory `𝗙𝗡𝗙`, what its axioms say in a model | `NFTheories`, `TFmExtra` |
| `FnBool.lean` | 651 | in a model of `𝗙𝗡𝗙`: values of λ-terms, truth-value terms, sets, comprehension, NFU | `FnTheory` |
| `FnSets.lean` | 513 | singletons, pairs, `ι"a`, `P(a)`, injections, Cantor | `FnBool` |
| `FnInfinity.lean` | 679 | the universe is not finite | `FnSets` |
| `FnInterpretsNFU.lean` | 214 | the translation; `𝗙𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜` | `FnInfinity`, `NFUJensen`, `NFUConsistent` |
| `NFFn.lean` | 460 | in a model of `𝗡𝗙`: a pair that preserves types, functions, the bijection between the universe and the functions, application | `NFMac` |
| `NFInterpretsFn.lean` | 487 | values of λ-terms in a model of `𝗡𝗙`; the translation; `𝗡𝗙 ⊳ 𝗙𝗡𝗙` | `NFFn`, `FnTheory` |
| `FnNF.lean` | 94 | compositions and consistency statements | all |

## 1. FunctionNF as stated

`FnTheory.lean`, down to `inductive FunctionNF`.

**Language `ℒλ`.** Function symbols: application `f · x` and the equality test `s ≐ t` (binary), `⊤` and `⊥` (constants). One relation symbol, equality.

**λ-terms** (`FNF.LTm`): variables, `t u`, `λx.t`, `s ≐ t`, `⊤`, `⊥`, with de Bruijn indices. They are not terms of the language, because abstraction binds a variable.

**Stratification** (`FNF.HasLev γ t ℓ`: `t` has level `ℓ` when its free variables have the levels `γ`).

| Term | Rule |
|---|---|
| variable `i` | `γ i = ℓ` |
| `t u` | `t` has level `ℓ + 1` and `u` has level `ℓ` |
| `λx.t` | `ℓ = k + 1`, and `t` has level `k` when `x` has level `k` |
| `s ≐ t` | `s` and `t` have level `ℓ` |
| `⊤`, `⊥` | every level |

**The value of a λ-term** (`FNF.Den t env v`) is a relation defined by recursion on the term. `v` is a value of `λx.t` when for every `x`, `v · x` is a value of `t`. `FNF.denF` is the formula of `ℒλ` that says this.

**Axioms.**

| Axiom | Statement |
|---|---|
| equality | the axioms of equality for `ℒλ` |
| `extensionality` | if `f · x = g · x` for all `x` then `f = g` |
| `eqtTrue` | `(a ≐ a) = ⊤` |
| `eqtFalse` | `a = b` or `(a ≐ b) = ⊥` |
| `nontrivial` | `⊤ ≠ ⊥` |
| `abstraction t`, for every stratified `t` | `t` has a value, for all values of its free variables |

Choices made in the statement, to compare with yours:

- β is not a separate axiom. It is in the meaning of "value of `λx.t`", and `abstraction` says the value exists.
- A free variable has one level in a term. `⊤` and `⊥` may have different levels at different occurrences.
- There is no pairing, no projection, no case expression, and no constant other than `⊤` and `⊥`.
- I wrote this from your description in this conversation and in the chat of 16 November. I could not fetch the C₀ report from GitHub to compare the axioms line by line.

## 2. FunctionNF interprets NFU + Infinity

Fix a model `M` of `𝗙𝗡𝗙`. A set is an object all of whose values are `⊤` or `⊥` (`IsSet`). `x ∈ s` means that `s` is a set and `s · x = ⊤` (`Mem`).

### 2.1 Truth values (`FnBool.lean`)

A stratified λ-term has exactly one value (`den_unique`, `fn_abs`), written `ev t env`. `bool p` is `⊤` if `p` holds and `⊥` otherwise. The Boolean operations are terms, as in your construction:

| Operation | Term | Level |
|---|---|---|
| not `p` | `p ≐ ⊥` | same |
| `p` iff `q` | `p ≐ q` | same |
| raise `p` | `λw.p ≐ λw.⊤` | one up |
| lower `p` | `p d ≐ ⊤ d`, where `⊤ d ≠ ⊥ d` | one down |
| `p` and `q` | `⟨p, q⟩ ≐ ⟨⊤, ⊤⟩`, with `⟨a, b⟩ = λz.λu.λv. z (λw.a) b`, lowered three times | same |
| for all `x`, `p` | `λx.p ≐ λx.⊤` | one up |

`d` exists because `⊤ ≠ ⊥` and by extensionality (`exists_sep`). The components of the pair are recovered by applying it to `λk.k` and to `λk.λm.m`.

`BT Γ R` packages a relation `R` with such a term at every level, when the variables have the levels `Γ`. The combinators `BT.mem`, `BT.eq`, `BT.app` (for `f · x = y`), `BT.not`, `BT.and`, `BT.or`, `BT.imp`, `BT.iff`, `BT.all`, `BT.ex`, `BT.comp` build the relation, the terms and the two proofs together. After this file no λ-term is written by hand.

- **Comprehension** (`BT.set`): a relation with a `BT` defines a set, for all values of the parameters. The set is `λx.p`.
- **Extensionality** (`set_ext`): sets with the same members are equal. Objects that are not sets have no members, so they are the urelements.
- **NFU** (`isNFU`): `(M, Mem)` satisfies extensionality for objects with members and comprehension for every stratified formula of set theory (`ofTFm` turns a typed formula into a `BT`).

### 2.2 Injections (`FnSets.lean`)

`ι"a` is the set of singletons of members of `a` (`simg`), `P(a)` the set of sets included in `a` (`pow`). `a ≼ b` means there is an injection, as a set of Kuratowski pairs (`Le`). `a ~ b` means `a ≼ b` and `b ≼ a` (`Eqv`); the Schröder–Bernstein theorem is not needed.

| Lemma | Statement |
|---|---|
| `le_of_rel` | a relation with a `BT` that is total on `a`, single-valued and one-to-one gives `a ≼ b` |
| `le_simg`, `le_of_simg` | `a ≼ b` iff `ι"a ≼ ι"b` |
| `le_pow` | `a ≼ b` implies `P(a) ≼ P(b)` |
| `simg_pow_le`, `pow_simg_le` | `ι"P(a) ~ P(ι"a)` |
| `le_simg_ex` | `a ≼ ι"z` implies `a ~ ι"y` for some `y` |
| `cantor` | not `P(y) ≼ ι"y` |

### 2.3 Infinity (`FnInfinity.lean`)

The axiom of infinity of `𝗡𝗙𝗨𝗜` says: some family contains every object without members and is closed under adjoining one element, but contains no universal set (`UnivInfinite`). The proof is by contradiction and follows Specker's proof that NF refutes Choice, with one change. NF has `P(V) ⊆ V`. FunctionNF has that too (sets are objects), and it has a bound in the other direction: every object is a function, and a function is determined by its graph.

**Definitions.**

- `Ex b a`: there is `y` with `b ~ ι"y` and `a ~ P(y)`. This says `a` is 2 to the power `b`, at the type of `b`.
- `Tw i a`, for `i` in `Fin 5`: `a` is in the tower 2, 2², 2^2², …, at a position congruent to `i` modulo 5. It is the least family of five sets such that the sets with exactly two elements are in the first, and `Ex b a` moves from one to the next.

**Lemmas on the tower.** None of them uses that the universe is finite.

| Lemma | Statement |
|---|---|
| `tw_ind` | induction on the tower, for a property with a `BT` |
| `tw_inv` | a tower term has two elements, or is `Ex` of the tower term before it |
| `tw_simg` | if `a` is a tower term then `ι"a` is one, at the same position |
| `tw_D` | for tower terms `κ`, `μ`: `μ ≼ κ`, or `e ≼ μ` for some `e` with `Ex κ e` |
| `tw_res` | tower terms with `a ~ a'` are at the same position modulo 5 |

`tw_res` uses `tw_D` and Cantor's theorem: if `2^b ~ 2^b'` for tower terms `b`, `b'`, then `b ~ b'`.

**If the universe is finite.**

| Lemma | Statement |
|---|---|
| `fin_ind` | a property with a `BT` that holds of the objects without members and is preserved by adjoining one element holds of every object |
| `comparable` | `a ≼ b` or `b ≼ a`, for all `a`, `b` |
| `exists_top` | below any `ι"z` with at least two members the tower has a last term: a tower term `τ ≼ ι"z` such that no `e` with `Ex τ e` has `e ≼ ι"z` |

`exists_top` uses `surgery`: an injection of `P(y)` into `s ∪ {b}` gives an injection of `ι"y` into `s`, by sending the one singleton that goes to `b` to the image of the empty set.

**The two bounds.** Let `w = ι"ι"V`.

| Lemma | Statement | Reason |
|---|---|---|
| `lemA` | `P(w) ≼ w` | `P(ι"ι"V) ~ ι"ι"P(V)` and `P(V) ⊆ V` |
| `lemB` | `w ≼ P(P(P(V)))` | `{{f}}` goes to the graph of `f`, a set of Kuratowski pairs; one-to-one by extensionality |

`lemB` is the only place where application enters a formula of set theory (`BT.app`).

**The contradiction** (`univInfinite`). Let `τ` be the last tower term below `w`, at position `c`.

1. `τ ≼ w`, so `τ ~ ι"y` for some `y`, and `P(y)` is not `≼ w`.
2. `P(τ)` is a tower term at position `c + 1`, and `P(τ) ≼ P(w) ≼ w`. By `tw_D` and the choice of `τ`, `P(τ) ≼ τ`.
3. `P(τ) ≼ ι"w` would give `P(y) ≼ w`. So `ι"w ≼ P(τ)` by `comparable`. Now `ι"w = ι³"V`.
4. From 3 and `lemB`: `ι³"τ ≼ ι³"w ≼ ι³"P³(V) ≼ P⁴(τ)`.
5. Let `B = ι³"τ` (position `c`) and `A = ι³"P(τ)` (position `c + 1`). The next tower terms after `A` are `P(ι²"Pτ)`, `P(ι"P²τ)`, `P⁴(τ)`, at positions `c + 2`, `c + 3`, `c + 4`.
6. `A ≼ B` by 2 and `B ≼ P⁴(τ)` by 4. By `tw_D` three times, `B` is equinumerous with one of these four terms. By `tw_res`, `c` equals `c + k` modulo 5 for some `k` from 1 to 4.

The modulus is 5 because the graph of a function is three power sets above its arguments with Kuratowski pairs. No arithmetic on cardinals is used.

### 2.4 The interpretation (`FnInterpretsNFU.lean`)

The membership formula is "for all `z`, `y · z = ⊤` or `y · z = ⊥`; and `y · x = ⊤`" (`memφ`). In a model `M` of `𝗙𝗡𝗙` the interpreted structure is `(M, Mem)`, a model of `𝗡𝗙𝗨𝗜` by §2.1 and §2.3 (`nfuModel_models`). `fnInterpretsNFUI` follows by the completeness theorem of the library.

## 3. NF interprets FunctionNF

Fix a model `V` of `𝗡𝗙`. The aim is a relation `AppR f x y` that is stratified with `f` one type above `x` and `y`, total and single-valued, extensional, and such that every definable function is `AppR f` for some `f`.

### 3.1 The construction (`NFFn.lean`)

| Step | Definition | Types |
|---|---|---|
| `Sg x y` | `y = σ(x)`: the successor of `x` if `x` is a finite ordinal (`Hin.InOm` of `NFMac.lean`), and `x` otherwise | `x`, `y` at 6 |
| `Pr p x y` | Quine's pair: `p = {σ"a : a ∈ x} ∪ {σ"b ∪ {0} : b ∈ y}` | `p`, `x`, `y` at 8 |
| `Fn F` | `F` is a set of pairs, total and single-valued | `F` at 9 |
| `Chi s F` | `F` is the characteristic function of `s`, with values `V` and `∅` | `s`, `F` at 9 |
| `InC x` | `x` is in the closure of the set of non-functions under `Chi` | `x` at 9 |
| `J f F` | `F = Chi(f)` if `InC f`, and `F = f` otherwise | `f`, `F` at 9 |
| `AppR f x y` | the pair of `x` and `y` is in `J(f)` | `f` at 9, `x`, `y` at 8 |

- `σ` is one-to-one, preserves types and misses zero (`sg_inj`, `sg_ne_zero`). That the finite ordinals are closed under successor is `Hin.om_succ_exists`, which uses `𝗡𝗙 ⊢ Axiom.universeInfinite`, that is, Specker's theorem. That successor is one-to-one uses foundation for the types (`ee_wf`).
- The pair has the type of its components, and determines them (`pr_inj`).
- `Chi` is a one-to-one map of the universe into the set of functions (`chi_inj`), and the set of functions is included in the universe. `J` is the bijection from the proof of the Cantor–Schröder–Bernstein theorem: `j_fn`, `j_fun`, `j_inj`, `j_surj`. `inC_inv` is the step that uses the least closed set.
- `app_total`, `app_fun`; `app_ext` (extensionality); `app_of_graph` (a set of pairs given by a total single-valued relation is the graph of `AppR f` for some `f`).

### 3.2 Values of λ-terms (`NFInterpretsFn.lean`)

`DenV t env v` is the value relation of §1 computed with `AppR`, with `⊤` the universal set and `⊥` the empty set, and `a ≐ b` equal to `⊤` or `⊥` according to whether `a = b`.

- `NDef γ R` is a stratified definition whose variables are indexed by ℕ, as the free variables of a λ-term are. `NDef.comprehension` is comprehension in `V` for it.
- `denN`: if `t` has level `ℓ` with free variables at levels `γ`, then `DenV t` has a stratified definition with the value at type `ℓ + 8` and the variables at types `γ i + 8`. The 8 is the type of a pair. The rules of §1 are what makes this work: in `t u` the function is one type above the argument and the result, as `f` is in `AppR f x y`.
- `denV_fun`: at most one value. `denV_exists`: a stratified λ-term has a value. For `λx.t` the set of the pairs `(x, value of t)` exists by comprehension, and `app_of_graph` gives the value.

### 3.3 The interpretation

`fnTranslation`: the domain is everything; equality is equality; `f · x = y` is `AppR f x y`; `(a ≐ b) = y` is `EqtR a b y`; `y = ⊤` is "`y` is the universal set"; `y = ⊥` is "`y` is empty". In a model `V` of `𝗡𝗙` the interpreted structure satisfies the five properties of `FNF.models_of` (`fnModel_models`). `nfInterpretsFn` follows by the completeness theorem of the library.

## 4. What the consistency statements do and do not say

`FnNF.lean` has `consistent_fn_iff_consistent_nf`, `consistent_fn_iff_consistent_nfui` and `consistent_fn : Consistent 𝗙𝗡𝗙`.

Lean proves `Consistent 𝗡𝗙𝗨𝗜` outright (`Jensen.consistent_nfuInfinity`, Jensen's model built in Lean's own logic). So `consistent_fn` is a theorem, and the two equivalences are true for a trivial reason. What `consistent_fn` gives is that the interpretations are not vacuous: `𝗙𝗡𝗙` has a model. What carries the information is the interpretations of §0, which are statements about derivations.

**Not established:** anything over a weak base theory. Both interpretations are proved through the completeness theorem, so Lean certifies that the derivations exist, not a procedure for them.

## 5. Checked and not checked

Checked on 17 November 2026:

- `lake build` of `standalone/` with the eight files added, in the layout of the tarball and from an empty build directory: 9,164 jobs, no errors. The build directory then held the 46 compiled modules.
- `#print axioms` for `nfInterpretsFn`, `fnInterpretsNFUI`, `fnInterpretsNF`, `nfuiInterpretsFn`, `nfInterpretsNFUIviaFn`, `univInfinite`, `isNFU`, `consistent_fn`: `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker` on each of the eight new modules: exit status 0 (`check/leanchecker_results_fn_2026-11-17.txt`).
- nanoda on an export of `nfInterpretsFn`, `fnInterpretsNFUI`, `fnInterpretsNF`, `nfuiInterpretsFn`, `nfInterpretsNFUIviaFn`, `univInfinite`, `isNFU`, `consistent_fn` with everything they depend on: 17,026 declarations, no errors, the same three axioms (`check/nanoda_fn.json`, `check/nanoda_fn_output.txt`).
- A census of the constants each proof depends on (`check/ModuleCensusFn.lean`, `check/module_census_fn_output.txt`): `fnInterpretsNFUI` depends on the five `Fn` files before it, on `NFTheories`, and on the definitions of typed formulas, `IsNFU` and `UnivInfinite` with the lemma that a structure with these two properties is a model of `𝗡𝗙𝗨𝗜`; it does not depend on Specker's theorem for NF or on Jensen's model. `univInfinite` depends on `FnTheory`, `FnBool`, `FnSets`, `FnInfinity` and three definitions. `nfInterpretsFn` depends on Specker's theorem (`nf_provable_universeInfinite`) and not on Jensen's model or on `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. Of the eight, only `consistent_fn` depends on `Jensen.consistent_nfuInfinity`.

Not checked by Lean:

- That `𝗙𝗡𝗙` as stated is the theory you mean (§1 lists the choices). The file to read is `FnTheory.lean` down to `inductive FunctionNF`: 200 lines.
- That `𝗡𝗙` and `𝗡𝗙𝗨𝗜` are the theories of the literature; these are the statements of `NFTheories.lean`, unchanged.
- Anything about Choice, or about FunctionNF with pairing, or about C₀ (FunctionNF with `⊤ = 𝐁`).

Not run this time: the main project with con-nf. The eight files are in its directory and in its `lakefile.toml`, but only `standalone/` was built. They are the same in both places and import nothing from con-nf.
