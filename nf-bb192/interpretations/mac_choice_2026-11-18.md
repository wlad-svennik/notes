# NF interprets Mac Lane set theory with Choice

18 November 2026. Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Foundation `fbcfee52`. This note continues `nf_interprets_mac_2026-11-17.md`, which gave `𝗡𝗙 ⊳ 𝗠` (no choice).

## 0. Result

```lean
instance nfInterpretsMH   : 𝗡𝗙 ⊳ 𝗠𝗛         -- NFInterpretsMH.lean
instance mhInterpretsMAC  : 𝗠𝗛 ⊳ 𝗠𝗔𝗖        -- MHInterpretsMAC.lean

instance nfInterpretsMAC  : 𝗡𝗙 ⊳ 𝗠𝗔𝗖        -- composition
instance nfuInterpretsMAC : 𝗡𝗙𝗨𝗜 ⊳ 𝗠𝗔𝗖      -- through 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙
```

```
𝗡𝗙𝗨𝗜  ⊳  𝗡𝗙  ⊳  𝗠𝗛  ⊳  𝗠𝗔𝗖
              │        │
              │        └─ the constructible sets; ∈ and = unchanged
              └─ types of well-founded pointed graphs (the model of 17 November)
```

- `𝗠` is Mathias's theory: extensionality, empty set, pairing, union, power set, infinity, foundation, separation for bounded formulas, transitive containment. No choice.
- `𝗠𝗔𝗖` is `𝗠` with the library's axiom of choice: every family of pairwise disjoint sets with members has a set that meets each of them in exactly one point.
- `𝗠𝗛` is `𝗠` with the collapse axiom of §1. It is the intermediate theory. It has no choice.

Thirteen files, 6,717 lines, no `sorry`. The four interpretations depend on `propext`, `Classical.choice`, `Quot.sound` only.

| File | Lines | Content |
|---|---|---|
| `MHTheory.lean` | 204 | the collapse axiom and the theory `𝗠𝗛` |
| `NFInterpretsMH.lean` | 471 | the model of 17 November satisfies the collapse axiom; `𝗡𝗙 ⊳ 𝗠𝗛` |
| `MHBasics.lean` | 363 | inside a model of `𝗠`: pairs, products, relations as sets, ordinals, `ω` |
| `MHRec.lean` | 529 | recursion along an ordinal; a limit ordinal above any ordinal |
| `MHLevels.lean` | 410 | the eight operations, the clause that defines the levels and their order |
| `MHCodes.lean` | 396 | tree codes: labelled trees with four subtrees at each node, as sets |
| `MHExist.lean` | 642 | the levels exist along every ordinal: `Lev γ`, `LtS γ` |
| `MHOrder.lean` | 459 | every level is well-ordered: `wol` |
| `MHSep.lean` | 842 | definable subsets of a constructible set are constructible: `sep_good` |
| `MHHull.lean` | 437 | hulls; the collapse axiom passes to images: `hull_exists`, `hcat_image` |
| `MHCond.lean` | 1,389 | condensation: the bound for the subsets of a level, `bound_exists` |
| `MHInterpretsMAC.lean` | 532 | the constructible sets form a model of `𝗠𝗔𝗖`; the interpretations |
| `MacChoiceAll.lean` | 43 | consistency statements |

Why there is an intermediate theory. NF refutes choice, so choice cannot be inherited from NF. It is obtained inside, in the constructible sets, where it costs almost nothing. What costs is power set in the constructible sets, and `𝗠` alone is not enough for the argument I know: one needs a bound on where the constructible subsets of a level appear. The collapse axiom supplies that bound, and the NF model of 17 November satisfies it.

## 1. The collapse axiom (`MHTheory.lean`)

> For every set `u` there is a transitive set `T` such that every well-founded relation `r` on `u` has a collapse into `T`: a function `F` from `u` to `T` with `F(b) = {F(a) : a ∈ u, a r b}` for every `b ∈ u`.

- `r` is a set of pairs. Well-founded on `u` means: every subset of `u` with a member has a member with no `r`-predecessor in the subset.
- `r` is not assumed extensional, so `F` need not be one-to-one.
- `T` depends on `u` only. That is the content: all the collapses of all the well-founded relations on one set lie in one set.

In Lean: `MH.HCat T u`, `MH.HC V`, `Axiom.collapse`, `𝗠𝗛`.

The axiom is in the spirit of Mathias's axiom H (for every `u` there is a transitive set that includes every transitive set of size at most that of `u`). **The equivalence with H over `𝗠` is not formalised**, and I did not check Mathias's wording of H against the paper for this note.

## 2. NF interprets `𝗠𝗛` (`NFInterpretsMH.lean`)

The translation is the one of 17 November: the domain is the types of well-founded pointed graphs that belong to a stable transitive set. Only the collapse axiom is new.

Let `u` be a set of the model and `X` a stable transitive set that contains it. The members of `u` are types, and `θ` maps `X` onto itself, so there is a set `U⁻` of the `x ∈ X` with `θ x ∈ u`.

| Step | Statement | Lean |
|---|---|---|
| bound | `T` is the set of the types of all well-founded pointed graphs on `U⁻`; it is stable and transitive | `typeOn_stable` |
| collapse | pull `r` back along `θ` to a graph `ρ` on `U⁻`; send `θ x` to the type of `(ρ, x)` | `theta_type` |
| the collapse is a set of the model | `θ x` and the type of a graph pointed at `x` have the same level in the sense of stratification | `hc_of_embed` |

## 3. `𝗠𝗛` interprets `𝗠𝗔𝗖`: the constructible sets

Work inside a model `V` of `𝗠𝗛`. `V` has separation for bounded formulas only, and no replacement. Two consequences shape everything below:

- An induction along the ordinals is legitimate only for a statement with a bounded definition, so that the counterexamples form a set. Each induction below has such a definition written out (`BDef`).
- A recursion along an ordinal needs all its values inside one set given in advance (`ord_rec`).

### 3.1 The levels (`MHLevels.lean`)

A level is a set `A` with an order `lt` on it. One step is

```
Def(A, lt) = {A} ∪ { {z ∈ A | Φ(lt; z, s, y₁, y₂, y₃)} : s, y₁, y₂, y₃ ∈ A }
```

and the level at `γ` is the union of `Def` of the levels at `β < γ`. `Φ` is a fixed bounded formula. The parameter `s` is a numeral that selects one of eight operations:

| `s` | The set `{z ∈ A | …}` | Used for |
|---|---|---|
| 0 | `z ∈ y₁` or `z = y₂` | `y₁ ∪ {y₂}`: pairs, numerals, finite functions |
| 1 | `z ∈ y₁` and `z ∉ y₂` | difference; complement, intersection |
| 2 | `z` is a function from `y₁` to `y₂` | all valuations of `n` variables in a set |
| 3 | `z ∈ y₁` and `z(y₂) ∈ z(y₃)` | the valuations with `xᵢ ∈ xⱼ` |
| 4 | `z ∈ y₁` and `z(y₂) = z(y₃)` | the valuations with `xᵢ = xⱼ` |
| 5 | `z ∈ y₁` and some `e ∈ y₂` agrees with `z` off `y₃` | the quantifier `∃xⱼ` |
| 6 | some `e ∈ y₁` has value `z` at `y₃` and agrees with `y₂` off `y₃` | from valuations back to a subset |
| 7 | `z ∈ lt` | the order of the level, as a member of a later level |

There are no coded formulas and no truth definition. Operations 0 to 6 use `∈` only; operation 7 is the only one that uses the order.

The order of the level at `γ` compares two sets first by the stage at which they appear; at the same stage `β` the level at `β` itself comes first; then by their least definitions `(s, y₁, y₂, y₃)` over the level at `β`, lexicographically in the order of that level (`KeyLess`, `SameLess`, `LeastD`, `Lex4`).

### 3.2 The levels exist (`MHExist.lean`)

`exists_hier`: for every ordinal `δ` there is a sequence of the levels up to `δ`. `Lev γ` and `LtS γ` are the level at `γ` and its order.

The recursion needs one set that contains all the levels up to `δ`. This is the first use of the collapse axiom:

| Step | Statement | Lean |
|---|---|---|
| codes | a member of a level is named by a tree: the root carries the stage, the four subtrees name `s, y₁, y₂, y₃` | `MHCodes.lean` |
| evaluation | the codes are evaluated by recursion on the label of the root | `GEv` |
| every member is named | by induction on the stage | `hcoded` in `next_sub` |
| collapse | the relation "the value of `c'` is a member of the value of `c`" on the set of the codes collapses onto the level; the codes with labels up to `δ` form a set given in advance | `next_sub` |

### 3.3 Every level is well-ordered (`MHOrder.lean`)

`wol`: the order is total on `Lev γ`, and every set of members of `Lev γ` with a member has a least member. By induction on `γ`; the step takes the least stage, then the least definition (`lex4_min`). `LtL` is the order of all the constructible sets, and `lts_iff` says that `LtS γ` is `LtL` on `Lev γ`.

### 3.4 Separation (`MHSep.lean`)

`sep_good`: if `t` is constructible, then every subset of `t` that is definable in the structure `(t, ∈)` with parameters in `t` is constructible. All formulas are allowed here, since the quantifiers range over `t`.

A valuation of `n` variables in `t` is a function from the numeral `n` to `t` (`fnOf`). For a formula `φ` with `n` variables, the set of the valuations in `t` that satisfy `φ` in `(t, ∈)` is built by induction on `φ` (`sat_good`):

| `φ` | Set of valuations | Operation |
|---|---|---|
| `⊤` | all functions from `n` to `t` | 2 |
| `xᵢ ∈ xⱼ`, `xᵢ = xⱼ` | | 3, 4 |
| `¬`, `∧`, `∨` | complement, intersection, union | 1 |
| `∃x φ` | the restrictions of the valuations of `n + 1` variables that satisfy `φ` | 5 |
| `∀x φ` | as `¬∃x¬φ` | 1, 5 |

Operation 6 then fixes the parameters and returns the subset of `t`. The theorem is stated for a property `X` of sets that is closed under the operations (`Closed`), because §3.5 uses it inside a hull.

### 3.5 Power set (`MHHull.lean`, `MHCond.lean`)

`bound_exists`: for an ordinal `ν ⊇ ω` there is an ordinal `κ` such that every constructible subset of `Lev ν` is a member of `Lev κ`. Then the constructible subsets of a constructible set are members of one level, which is what power set needs.

Let `x₀ ⊆ Lev ν` be constructible, say `x₀ ∈ Lev δ′` with `δ′` a limit.

| Step | Statement | Lean |
|---|---|---|
| hull | `N ⊆ Lev δ′` contains the members of `Lev ν`, `Lev ν` and `x₀`, and is closed under: pairs; the level at which a set appears; the next level; the eight operations over a level in `N`; the components of the least definition of a set; the least member of a set | `HullData`, `exists_hull` |
| `N` is an image of a fixed set | `N` is the set of the values of tree codes whose leaves are labelled by the members of `Lev ν`, by `Lev ν`, and by one further label that stands for `x₀`; the set of these codes depends on `ν` only, not on `x₀` or `δ′` | `hull_exists` |
| one bound | if `T` is as in the collapse axiom for the set of the codes, it is as in the collapse axiom for `N` | `hcat_image` |
| collapse | `π` is the collapse of `(N, ∈)`. It is one-to-one, because two different members of `N` are separated by the least member of their difference, which is in `N` | `pi_inj`, `ext_wit` |
| `π` preserves bounded formulas | by induction on the formula; for a bounded quantifier the witnesses form a set in `N` (§3.4 inside `N`) and its least member is in `N` | `elem_form` |
| collapsed ordinals | `c` is the collapse of the ordinals `γ` with `Lev γ ∈ N`; its values are ordinals in `T` | `cc_ord`, `cc_lt` |
| **the collapsed hull is a level** | for every `γ` with `Lev γ ∈ N`: `π` maps `N ∩ Lev γ` onto `Lev (c γ)`, and it preserves the order | `main_ind`, `step` |
| `π` fixes `x₀` | `π` is the identity on `Lev ν`, and `x₀ ⊆ Lev ν` | `pi_x0` |
| bound | `x₀ = π x₀ ∈ Lev (c ρ + 1)`, with `c ρ` an ordinal in `T`; `κ` is the set of the ordinals in `T` | `bound_exists` |

The step of `main_ind`, for `ρ` below `γ` with `Lev ρ ∈ N`:

- `π` commutes with the eight operations over `Lev ρ` (`phi_pi`, `pi_isD`). For operations 0 to 6 this is `elem_form`. For operation 7 it is the preservation of the order at `ρ`, which is the induction hypothesis.
- `π` sends the set that appears at `ρ` to a set that appears at `c ρ` (`pi_rk`), and least definitions to least definitions (`pi_leastD`). Hence it preserves the order at `γ` (`sameless_pi`).

### 3.6 Choice (`ac_of_con` in `MHInterpretsMAC.lean`)

Let `𝓧 ∈ Lev γ` be a family of pairwise disjoint sets with members. Operation 7 over a level four steps above `γ` gives a constructible set `R` that contains the pair `(a, b)` exactly when `a` is before `b`, for `a, b ∈ Lev γ`. The choice set is

```
C = { z : z ∈ X for some X ∈ 𝓧, and no w ∈ X has (w, z) ∈ R }
```

It is constructible by §3.4, and it meets each `X ∈ 𝓧` in exactly its least member by §3.3.

### 3.7 The interpretation (`MHInterpretsMAC.lean`)

The domain is "`x` is a member of the last level of some sequence of levels" (`conF`), a formula with unbounded quantifiers. Membership and equality are unchanged. In a model of `𝗠𝗛` the constructible sets satisfy the conditions `IsMacBase` of 17 November (`isMacBase_of_con`) and choice (`ac_of_con`):

| Axiom | Why |
|---|---|
| extensionality, foundation | the constructible sets form a transitive class |
| pairing, transitive containment | every level is a constructible transitive set |
| infinity | `Lev ω` |
| separation | §3.4 |
| power set | §3.5 |
| choice | §3.6 |

`mhInterpretsMAC` follows by the completeness theorem of the library, and `nfInterpretsMAC` by composition with §2.

## 4. What is not established

- **That the collapse axiom is Mathias's H.** See §1.
- **That the hierarchy is Gödel's `L`.** The levels are generated by the eight operations above. I did not prove that their union is the class of the constructible sets in the usual sense, nor that the model satisfies `V = L`, the generalised continuum hypothesis, or a global well-order. What is proved is that it is a model of `𝗠𝗔𝗖`.
- **That the constructible sets satisfy the collapse axiom.** So the interpretation is of `𝗠𝗔𝗖`, not of `𝗠𝗔𝗖` with the collapse axiom.
- **Mac Lane's own form of choice.** `𝗔𝗖` here is the library's statement about families of pairwise disjoint sets. The well-ordering theorem and Zorn's lemma in `𝗠𝗔𝗖` are not derived.
- **Anything over a weak base theory.** All interpretations are proved through the completeness theorem.
- **Novelty.** On 18 November I searched for an existing Lean formalisation of a constructible hierarchy over Mac Lane set theory and found none. The closest I found were an unfinished Lean 4 development of the constructible hierarchy and developments in other provers that use replacement. I did not survey the literature on NF and Mac Lane set theory for this note.

`MacChoiceAll.lean` has `consistent_mac : Consistent 𝗠𝗔𝗖` and `consistent_mh : Consistent 𝗠𝗛`. As before, they are theorems because Lean proves `Consistent 𝗡𝗙𝗨𝗜` outright. They show that the interpretations are not vacuous. They say nothing about relative strength.

## 5. Checked and not checked

Checked on 18 November 2026:

- `lake build` of `standalone/` with the thirteen files added, in the layout of the tarball and from an empty build directory: 9,182 jobs, no errors. The build directory then held the 63 compiled modules.
- `#print axioms` for the four interpretations of §0, and for `MH.exists_hier`, `MH.wol`, `MH.sep_good`, `MH.hull_exists`, `MH.hcat_image`, `MH.bound_exists`, `consistent_mac_of_consistent_nf`, `consistent_mh`, `consistent_mac`: `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker` on each of the thirteen new modules: exit status 0 (`check/leanchecker_results_mac_choice_2026-11-18.txt`).
- nanoda on an export of the four interpretations of §0, `consistent_mh` and `consistent_mac` with everything they depend on: 17,763 declarations, no errors, the same three axioms (`check/nanoda_mac_choice.json`, `check/nanoda_mac_choice_output.txt`).

Not checked by Lean:

- That `𝗠𝗔𝗖` as stated is the theory you mean. It is `𝗠 ∪ 𝗔𝗖` in `MacTheories.lean` (96 lines), with `𝗔𝗖` the library's axiom. Read that file and the first 100 lines of `MHTheory.lean` first: the theorems say what they appear to say only if those definitions are right.
- That the collapse axiom holds anywhere except in the model inside NF. In particular it is not shown in Lean that ZF proves it.
- The descriptions in §2 and §3. They are written from the Lean files, and the Lean names are given so that each can be compared with its statement.

Not run this time: the main project with con-nf. The thirteen files are in its directory and in its `lakefile.toml`; they import nothing from con-nf.
