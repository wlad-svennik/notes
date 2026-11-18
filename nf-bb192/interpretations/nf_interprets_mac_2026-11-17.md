# NF interprets Mac Lane set theory without Choice

17 November 2026. Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Foundation `fbcfee52`.

## 0. Result

```lean
instance interpretsM    : 𝗡𝗙 ⊳ 𝗠
instance nfuInterpretsM : 𝗡𝗙𝗨𝗜 ⊳ 𝗠
theorem nf_provable_translate_of_m {σ : Sentence ℒₛₑₜ} : 𝗠 ⊢ σ → 𝗡𝗙 ⊢ interpretsM σ
theorem consistent_m_of_consistent_nf : Entailment.Consistent 𝗡𝗙 → Entailment.Consistent 𝗠
```

`𝗠` is Mathias's theory M: extensionality, empty set, pairing, union, power set, infinity, foundation, separation for bounded formulas and transitive containment. It has no axiom of choice. `𝗠𝗔𝗖` is `𝗠` with the library's `Axiom.choice`; it is stated in `MacTheories.lean` but nothing is proved about it.

**Status of "NF interprets MAC".** Lean proves `𝗡𝗙 ⊳ 𝗠`. The step from M to MAC is Mathias, *The strength of Mac Lane set theory* (2001), Theorem 1: if M is consistent, so is MAC with V = L. His proof builds the new model inside M: first a model of M + Axiom H from the well-founded extensional relations, then L inside it. That gives an interpretation of MAC in M. This step is not formalised here. I have the statement from a secondary source (arXiv 1806.08500) and did not go through Mathias's proof to confirm that each step is an interpretation in the sense of `⊳`. So "NF ⊳ MAC" is this Lean theorem composed with a theorem on paper.

Six files, 2,205 lines, no `sorry`. `interpretsM` and `nfuInterpretsM` depend on `propext`, `Classical.choice`, `Quot.sound` only.

| File | Lines | Content | Imports |
|---|---|---|---|
| `MacTheories.lean` | 96 | `𝗦𝗘𝗣₀`, `𝗧𝗖𝗼`, `𝗠`, `𝗠𝗔𝗖` | Foundation |
| `MacModel.lean` | 358 | bounded formulas are absolute; `IsMacBase`; `IsMacBase.models` | `MacTheories` |
| `NFStrat.lean` | 250 | stratified definitions and comprehension in a model of `𝗡𝗙` | `NFTheories`, `MacModel` |
| `NFRel.lean` | 420 | pointed graphs, bisimulation, types, membership on types | `NFStrat` |
| `NFMac.lean` | 505 | θ, stable sets, finite ordinals, the domain | `NFRel`, `NFInterpretations` |
| `NFInterpretsMac.lean` | 576 | definable subsets, the model conditions, the interpretation | `NFMac`, `NFUJensen` |

## 1. The model

Work in a model V of NF. Kuratowski pairs are used throughout.

**Pointed graphs.** A *graph* is any set r; its edges are the pairs in it, written a → b (`Rl r a b`). A pointed graph (r, t) is a picture of a set: the node t stands for a set whose members are the sets pictured by (r, a) for the edges a → t. A graph is *well-founded* if every set with a member has a member with no predecessor in the set (`WF`). No extensionality is asked of the graph.

**Types.** Two pointed graphs picture the same set when they are bisimilar (`Bis`). The *type* of (r, t) is the set of the codes ⟨s, {{{u}}}⟩ of the well-founded pointed graphs (s, u) bisimilar to it (`IsType x r t`). Z is the set of types (`InZ`). Membership on types is

> x E y  ⟺  some (s, t) in y has an edge a → t with (s, a) in x   (`EE`).

E is a set relation; call its graph g (`IsEg g`).

**The type-raising map.** θ(x) is the type of the pointed graph (g, x): the picture of x drawn with types as nodes (`IsType y g x` says y = θ(x); `IsTheta`). If x has type 6 in a stratification, θ(x) has type 12. So θ is not a set, but "y = θ(x)" is a stratified condition.

**The domain.** A set X of types is *stable* if θ maps X onto X (`Stable g X`), and *transitive* if members of members of X are in X (`Trans`). The domain is

> D = the types that belong to some stable transitive set   (`Dom`).

Membership is E and equality is equality. The condition "stable" uses X at two types, so `Dom` is not stratified. It does not need to be: only the sets formed inside the proof need stratified conditions.

## 2. Why this is a model of 𝗠

Three facts carry the proof.

1. **Types behave like sets** (`NFRel.lean`).
   - `ee_iff`: the members of the type of (r, t) are the types of (r, a) for a → t.
   - `ee_ext`: types with the same members are equal. The bisimulation is the set of pairs (a, a′) with (r, a) bisimilar to (s, a′), together with the pair of the two points.
   - `ee_wf`: a set that contains a type contains a type with no member in the set.
2. **Sets of types become types after θ** (`NFMac.lean`).
   - `theta_mem`: the members of θ(x) are the θ(u) for u E x. `theta_inj`: θ is one-to-one on types.
   - `theta_sup`: for every set S of types there is a type whose members are exactly the θ(s), s ∈ S. The graph is g with one more node, the empty set, placed above the members of S. The empty set is not a type, so it is a new node. No extensionality has to be checked, which is why graphs are taken up to bisimulation and not up to isomorphism.
   - `full`: every set of types of the form θ(x) is the extension of a type. Proof: apply `theta_sup` to {x : θ(x) ∈ S}, which is a set because "θ(x) ∈ S" is stratified.
3. **Stable sets are closed under power set** (`NFMac.lean`).
   - `stable_full`: every subset of a stable set is the extension of a type.
   - `pow_stable`: if X is stable, so is P(X) = {y : every member of y is in X}. Given y ∈ P(X), the set {u ∈ X : θ(u) E y} is a subset of X, so it is the extension of some w; then θ(w) and y have the same members, so θ(w) = y.

No induction, no natural numbers and no cut are used in 1–3.

**Infinity.** The finite ordinals among the types (`InOm`) are the members of every set that contains the type without members and is closed under successor. They form a stable transitive set (`om_stable`). The one thing to prove by construction is that every finite ordinal has a successor (`succ_of_hasFin`): take a picture with finitely many nodes, pick a node c outside them, and put c above the top and its predecessors. A node outside a finite set exists because the universe is not finite: `exists_fresh` uses `nf_provable_universeInfinite`, that is, Specker's theorem. This is the only use of the earlier files.

**The axioms.** `MacModel.lean` proves, with no reference to NF, that a structure is a model of `𝗠` if it has (`IsMacBase`): extensionality; foundation; infinity; a set containing any two given elements; a set containing all subsets of a given element; transitive containment; and

> `sep`: for every t, every subset of the members of t that is definable with parameters in the structure of the members of t is the extension of an element.

Exact pairing, union and power set come from the weak forms and bounded separation. Bounded separation comes from `sep` and `eval_submodel_iff`: bounded formulas are absolute for transitive sets.

`isMacBase_of_embed` checks these conditions for D. All of them reduce to one statement (`key` in the proof): if X is stable and transitive and S ⊆ X is a set, then S is the extension of an element of D. It follows from `stable_full` and `pow_stable`.

| Condition | Why it holds |
|---|---|
| extensionality | `ee_ext` |
| foundation | `ee_wf` |
| pairing (weak) | `key` with the union of two stable transitive sets (`union_stable`) |
| power set (weak), transitive containment | `key` with S = P(X), S = X |
| infinity | `key` with the finite ordinals (`om_stable`, `om_succ_exists`) |
| `sep` | `exists_definable_subset`, then `key` |

**Definable subsets** (`exists_definable_subset`). Let a structure have universe a set A of the model and membership given by a graph R. For any formula ψ, rewrite it so that every quantifier is restricted to A and every atom x ∈ y becomes "some pair ⟨x, y⟩ is in R" (`tr`). The result is stratified whatever ψ was (`tr_strat`): all variables of ψ get type 0, A type 1 and R type 3. It means in the model what ψ means in the structure (`tr_eval`). So the subset defined by ψ is a set by comprehension.

## 3. Stratified comprehension without writing formulas

`NFStrat.lean`. `SDef τ R` holds a formula, a proof that it is stratified with variable types τ, and a proof that it defines the relation R in every structure. The constructors `SDef.mem`, `SDef.eq`, `SDef.and`, `SDef.or`, `SDef.not`, `SDef.imp`, `SDef.iff`, `SDef.all t`, `SDef.ex t` and `SDef.comp` build the three together; the type of each bound variable is the argument `t`. `SDef.comp f c` substitutes variables and shifts all types by c; it rests on `Semiformula.stratified_rew`. `SDef.comprehension` turns an `SDef` into a set of the model, and `exists_rel` into a graph.

Types used, with nodes at 0: pairs 2, graphs 3, codes of pointed graphs 5, types 6, the graph of E 9, θ(x) 12.

## 4. The interpretation as a statement about derivations

`macTranslation : DirectTranslation 𝗡𝗙 ℒₛₑₜ` has domain formula `Hin.domU.φ`, membership formula `Hin.eeD.φ`, and equality as equality. Both formulas are closed. `macModel_models` shows that in every model of `𝗡𝗙` the interpreted structure is a model of `𝗠`; `interpretsM` follows by the completeness theorem of the library (`SetTheory.complete`), as in `NFInterpretations.lean`. `nfuInterpretsM` is `DirectInterpretation.comp interpretsM nfuInterpretsNF`.

## 5. Checked and not checked

Checked on 17 November 2026:

- `lake build` of `standalone/` with the six files added, in the layout of the tarball and from an empty build directory: 9,149 jobs, no errors, about 8 minutes with Mathlib and Foundation already compiled. The build directory then held the 31 compiled modules.
- `#print axioms` for `interpretsM`, `nfuInterpretsM`, `IsMacBase.models`, `eval_submodel_iff`: `propext`, `Classical.choice`, `Quot.sound`.
- `leanchecker` on each of the six new modules: exit status 0 (`check/leanchecker_results_2026-11-17.txt`).
- nanoda on an export of `interpretsM`, `nfuInterpretsM`, `IsMacBase.models`, `eval_submodel_iff`, `nf_provable_translate_of_m` and `consistent_m_of_consistent_nf` with everything they depend on: 15,704 declarations, no errors, the same three axioms (`check/nanoda_mac.json`, `check/nanoda_mac_output.txt`). The output prints the statements as the checker read them.

Not checked by Lean:

- That `MacTheories.lean` states Mathias's M. It is 96 lines and is the file to read. Two points to look at: bounded formulas are the library's `Bounding.Closure` for `∈`, and infinity and foundation are the library's `𝗕𝗦𝗧` forms.
- Anything about Choice, and Mathias's theorem that M interprets MAC.
- The converse question (that Mac does not interpret NF).

Not run this time: the main project with con-nf. The six files are in its directory and in its `lakefile.toml`, but only `standalone/` was built. The six files are the same in both places and import nothing from con-nf.

Remarks:

- The proof does not use ladders, the calm cut or the arithmetic of the model. The plan of 17 November was to use ladders; this route is shorter.
- `𝗡𝗙 ⊳ 𝗠` uses, of the earlier work, only `𝗡𝗙 ⊢ Axiom.universeInfinite`. It imports `NFInterpretations.lean` for that theorem and `NFUJensen.lean` for the composition, so the files do depend on the earlier ones as files.
- `𝗡𝗙𝗨𝗜 ⊳ 𝗠` is obtained through `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. A direct proof inside NFU + Infinity should go the same way with sethood carried along; it was not attempted.
