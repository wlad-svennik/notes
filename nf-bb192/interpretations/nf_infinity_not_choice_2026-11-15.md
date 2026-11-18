# NF proves Infinity and refutes Choice: the Lean proof

15 November 2026. Every numbered statement is a Lean theorem; its name is given in `code`. The prose proofs are summaries of the Lean proofs.

Files: `NFSpecker.lean` (1,873 lines; imports `ConNF.NF.NFUHartogs` and `ConNF.NF.Hailperin`) and `MutualInterpretability.lean` (39 lines; imports `NFUInterpretsNF` and `NFSpecker`). No `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`.

**Was there a formal proof already?** Not in Lean, as far as I could find. Metamath's New Foundations Explorer (Scott Fenton, 2015) has both results: `vinf` (the universe is infinite, after Rosser) and `nchoice` (≤ does not well-order the cardinals, Specker's Theorem 7.5). Beeson has Lean-checked basics for intuitionistic NF, which do not include Specker's theorem.

---

## 0. The statements

A **model of NF** is taken in two equivalent forms: a model of NFU in the sense of `NFUCut.Model` in which every object is a set (hypothesis `Fact (∀ x, M.isSet x)`), or a structure with `ConNF.NF.IsNF V mem` (extensionality and stratified comprehension for formulas in de Bruijn form). The second is the notion used in `nfu_inf_interprets_nf`. Theorem 6.1 passes from the second to the first.

| Lean name | Statement |
|---|---|
| `Model.nf_infinity` | Infinity: the universe belongs to no natural number |
| `IsNF.univ_not_finite` | the same with membership only: some family of sets contains every empty set and is closed under adjoining one element, but contains no universal set |
| `Model.not_wellOrdered_le` | Specker's theorem: it is not the case that any two sets are comparable by ≼ and every nonempty set of sets has a ≼-least member |
| `Model.no_wellOrdering_univ` | no set relation is a well-ordering with the whole universe as its field |
| `Model.nf_not_choice`, `IsNF.not_choice` | ¬Choice: some set of nonempty, pairwise disjoint sets has no set meeting each of them in exactly one element |
| `nf_interprets_nfu_inf` | every model of NF, with every object declared a set, is a model of NFU + Infinity |
| `nf_nfu_inf_mutually_interpretable` | the conjunction of `nfu_inf_interprets_nf` and `nf_interprets_nfu_inf` |

Here x ≼ y means that some set of Kuratowski pairs is an injection from x into y.

---

## 1. How this proof differs from Specker's

Specker works with cardinal numbers, the operation T, exponentiation 2^κ, and the sequence Φ(κ) = {κ, 2^κ, 2^(2^κ), …}. He shows that if Φ(κ) is finite with n elements then Φ(Tκ) has T(n) + 1 or T(n) + 2 elements, and gets a contradiction modulo 3 at a κ with Tκ = κ.

The Lean proof keeps the argument and removes two layers of machinery.

1. **No cardinals.** Everything is stated for sets and the preorder ≼, with x ≈ y meaning x ≼ y and y ≼ x. The role of Tκ is played by the singleton image ι"x. The exponential of x is defined when x ≼ ι"V; then x ≈ ι"y for some y, and the exponential is 𝒫y, which is determined up to ≈. Since ≈ is used in place of equinumerosity, the Cantor–Schröder–Bernstein theorem is never needed.
2. **No natural numbers.** Only the length of the sequence modulo 3 matters. The three lengths are three fixed objects, r₀ = ∅, r₁ = {∅}, r₂ = V, with the cyclic successor. So there is no arithmetic of finite cardinals, no T on numbers, and no counting.

A third point is specific to Infinity. In a finite universe the empty set has a finite Specker sequence, and ι"∅ = ∅. So Infinity follows from the key lemma directly, without passing through Choice.

---

## 2. Injections (part 1 of the file)

**Lemma 2.1** (`le_of_sub`, `le_trans'`, `le_conv`, `inj_img`). ≼ is reflexive and transitive and extends inclusion. An injection that is onto has a converse. The image of x under an injection is ≈ x.

**Lemma 2.2** (`le_simg`, `le_of_simg`). x ≼ y if and only if ι"x ≼ ι"y.

**Lemma 2.3** (`le_pow`, `simg_pow`). If x ≼ y then 𝒫x ≼ 𝒫y. And ι"𝒫y ≈ 𝒫ι"y.

**Lemma 2.4 (Cantor)** (`cantor`, `pow_univ`, `cantor_univ`). 𝒫y does not inject into ι"y. Since every object is a set, 𝒫V = V, so V does not inject into ι"V.

*Proof.* Given an injection f, let D be the set of a ∈ y such that f(s) = {a} for some s ⊆ y with a ∉ s. Then f(D) = {d} for some d ∈ y, and d ∈ D if and only if d ∉ D. The formula defining D is stratified because f relates s to {a}. ∎

**Lemma 2.5** (`exists_simg_eqv`). If x ≼ ι"V then x ≈ ι"y for some y.

Nothing in this part uses Infinity. The fact 𝒫V = V, which holds because every object is a set, is what separates NF from NFU here. It is used in Lemma 2.4 and in case (R1) of Lemma 3.2. Elsewhere the hypothesis only serves to apply extensionality to every object.

---

## 3. The length of the Specker sequence modulo 3 (part 2)

Let Ex be the set of pairs ⟨x, 𝒫y⟩ with x ≈ ι"y (`Ex`, `mem_Ex`), and let Nx be the cyclic successor on r₀, r₁, r₂ (`Nx`).

**Definition** (`L`). L is the least set of pairs such that

- (R1) if x does not inject into ι"V, then ⟨x, r₁⟩ ∈ L;
- (R2) if ⟨x, q⟩ ∈ Ex, ⟨q, r⟩ ∈ L and Nx(r, r′), then ⟨x, r′⟩ ∈ L.

So ⟨x, r⟩ ∈ L says that the sequence x, exp x, exp exp x, … stops, and that its length is r modulo 3. L exists by comprehension; the relation ≼ is first turned into a set of pairs (`LeSet`), so that the closure conditions are short formulas.

**Lemma 3.1** (`L_ind`, `L_inv`, `L_congr`, `L_res`, `L_fun`). Induction on L for properties given by sets. Inversion: a member of L arises by (R1) or (R2). If ⟨x, r⟩ ∈ L and x ≈ x′ then ⟨x′, r⟩ ∈ L. The second component is one of r₀, r₁, r₂, and it is determined by x.

**Lemma 3.2 (Specker's lemma)** (`L_T`). Assume that every set that does not inject into ι"V includes a copy of ι"V. If ⟨x, r⟩ ∈ L, then ⟨ι"x, r + 1⟩ ∈ L or ⟨ι"x, r + 2⟩ ∈ L (successors in the sense of Nx).

*Proof.* Induction on L.

(R1) x does not inject into ι"V, so ι"V ≼ x, and r = r₁. The exponential of ι"x is 𝒫x. If 𝒫x does not inject into ι"V, then ⟨𝒫x, r₁⟩ ∈ L and ⟨ι"x, r₂⟩ ∈ L. Otherwise 𝒫x ≈ ι"y for some y, and 𝒫y does not inject into ι"V: from ι"V ≼ x we get ι"V = ι"𝒫V ≼ 𝒫ι"V ≼ 𝒫x ≼ ι"y, hence V ≼ y, hence V = 𝒫V ≼ 𝒫y, and 𝒫y ≼ ι"V would contradict Lemma 2.4. So ⟨𝒫y, r₁⟩, ⟨𝒫x, r₂⟩ and ⟨ι"x, r₀⟩ are in L.

(R2) x ≈ ι"y, ⟨𝒫y, r⟩ ∈ L, and by the induction hypothesis ⟨ι"𝒫y, s⟩ ∈ L with s = r + 1 or r + 2. Then ι"x ≈ ι"ι"y, its exponential is 𝒫ι"y ≈ ι"𝒫y, so ⟨𝒫ι"y, s⟩ ∈ L by Lemma 3.1 and ⟨ι"x, s + 1⟩ ∈ L. ∎

The statement relates L at one type to L at the next. In the comprehension that carries the induction (`exists_TSet`), L and the three lengths occur under two names each, with types one apart. This is the only use of typical ambiguity.

**Lemma 3.3** (`L_refl`). If ⟨z, r⟩ ∈ L and z ≈ ι"y, then ⟨y, r′⟩ ∈ L for some r′.

**Theorem 3.4** (`specker_core`). Under the hypothesis of Lemma 3.2, no x with ⟨x, r⟩ ∈ L has ι"x ≈ x.

*Proof.* By Lemmas 3.2 and 3.1, ⟨x, r + 1⟩ ∈ L or ⟨x, r + 2⟩ ∈ L, and the length is unique. But r, r + 1, r + 2 are distinct. ∎

---

## 4. Infinity (part 3)

**Lemma 4.1** (`fin_ind`, `fin_sub`, `fin_all`). Induction on finite sets (members of natural numbers) for properties given by sets. Subsets of finite sets are finite. If Infinity fails, every set is finite.

**Lemma 4.2** (`fin_compar`, `fin_max`). A finite set is comparable by ≼ with every set. If any two sets are comparable, every nonempty finite set of sets has a ≼-largest member.

**Theorem 4.3** (`nf_infinity`). Infinity holds.

*Proof.* Suppose not. By Lemmas 4.1 and 4.2 any two sets are comparable and every nonempty set of sets has a largest member. Let X be the set of x with no ⟨x, r⟩ in L. If X is not empty, let m be largest in X. Then m ≼ ι"V by (R1), so m ≈ ι"y for some y; and 𝒫y ∈ X by (R2); so 𝒫y ≼ m ≼ ι"y, against Lemma 2.4. Hence X is empty, and ⟨∅, r⟩ ∈ L for some r. But ι"∅ = ∅, against Theorem 3.4. ∎

This part and the two before it depend only on the core file `ConNF.NF.NFUCut` (1,242 lines) and Mathlib.

---

## 5. Choice (parts 3–5)

**Theorem 5.1 (Specker)** (`specker`, `not_wellOrdered_le`). Suppose every set that does not inject into ι"V includes a copy of it. Then some nonempty set of sets has no ≼-least member.

*Proof.* Take the set of all x with some ⟨x, r⟩ ∈ L. V is in it by (R1) and Lemma 2.4. Let x be least. By Lemma 3.2, ι"x is in the set, so x ≼ ι"x ≼ ι"V and x ≈ ι"y for some y. By Lemma 3.3, y is in the set, so x ≼ y, hence ι"x ≼ ι"y ≼ x. So ι"x ≈ x, against Theorem 3.4. ∎

**Theorem 5.2** (`wo_le_total`, `wo_le_least`, `no_wellOrdering_univ`). If R is a well-ordering whose field is the universe, any two sets are comparable by ≼ and every nonempty set of sets has a ≼-least member. Hence there is no such R.

*Proof.* Restrict R to the sets in question and use the comparability of well-orderings and the least-element lemma for them (`emb_total`, `wo_min` in `NFUHartogs`). These are theorems about NFU + Infinity; they are available because Infinity is now a theorem. ∎

**Theorem 5.3 (Zermelo)** (`exists_selector`, `zermelo_key`, `K0_cmp`, `exists_final`, `zermelo_wo`, `ac_wellOrdering`). If every set of nonempty, pairwise disjoint sets has a choice set, the universe has a well-ordering.

*Proof.* Zermelo's proof of 1908. Applying Choice to the sets {⟨s, {a}⟩ : a ∈ s} for nonempty s gives a set c that selects one element γ(s) from each nonempty s; the pairs are ⟨s, {a}⟩ and not ⟨s, a⟩ so that the definitions are stratified. A chain is a family of sets that contains V and is closed under s ↦ s ∖ {γ(s)} and under intersections of nonempty subfamilies. Let K be the least chain. The key step: if s ∈ K is comparable by inclusion with every member of K, then every member of K is included in s ∖ {γ(s)} or includes s. From it, the members of K comparable with all others form a chain, so K is linearly ordered by inclusion. Put a ≤ b if every member of K that contains a contains b. This is a well-ordering of V: the least element of a nonempty X is γ(m) for m the intersection of the members of K that include X. ∎

**Theorem 5.4** (`nf_not_choice`). Choice fails.

---

## 6. The link to `IsNF` and the converse interpretation (part 6)

**Theorem 6.1** (`modelOfNF`, with `sat_trF`, `strat_trF`). If `IsNF V mem`, then (V, mem), with every object declared a set, is a `NFUCut.Model`.

*Proof.* A formula with named variables and a stratification σ is translated into de Bruijn form, each quantifier carrying the type σ gives to its variable; "is a set" becomes a true formula. Satisfaction and stratification are preserved. ∎

**Corollaries** (`IsNF.infinity`, `IsNF.univ_not_finite`, `IsNF.not_choice`, `nf_interprets_nfu_inf`). Theorems 4.3 and 5.4 for every structure with `IsNF`. In particular the identity is an interpretation of NFU + Infinity in NF.

**Theorem 6.2** (`nf_nfu_inf_mutually_interpretable`, in `MutualInterpretability.lean`). (1) There are formulas δ, ε, η of the language of NFU, without parameters, such that in every model of NFU + Infinity the objects satisfying δ, with ε as membership and η as equality, form a model of NF. (2) Every model of NF, with every object declared a set, is a model of NFU + Infinity.

---

## 7. What is checked and what is not

**Checked.** Both files compile with Lean 4.35.0, with no `sorry`. Every theorem in the table of §0 depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`. The two files as delivered were rebuilt in an empty directory. `nf_infinity` and `not_wellOrdered_le` use, besides Mathlib, only the core file `ConNF.NF.NFUCut`; `no_wellOrdering_univ`, and with it `nf_not_choice`, also uses declarations of `NFUArith` and `NFUHartogs` (19 and 33 of them for the former).

**Not checked by Lean.**

1. That the definitions say what they are meant to say. The ones to read are `NFUCut.Model`, `Model.Infinity`, `Model.IsWO`, `Model.AC` and `ConNF.NF.IsNF`. Two of the statements (`IsNF.univ_not_finite`, `IsNF.not_choice`) are written with membership alone, so that nothing else has to be read.
2. (Resolved on 15 November, evening.) The passage from "holds in every model" to "NF proves" is now in Lean, by the completeness theorem of the library Foundation: `SetTheory.nf_provable_universeInfinite : 𝗡𝗙 ⊢ Axiom.universeInfinite` and `SetTheory.nf_provable_not_choice : 𝗡𝗙 ⊢ ∼Axiom.choice`. See `nf_syntactic_interpretation_2026-11-15.md`.
3. (Resolved on 15 November, evening, in `NFChoiceForms.lean`.) Other forms of Choice. Zorn's lemma and the existence of choice functions each imply the form with choice sets for disjoint families, in every model of NFU (`zorn_ac`, `choiceFunctions_ac`), so NF refutes them (`nf_not_zorn`, `nf_not_choiceFunctions`, `IsNF.not_zorn`, and `𝗡𝗙 ⊢ ∼Axiom.zorn`). The well-ordering form was already refuted directly (`no_wellOrdering_univ`).
4. (Resolved on 15 November, evening.) The files are now modules of a lake project built with `lake build`, were replayed in Lean's kernel with `leanchecker`, and the main theorems were checked by the external type checker nanoda. See `nf_syntactic_interpretation_2026-11-15.md`, §8.

The theorems are not vacuous: the Lean development contains `exists_nf`, a structure with `IsNF`.
