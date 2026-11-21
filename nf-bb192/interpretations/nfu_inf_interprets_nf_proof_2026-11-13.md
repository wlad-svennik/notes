# NFU + Infinity interprets NF: the proof written out

13 November 2026; §3.3 revised 14 November 2026, when Lemma 3.2 became a Lean theorem; status, §1, §4.5, §8 and §9 revised 15 November 2026, when the theorem itself became a Lean theorem. Apart from the places marked **[Lean]** this is a paper proof.

**Status in one paragraph.** The theorem is now proved in Lean: `NFUCut.nfu_inf_interprets_nf` (stated in §1), with no `sorry` and the axioms `propext`, `Classical.choice`, `Quot.sound`. The proof that Lean checks is not the one this document was written around. It uses §2 (arithmetic of U, the calm cut), the satisfaction relation of §3.1, §3.2 (ladders) and §3.3 (Lemma 3.2) as they stand. From there it takes a different route, described in the companion note `nfu_inf_interprets_nf_term_model_2026-11-15.md`: the overlapping construction of a model of tangled type theory is formalised inside an abstract structure with Separation and Collection, with the height an element of that structure (§4.5), and the interpretation is a term model on a cut of the numbers, defined arithmetically. **The Transfer Lemma (§4.3) is no longer needed, and neither are §4.2, §4.4, §5, §6 and §7** (finite-height tangles from the Holmes–Wilshaw formalisation, Crabbé's conversion, the Main Lemma, interpretation existence, cut elimination). Those sections are kept unchanged below because their results are correct and partly formalised, but the theorem does not depend on them; Lean's list of the constants the theorem uses contains nothing from the corresponding files. The converse is in Lean too: NF proves Infinity (Specker's theorem), so NF interprets NFU + Infinity by the identity, and the two theories are mutually interpretable (`nf_nfu_inf_mutually_interpretable`; §8, item 1). What Lean does not check is listed at the end of §9.

Tags on results: **[proved]** full proof here; **[textbook]** standard, with the adaptation explained; **[Lean]** compiled and kernel-checked; **[cited]**; **[inspection]**.

---

## 1. Statement

**NFU.** Language: ∈ and a unary predicate S ("is a set"). Axioms: x ∈ y → S(y); sets with the same members are equal; and for every stratified formula φ not containing y, ∃y (S(y) ∧ ∀x (x ∈ y ↔ φ)). (S imposes no stratification constraint.) **Infinity**: the universe is not finite. Let **U = NFU + Infinity**. No form of Choice and no Axiom of Counting is assumed.

**NF.** Language: ∈ and =. Axioms: the equality axioms, extensionality, and comprehension for every stratified formula. Let **NF₀** be the finite list consisting of the equality axioms, extensionality, and the twelve existence statements of the Lean structure `NFModel`, written without function symbols. NF₀ and NF have the same theorems: one direction is immediate, the other is Hailperin's theorem **[Lean: `NFModel.comprehension`]**. Every axiom of NF₀ is a stratified sentence using at most six types, so each has a stratified typed version with types in the **window** W = {0,…,5}.

**Theorem.** U interprets NF.

**The Lean statement** (`NFUCut.nfu_inf_interprets_nf`). There are formulas δ, ε, η of the language of NFU, without parameters and the same for all models, such that for every model M of U there are a structure (W, mem) satisfying extensionality and every instance of stratified comprehension, and a map π from {x : M ⊨ δ(x)} onto W, with π(x) = π(y) ⇔ M ⊨ η(x, y) and mem(π(x), π(y)) ⇔ M ⊨ ε(x, y). Equality of NF is interpreted by η. That U proves the translations of the axioms of NF follows by the completeness theorem. Since 15 November (evening) this step is in Lean as well, using the completeness theorem of the library Foundation, with equality interpreted by equality: `SetTheory.nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`, where `𝗡𝗙𝗨𝗜` is Jensen's NFU + Infinity in the language of ∈ and = alone, and `SetTheoryU.interpretsNF : 𝗡𝗙𝗨𝗜ₛ ⊳ 𝗡𝗙` for NFU with a predicate "is a set". See `nf_syntactic_interpretation_2026-11-15.md`.

**Plan, as carried out.** (i) Arithmetic of U and the calm cut (§2). (ii) At calm heights, a structure 𝔏 with Separation, Collection and a definable well-ordering, built as a level of a constructible hierarchy over a ladder (§3). (iii) Inside any such structure, a model of tangled type theory whose height is a number of the structure (§4.5). (iv) Closed terms in a signature with Skolem functions for the axioms of `NFModel` are evaluated in that model along increasing sequences of levels; Ramsey's theorem inside the structure makes the truth values of the atoms below a bound q independent of the levels; this gives, for every q in a cut, a truth assignment satisfying the axioms below q. (v) From these assignments a term model of NF₀ is defined on a cut of the numbers by a Henkin-style choice of the leftmost assignment, with all definitions arithmetical. (vi) The definitions are written as formulas of the language of NFU. Steps (iv)–(vi) are in the companion note.

**The original plan** (not used in the Lean proof). By the interpretation existence lemma (§7) it suffices to find a definable cut 𝖪 of the natural numbers of U such that U proves: no number in 𝖪 codes a cut-free refutation of NF₀. Inside U, given such a refutation π, a syntactic conversion (§5) produces a finite list of typed sentences; a model of tangled type theory with enough types (§4), built inside a constructible structure that exists at "calm" heights (§§2–3), has seven types on which those sentences cannot tell a type from its successor; evaluating the converted proof on these types gives a contradiction (§6).

---

## 2. Arithmetic in U

Every numbered statement in this section, and the two remarks at the end of §2.1, are formalised in Lean for an arbitrary model of U. Not formalised: the asides marked as such. Lean names are given in `code`; §2.4 describes the files.

### 2.1 Numbers **[Lean]**

ℕ is the set of Frege numerals: 0 = {∅}, n + 1 = {x ∪ {y} : x ∈ n, y ∉ x}, and ℕ is the intersection of all sets containing 0 and closed under successor.

**Lemma 2.0.** (a) *Induction.* If a condition on n is given by a stratified formula with parameters, induction on ℕ holds for it (`nat_ind_fml`). (b) Every natural number is 0 or a successor, and 0 is not a successor (`nat_cases`, `zero_ne_succ`). (c) If y ∈ n + 1 and c ∈ y, then y ∖ {c} ∈ n (`rem_mem_of_succ`). (d) Two natural numbers with a common member are equal (`nat_disjoint`). (e) With Infinity, every natural number has a member and successor is injective (`nat_nonempty`, `succ_inj`).

*Proof.* (a) The n satisfying the condition form a set. (b) Induction. (c) Induction on n: a member of n + 2 is x ∪ {b} with x ∈ n + 1 and b ∉ x; removing b gives x, and removing c ∈ x gives (x ∖ {c}) ∪ {b}. (d) Induction on m, for all n at once, by (b) and (c). (e) For x ∈ m and b ∉ x, x ∪ {b} ∈ m + 1 = n + 1, so x ∈ n by (c), and m = n by (d). ∎

*Set functions.* Pairs are Kuratowski pairs, and a triple ⟨a, b, c⟩ is ⟨⟨a, b⟩, ⟨c, c⟩⟩, so that its three components have one type. A function F : ℕ → ℕ is a *set function* if its graph is a set (`NatFn`, and `NatOp` for two arguments). Set functions are closed under composition (`natFn_comp`, `natFn_op₂`). The numbers satisfying an equation or an inequality between set functions, or a Boolean combination of such, form a set (`isPred_eq`, `isPred_le`, `isPred_not`, `isPred_and`), so induction holds for these conditions (`num_ind`).

**Lemma (recursion)** (`exists_prec`, `prec_unique`). For set functions h : ℕ → ℕ and g : ℕ × ℕ → ℕ there is exactly one set function F : ℕ × ℕ → ℕ with F(a, 0) = h(a) and F(a, b + 1) = g(a, F(a, b)).

*Proof.* Let A be the intersection of all sets of triples that contain ⟨a, 0, h(a)⟩ and contain ⟨a, b + 1, g(a, c)⟩ whenever they contain ⟨a, b, c⟩. By induction on b, for every a some ⟨a, b, c⟩ is in A. The triples of A that arise from one of the two clauses form a set closed under the clauses (this uses 2.0(b) and (e)), so every triple of A arises from a clause. Then, by induction on b, c is determined by a and b. Uniqueness of F is an induction on an equation between set functions. ∎

So +, ×, 2ˣ (with 2⁰ = 1 and 2^{b+1} = 2^b + 2^b) and the **tower** t(0) = 2, t(b + 1) = 2^{t(b)} are set functions on ℕ (`addN`, `mulN`, `expN`, `towN`).

**Theorem 2.1 (the arithmetic of U).** With 0, 1, +, ×, the set ℕ is a commutative semiring, and a ≤ b ⇔ ∃c (a + c = b) is a total order compatible with + and × (`instCommSemiringNum`, `instIsOrderedRingNum`, `instCanonicallyOrderedAddNum`, `le_total'`). ℕ satisfies the axioms of Robinson arithmetic (`peano`) and the induction schema for every formula of arithmetic with parameters (`pa_induction`). So U proves every theorem of Peano arithmetic about its ℕ.

*Proof.* The semiring and order laws are inductions on equations and inequalities between set functions. For the schema, take formulas of arithmetic in relational form, with atomic formulas x = y, x = 0, x = 1, x + y = z, x · y = z. Restrict the quantifiers to ℕ and replace the last two atoms by membership of a triple in the graph of + or of ×. The result is stratified: give every variable the type of a number and the two graphs, which are parameters, the type of a set of triples of numbers (`strat_trA`). Apply 2.0(a). ∎

I call this *the arithmetic of U*. In particular U proves, for its own numbers, every theorem of PA about finite syntactic objects coded by numbers.

Two remarks which §§3 and 6 use:

- *Recursion into an arbitrary set* (`exists_rec_set`, `rec_set_unique`). For a set D, a ∈ D and a set function g : D → D there is a unique set function f : ℕ → D with f(0) = a and f(n + 1) = g(f(n)). The proof is the one above.
- *Coding finite sets* (`exists_code`, `exists_code_rel`). Say that digit i of c is 1 if c = a·2^{i+1} + 2^i + b for some a and some b < 2^i (`Bit`). Every finite set s of numbers is coded by a number c: i ∈ s if and only if digit i of c is 1. Every finite relation between numbers, in particular every set function from one finite set of numbers to another, is coded in the same way through the pairing (x, y) ↦ (x + y)² + x. The proof is an induction on a bound n for the stratified condition "every set of numbers below n has a code below 2ⁿ", together with the fact that a finite set of numbers is bounded (induction on its size). So theorems of PA about coded finite sets and colourings apply in U to sets.

### 2.2 The operation T **[Lean]**

For n ∈ ℕ there is a natural number that contains {{a} : a ∈ x} for every x ∈ n (`exists_T`; induction on n). Call it T(n) (`T`). By 2.0(d), T(m) = n as soon as one x ∈ m has {{a} : a ∈ x} ∈ n (`T_eq_of_mem`). The relation "T(m) = n" is stratified, with m one type below n; T is not a set function, since its two arguments have different types.

**Lemma 2.1.** (a) T(0) = 0 and T(n + 1) = T(n) + 1 (`T_zero`, `T_succ`). (b) T(n) = n for every calm n, in the sense of §2.3 (`T_eq_self_of_inS`).

Earlier versions of this note also stated that T is a bijection of ℕ commuting with +, ×, 2ˣ and t, and that formulas of arithmetic are invariant under T. Those statements are standard and true, but they were used only in the earlier proof of Lemma 2.2. Nothing below needs them, and they are not formalised.

### 2.3 Calm numbers **[Lean]**

A set x is **strongly cantorian** if the restriction of a ↦ {a} to x is a set (`SC`). A natural number is **calm** if it has a strongly cantorian member. Let 𝖲 be the class of calm numbers (`InS`). The condition is not stratified, so 𝖲 need not be a set; it is a definable class. (Earlier versions called n calm if T(m) = m for all m ≤ n. By Lemma 2.2 the calm numbers in the present sense have that property, and only the present definition is used.)

**Lemma 2.1′.** ∅ is strongly cantorian; if x is, so are x ∪ {b}, every subset of x, and P(x) (`sc_emp`, `sc_adj`, `sc_subset`, `sc_pow`). If x ∈ n is strongly cantorian then {{a} : a ∈ x} ∈ n (`simg_mem_of_sc`).

*Proof.* Let f be the graph of a ↦ {a} on x. For P(x), the graph of y ↦ {y} on P(x) is {⟨y, {⋃ f″y}⟩ : y ⊆ x}, given by a stratified formula with f as a parameter. For the last claim, the condition "for all y ⊆ x, if y ∈ m then f″y ∈ m" on m is stratified because f is a parameter, f″y is the singleton image of y, and induction on m proves it. ∎

**Lemma 2.1″ (counting).** (i) Every member of a + c includes a member of a (`exists_subset_of_add`). (ii) If A ∈ a and B ∈ c are disjoint, then A ∪ B ∈ a + c (`un_mem_add`). (iii) If W ∈ k is a set of sets none of which contains b, then {z ∪ {b} : z ∈ W} ∈ k (`adjImg_mem`). (iv) If y ∈ m and {{a} : a ∈ y} ∈ n, then P(y) ∈ 2ⁿ (`pow_mem_expN`).

*Proof.* (i)–(iii) by induction on c, c and k. (iv) is the equation 2^{T(m)} = |P(y)| for the exponential defined by recursion; it is an induction on m, for all n at once, with the graph of 2ˣ as a parameter: P(x ∪ {b}) is the disjoint union of P(x) and {z ∪ {b} : z ∈ P(x)}, both in 2^{n′} where n = n′ + 1, by 2.0(c), (ii), (iii). ∎

**Lemma 2.2** (`lemma_2_2`). 0 ∈ 𝖲. If n ∈ 𝖲 then n + 1 ∈ 𝖲 and 2ⁿ ∈ 𝖲. 𝖲 is closed downwards and under + and ×. T(n) = n for n ∈ 𝖲.

*Proof.* Successor: for x ∈ n strongly cantorian, Infinity gives b ∉ x, and x ∪ {b} ∈ n + 1 is strongly cantorian. Downwards: 2.1″(i) and subsets. T(n) = n: Lemma 2.1′. Exponential: for x ∈ n strongly cantorian, {{a} : a ∈ x} ∈ n, so P(x) ∈ 2ⁿ by 2.1″(iv), and P(x) is strongly cantorian. Sum and product: if a ≤ b then a + b ≤ 2^{b+1} and a · b ≤ 2^{b+b}, since k ≤ 2^k. ∎

So 𝖲 is a cut closed under addition, multiplication and exponentiation. (In a model of the Axiom of Counting, 𝖲 = ℕ. This remark is not in Lean and is not used.)

**Lemma 2.3 (tower absorption)** (`lemma_2_3`; for the first sentence `Shortening.C₂_down` and `Shortening.C₂_succ`). 𝖢₂ = {n : t(n) ∈ 𝖲} is a cut. There is a definable cut 𝖪 ⊆ 𝖢₂ closed under + and ×. For n ∈ 𝖪 and standard c, d, e, the result of applying e exponentials to t(c·n + d) is calm.

*Proof.* t is monotone, because k ≤ 2^k, so 𝖢₂ is closed downwards; t(n + 1) = 2^{t(n)} and Lemma 2.2 give closure under successor. Put K₁ = {n : ∀m ∈ 𝖢₂ (m + n ∈ 𝖢₂)}, which is closed under +, and 𝖪 = {n : ∀m ∈ K₁ (m · n ∈ K₁)} (Solovay's shortening). The last claim follows from closure of 𝖪 under + and × and Lemma 2.2. In Lean the argument is done once for an abstract ordered commutative semiring (`Shortening.absorb`) and then applied to the numbers of the model (`shortening_hyp`). ∎

This is the only place where the argument is specific to NFU: the exponential closure of the cut lets it absorb one tower.

### 2.4 The Lean files **[Lean]**

Files `ConNF/NF/NFUCut.lean` (about 1,240 lines), `ConNF/NF/NFUArith.lean` (about 1,990 lines), `ConNF/NF/NFULadder.lean` (about 1,550 lines; the two remarks of §2.1 and §3.2), `ConNF/NF/NFUSat.lean` (about 1,080 lines; the satisfaction relation of §3.1), `ConNF/NF/NFUSound.lean` (about 1,500 lines; soundness, §3.1) `ConNF/NF/NFUHartogs.lean` (about 8,540 lines; steps (1) and (2) of §3.3, recursion along a well-ordering, the definition of the hierarchy and the facts about it listed in §3.3 (3)) and `ConNF/NF/NFUConstr.lean` (about 7,700 lines; steps (4)–(9) of §3.3 and Lemma 3.2); the standalone `NFUCut.lean` (about 23,380 lines) contains all seven and needs only Mathlib. No `sorry`, replayed in the kernel checker, axioms `propext`, `Classical.choice`, `Quot.sound` only. Build with `lake build ConNF.NF.NFUConstr`.

**Setting.** A model of NFU (`Model`) is a type with a membership relation and a predicate "is a set" such that only sets have members, sets with the same members are equal, and every stratified formula with parameters defines a set. Formulas (`Fml`) have named variables, and a stratification is a function from names to types (`Fml.strat`). Infinity (`Infinity`) says that the universe belongs to no natural number; `infinity_iff` shows this is the same as: every member of a natural number omits some object. Every theorem of this section is proved for an arbitrary such model with Infinity, so it is a statement about what U proves. `M.Num` is the type of natural numbers of the model M.

**Three things to know when reading the statements.**

1. No model of NFU + Infinity is exhibited in Lean (that would be Jensen's theorem). The theorems are about all models, and Lean does not rule out that there are none.
2. `pa_induction` is about formulas of arithmetic in relational form (`AFml`). The passage from formulas with terms to relational form is the usual one and is not formalised.
3. Lemma 2.3 quantifies over standard c, d, e: they are Lean natural numbers, cast into `M.Num`.

---

## 3. Structures inside U

### 3.1 Set structures, satisfaction and soundness **[Lean]**

A *set structure* is given by two sets: U, the set of pairs ⟨t, a⟩ with a an element of sort t, and E, the set of triples ⟨r, a, b⟩ with a related to b by the relation number r. Sorts and relations are indexed by numbers. Equality, where wanted, is one of the relations.

Formulas are coded by numbers of U, which may be nonstandard, through the pairing (x, y) ↦ (x + y)² + x: the atomic formula r(v, w) is (0, (r, (v, w))), ¬φ is (1, φ), φ ∧ ψ is (2, (φ, ψ)), ∀v φ is (3, (v, φ)), and the n-th variable of sort t is (t, n) (`cRel`, `cNeg`, `cAnd`, `cAll`, `vr`). An *assignment* is a set function defined on all of ℕ that gives every variable a value of its sort (`IsAsg`); s[v ↦ a] is `updS`.

**Theorem 3.0 (satisfaction)** (`satisfaction`; also `exists_satSet`, `sat_char`, `consistent`). For every set structure 𝔐 = (U, E) there is a set of the model, the satisfaction relation (`satSet`), such that, writing 𝔐 ⊨ φ[s] for membership of the pair of φ and s in it (`Holds`):

- every code built from atomic formulas by ¬, ∧ and ∀v is *decided*: at every assignment it is true or false, and never both (`Form`);
- 𝔐 ⊨ r(v, w)[s] if and only if s(v) is related to s(w) by the relation number r;
- 𝔐 ⊨ ¬φ[s] if and only if not 𝔐 ⊨ φ[s], for decided φ;
- 𝔐 ⊨ (φ ∧ ψ)[s] if and only if 𝔐 ⊨ φ[s] and 𝔐 ⊨ ψ[s];
- 𝔐 ⊨ ∀v φ[s] if and only if 𝔐 ⊨ φ[s[v ↦ a]] for every a of the sort of v.

Here r, v, w, the sort and index of a variable, and the formulas themselves are arbitrary numbers of the model.

*Proof.* Work with *signed facts*: (φ, 1, s) for "φ is true at s" and (φ, 0, s) for "φ is false at s", coded as the pair of {{{c}}} and s, c the number coding (φ, sign); the three singletons make the two components of one type. One step of the truth definition says which facts follow from a set Y of facts: for instance (φ ∧ ψ, 0, s) follows if one of φ, ψ is false at s and the other is true or false at s, and (∀v φ, 0, s) follows if φ is true or false at every s[v ↦ a] and false at one. Every clause is positive in Y, and one step is given by a stratified formula with Y, U, E, the set of assignments and the graphs of + and · as parameters. Let Sat be the intersection of all sets closed under one step; it is a set by one comprehension. It is closed under one step, and, the step being monotone, every member of Sat arises by one step from Sat (Knaster–Tarski). Since codes determine their tag, sign and parts, this gives the clauses for truth and for falsity separately (`sat_char`). No code is both true and false at an assignment: induction on the code, the parts of a code being smaller numbers (`consistent`). The clauses of the theorem follow. ∎

Two differences from the textbook route. The relation is obtained as a least fixed point, not by recursion on the height of formulas, so no notion of height is needed. Assignments are total, not finite; a structure has an assignment as soon as there is a set function choosing an element of every sort, which for sorts indexed by an initial segment of ℕ is an induction (not in Lean, and not needed for the theorem).

**Derivations.** A *sequent* Γ ⊢ Δ is a pair of sets of U whose members are codes of formulas. The calculus is the two-sided sequent calculus for ¬, ∧, ∀ **without cut**, with weakening built into the axioms and the principal formula kept in the premises:

- axiom: Γ ⊢ Δ when some formula is in both Γ and Δ;
- ¬ left: from Γ ⊢ Δ, φ infer Γ ⊢ Δ, when ¬φ ∈ Γ; ¬ right: from Γ, φ ⊢ Δ infer Γ ⊢ Δ, when ¬φ ∈ Δ;
- ∧ left: from Γ, φ, ψ ⊢ Δ infer Γ ⊢ Δ, when φ ∧ ψ ∈ Γ; ∧ right: from Γ ⊢ Δ, φ and Γ ⊢ Δ, ψ infer Γ ⊢ Δ, when φ ∧ ψ ∈ Δ;
- ∀ left: from Γ, φ[y/x] ⊢ Δ infer Γ ⊢ Δ, when ∀x φ ∈ Γ and y is a variable of the sort of x;
- ∀ right: from Γ ⊢ Δ, φ[y/x] infer Γ ⊢ Δ, when ∀x φ ∈ Δ, y is a variable of the sort of x, and y, as a number, is greater than every code in Γ ∪ Δ.

φ[y/x] is given by a relation Sub(x, y, φ, ψ), "ψ is φ with the free occurrences of x replaced by y, none of them inside a quantifier ∀y" (`Sub`): the least set of quadruples of numbers closed under the evident clauses. A variable that is a larger number than a code does not occur in it, so the condition in ∀ right implies the usual eigenvariable condition. The fact "Γ ⊢ Δ has a derivation of size n" is the triple of {n}, Γ, Δ, and the set of these facts is the least set closed under the rules (`derSet`, `Der`; the rules are `der_ax`, `der_negL`, `der_negR`, `der_andL`, `der_andR`, `der_allL`, `der_allR`). The size is a number of the model and may be nonstandard.

**Theorem 3.0′ (soundness)** (`soundness`; also `no_model_of_refutation`, `soundness_form`). If Γ ⊢ Δ has a derivation of some size, then in every set structure, at every assignment at which every member of Γ is true, some member of Δ is not false. If the members of Δ are decided, some member of Δ is true. If Δ is empty, no assignment in any set structure makes every member of Γ true.

*Proof.* The set of facts whose sequent is sound in a given structure is a set, by one comprehension. It is closed under the rules, so it contains the least such set. The propositional rules use the clauses for truth and for falsity of Theorem 3.0 and the fact that nothing is both true and false. The quantifier rules use two lemmas, each stated for truth and for falsity and each proved by induction on codes for a stratified condition. *Substitution* (`substitution`): if Sub(x, y, φ, ψ) and s(y) = b then ψ at s has the same truth and falsity as φ at s[x ↦ b]. *Coincidence* (`coincide`): changing an assignment at a variable that is a greater number than the code φ changes neither the truth nor the falsity of φ. For ∀ right: suppose every member of Γ is true and every member of Δ false at s. Then ∀x φ is false at s, so φ is false at s[x ↦ a] for some a. Pass to s[y ↦ a]; by coincidence Γ is still true and Δ still false there, and by coincidence and substitution φ[y/x] is false there. This contradicts the premise. ∎

The sets of numbers involved (Sub, and the set of triples (∀x φ, y, φ[y/x])) are defined by arithmetical formulas, for which the Lean file has one general comprehension and least-fixed-point theorem (`arith_comp`, `arith_lfp`).

What this theorem is not. The calculus has no cut rule, and the Lean files do not prove that it derives the same sequents as a calculus with cut, nor that the large-eigenvariable condition and capture-free substitution lose nothing. A cut rule is sound in the present sense only when the cut formula is decided, so it would need the set of well-formed codes as a further parameter; that is not done. The main proof appeals to soundness in two places, and both are stated for calculi with cut: Step 4 of §6 (the Transfer Lemma, a theorem of ZFC⁻ with a standard proof, holds in 𝔏) and Step 7 of §6 (the two typed derivations). For Step 4 the derivation is standard, so its cuts can be eliminated outside U. For Step 7 the semantic form of §5.6 argues with truth in the strand directly and does not use a soundness theorem. Neither reduction is in Lean.

### 3.2 Ladders **[Lean]**

A **ladder of height n** is a sequence of sets T₀,…,Tₙ with set relations Eᵢ ⊆ Tᵢ × Tᵢ₊₁ such that every subset of Tᵢ is the Eᵢ-extension {a : a Eᵢ b} of exactly one b ∈ Tᵢ₊₁, together with a zero and an injective successor on T₀, the zero not a successor, satisfying induction for all subsets of T₀ (`IsLadder`; the rungs are given by one set of pairs ⟨i, a⟩ with a ∈ Tᵢ, the relations by one set of triples ⟨i, a, b⟩). "Subset" means subset in U. All Tᵢ are members of one sequence, so their elements have one type, and any statement about relations among rungs is stratified.

**Lemma 3.1** (`lemma_3_1`). (a) The base of a ladder is isomorphic to ℕ by a set bijection (`ladder_base_iso`). (b) For every calm n there is a ladder of height n (`exists_ladder`; the step from n to n + 1 is `ladder_succ`).

*Proof.* (a) Dedekind: intersect all sets R ⊆ ℕ × T₀ containing (0, 0′) and closed under (k, a) ↦ (k+1, a′). (b) Let I be the set of heights of ladders; it is a set. 0 ∈ I: take T₀ = ℕ. If n ∈ I and n is calm then n+1 ∈ I: replace each rung Tᵢ by its singleton image and each Eᵢ by the induced relation; the function i ↦ {{a} : a ∈ Tᵢ} raises type, so the new sequence is indexed by T(i), i ≤ n, and T(i) = i for these i, because the calm numbers are closed downwards and fixed by T (Lemma 2.2); then put the set of all subsets of the old Tₙ on top, with {a} E b ⇔ a ∈ b. Now suppose a calm n is not in I, and let m be the least number not in I. Then 0 < m ≤ n, m−1 ∈ I and m−1 is calm, so m ∈ I. Contradiction. ∎

### 3.3 The constructible ladder **[Lean]**

**ZFC⁻** is ZFC without Power Set, with Collection and with the well-ordering principle.

**Lemma 3.2.** For every m with 3m+5 calm there is a well-founded set structure 𝔏 = (L, ε, <*) such that: 𝔏 satisfies extensionality, foundation, pairing, union, infinity, and Separation and Collection for all formulas in ε and <*; <* is a linear order of 𝔏 in which every set that has a member has a least member; the natural numbers of 𝔏 are isomorphic to ℕ; and the m-th iterated power set of ω exists in 𝔏. **[Lean: `lemma_3_2`, `lemma_3_2_calm`. The exact statement, and how it differs from this sentence, is in step (9).]**

The well-ordering principle of ZFC⁻ is here in the form of a global well-ordering <*, from which "every set has a well-ordering" follows in 𝔏 by Separation. The earlier version of this section asked for 2m+7 calm; the count in step (7) costs three rungs for each power set, not two, hence 3m+5. Nothing later depends on the exact number.

Fix a ladder of height n = 3m+5. Three consequences of fullness are used: every relation on Tᵢ is coded by a member of Tᵢ₊₁ (once pairing is available); a statement quantifying over all relations on Tᵢ is a statement about members of Tᵢ₊₁; well-foundedness of a coded relation is absolute. Every induction below is on a number ≤ n or along a set well-ordering, for a stratified condition.

**(1) Pairing.** **[Lean]** Each rung carries an injection Tᵢ × Tᵢ → Tᵢ: Cantor's on T₀; on Tᵢ₊₁, send (x, y) to the set of all (0ᵢ, a) with a ∈ x and (1ᵢ, b) with b ∈ y, for fixed 0ᵢ ≠ 1ᵢ in Tᵢ. Finite sequences are coded likewise. A structure is *coded at rung i* if its universe is a subset of Tᵢ; its relations are then members of Tᵢ₊₁.

In Lean (`exists_pairing`): every ladder of height m has a *pairing family* (`IsPairing`), a single set P of quadruples ⟨i, a, b, c⟩ that for each i ≤ m is the graph of an injection from Tᵢ × Tᵢ into Tᵢ. The proof is an induction on i ≤ m for a stratified condition; the step is `pairing_succ`, the base `pairing_zero`, and each rung has two different members by `rung_two`. With it, every set relation on Tᵢ is coded by a member of Tᵢ₊₁, whose members are the pairs of the relation (`rel_code`), and the relation coded by a member of Tᵢ₊₁ is a set (`rel_decode`). Finite sequences (`exists_seq`, `nth_fun`, `seq_code`): with the pairing of rung j every member t of the rung is read as a sequence, whose entry 0 is a if t is the pair (a, t′) and whose entry n + 1 is the entry n of t′. The relation "the entry n of t is a" is a set, entries are unique, and for every number n of the model and every set g that has a value in Tⱼ at each k < n, some member of Tⱼ has a value of g at k as its entry k for all k < n. The number n may be nonstandard.

**(2) Hartogs.** **[Lean]** Let ηᵢ be the set of isomorphism classes of well-orderings of subsets of Tᵢ, ordered by length. It is a well-ordering coded at rung i+2. For a well-ordering w of a subset of Tᵢ, the map sending a point of w to the class of the initial segment below it is a set (it is a relation between Tᵢ and Tᵢ₊₂, defined from the Eᵢ) and is an isomorphism of w onto a proper initial segment of ηᵢ. Hence ηᵢ does not inject into Tᵢ, so into no shorter ordinal: ηᵢ is an **initial ordinal of U**. Also ηᵢ < ηᵢ₊₂. Initial ordinals are closed under ordinal sum and product, by Gödel's ordering of pairs, without Choice.

In Lean this has two parts. The first is about well-orderings that are sets, in any model of NFU. A well-ordering is a set r of pairs, reflexive on its field, such that every set meeting the field has a least member (`IsWO`). A *partial isomorphism* from r to s is a set of pairs that is an order isomorphism between an initial segment of r and an initial segment of s (`PIso`). Two partial isomorphisms between well-orderings agree where both are defined (`piso_agree`, by a least counterexample). The union of all of them is a set and is the largest one, and it is defined on all of r or onto all of s: this is comparability (`wo_compare`). r *embeds* in s if some partial isomorphism is defined on all of r (`Emb`); this is reflexive, transitive and total on well-orderings (`emb_refl`, `emb_trans`, `emb_total`). A partial isomorphism defined on all of s is onto r or onto the predecessors of a point of r (`piso_onto_or_seg`, `SegOf`), and a well-ordering is not isomorphic to the predecessors of one of its points (`not_segOf_self`). Among the well-orderings satisfying a condition there is one that embeds in all the others, provided a certain set of points exists (`wo_min`).

The second part is the theorem (`hartogs`): in a ladder of height m with a pairing family, for every i with i + 2 ≤ m there is a set well-ordering H whose points are members of Tᵢ₊₂ such that

- every set well-ordering w of a subset of Tᵢ embeds in H and H does not embed in w;
- the predecessors of every point of H are isomorphic to a set well-ordering of a subset of Tᵢ.

H is built as in the text: the members of Tᵢ₊₁ that code well-orderings, compared by `Emb`, give a set preorder; the classes are the members of Tᵢ₊₂ whose members are the codes equivalent to a given one; H orders the classes. It is a well-ordering by `wo_min` (`isWO_H`). The map of the text is `exists_segMap`, and `segMap_spec` shows it is an isomorphism of w onto the predecessors of the class of w. Consequently no set maps the field of H injectively into Tᵢ (`hartogs_no_inj`; the well-ordering is transported along the injection by `wo_transport`). ηᵢ < ηᵢ₊₂ is the first property of `hartogs` at i + 2 applied to the H of rung i. Closure under sum and product: for two set well-orderings of subsets of Tᵢ, their sum (two tagged copies, `wo_sum`) and their lexicographic product (on pairs, `wo_lex`) are set well-orderings of subsets of Tᵢ; so by `hartogs` each embeds in H and not conversely, and by `seg_of_strict` each is isomorphic to the predecessors of a point of H. Since the predecessors of any point of H are isomorphic to a well-ordering of a subset of Tᵢ, this is closure of the ordinals below ηᵢ under sum and product. The combined statement about points of H is not written as one Lean theorem.

**(3) The hierarchy.** Let W be a well-ordering coded at rung i. The constructible hierarchy along W is built from *names*: a name of rank α is a triple (α, number of a formula, finite sequence of names of smaller rank); names are finite objects over W and ℕ, so they are coded at rung i. By recursion along W one defines when two names denote the same set and the relation ε, so that the names of rank α denote exactly the subsets of L_α = {names of rank < α} definable over (L_α, ε) with parameters; satisfaction over L_α is a set by §3.1. Keeping the least name of each set gives the structure L_W and its canonical well-ordering <_L. Existence and uniqueness are by induction along W.

**In Lean for this step.** The tools: the least number principle and the natural numbers as a set well-ordering (`nat_least`, `isWO_natLe`), and **recursion along a set well-ordering** (`wo_rec`): let r be a set well-ordering and Φ(α, y, G) a condition given by a stratified formula; then there is a set F of pairs with ⟨α, y⟩ ∈ F if and only if α is a point of r and Φ(α, y, F↾α), where F↾α is the set of pairs ⟨β, z⟩ ∈ F with β strictly below α.

The hierarchy is defined in Lean in a form that differs from the paragraph above in three ways; the differences make the recursion a single one.

- *Names without well-formedness.* Fix a rung j, a set well-ordering θ of members of Tⱼ, and an injection n ↦ n̂ of ℕ into Tⱼ (`exists_numerals`). A **name of rank β** is any member of Tⱼ of the form (β, (φ̂, u)), with β a point of θ, φ a number (a formula) and u any member of Tⱼ, read as the sequence of parameters by step (1) (`RankIs`). The **value** of the variable i under t ∈ Tⱼ at stage α is the entry i of t if that is a name of rank below α, and a fixed default name d of least rank otherwise (`ValRaw`). So no recursion is needed to say what a name is.
- *Truth for all stages and formulas at once.* The recursion (`wo_rec`) runs along the lexicographic product of θ and ℕ with a top point ⊤ added. At the point (α, ĉ) it defines the set of t ∈ Tⱼ such that the formula c is true at stage α under t (`TrueAt`). The members of the name (β, (φ̂, u)) are the names a of rank below β such that φ is true at stage β under the sequence (a, u) (`EpsRaw`, `eps_iff`). So a name of rank β denotes the set of names of rank below β that satisfy φ with the parameters u, over the structure of names of rank below β.
- *No quotient; "denote the same set" is part of the recursion.* Different names may denote the same set, and they may have different ranks. At the point (γ, ⊤) the recursion defines, for names a, a′ of ranks at most γ, one of them of rank γ, when a and a′ **denote the same set**: every member of a denotes the same set as some member of a′, and conversely (`SimRaw`, `hier_sim`). The atomic formula v ε w means: some name that denotes the same set as the value of v is a member of the value of w (`EpsStarRaw`). The language has no equality.

The third point matters. In a first version atomic formulas meant "the value of v is a member of the value of w" for names as such. Membership in a name of rank β requires rank below β, so two names with the same members and different ranks could be told apart by a formula, and the levels were not those of L. That version was replaced.

The data and the solution of the recursion exist for every rung with a pairing and every nonempty θ (`exists_hierData`, `HierData`). The clauses, each a Lean theorem about any such solution, for α a point of θ:

- r(v, w) is true at stage α under t ⇔ the set denoted by the value of v is a member of the set denoted by the value of w, in the sense just given (`hier_rel`);
- ¬c is true ⇔ c is not true (`hier_neg`); c ∧ c′ is true ⇔ both are (`hier_and`);
- ∀v c is true under t ⇔ c is true under every t′ whose values at the variables up to the code agree with those of t, except that its value at v is an arbitrary name of rank below α (`hier_all`);
- a and a′ denote the same set ⇔ every member of a denotes the same set as a member of a′, and conversely (`hier_sim`).

A number that is not a code of one of the four shapes is never true (`trueAt_shape`). The following facts are proved in Lean for any such solution.

- **Coincidence** (`coin_hier`): the truth of c at a stage depends only on the values of the variables up to its code. With the existence of the sequence "t with v changed" (`exists_upd`, from step (1)) the quantifier clause takes Tarski's form: ∀v c is true under t ⇔ for every name a of rank below α, c is true under t with v changed to a (`hier_all_ex`).
- **Transitivity of the levels** (`eps_rank`): the members of a name of rank below α are names of rank below α. The members of the name (β, (φ̂, u)) are exactly the names a of rank below β with φ true at stage β under (a, u) (`eps_iff`).
- **"Denote the same set" is an equivalence relation** on names (`sim_refl`, `sim_symm`, `sim_trans`; inductions on the rank of the first name, by least counterexample in θ).
- **It is a congruence** (`inv_hier`): if the values of the variables up to the code of c under t and under t′ denote the same sets, then c is true under t if and only if it is true under t′. Membership between denoted sets respects it (`epsStar_congr`).
- **Extensionality** (`sim_iff_ext`): two names denote the same set if and only if the same things are members of the sets they denote.
- **Equality is definable** (`hier_eq`, `hier_eq_sim`): for variables whose values are names a, b of rank below α, the formula ∀z (z ε v ↔ z ε w) is true at stage α if and only if a and b denote the same set. The clauses for ∨, ↔ and ∃ are `hier_or`, `hier_iff`, `hier_ex`.
- **The names of rank α denote the definable subsets of the level** (`def_name`, with `eps_iff`): for every stage α, every formula φ and every u in the rung there is a name of rank α whose members are exactly the names a of rank below α such that φ is true at stage α under (a, u); and every name of rank α is of this form.
- **The levels increase** (`up_name`): a name of rank below α denotes the same set as some name of rank α. **Each level is a member of the later ones** (`level_name`, `level_mem`): for β below α there is a name of rank β, hence of rank below α, whose members are exactly the names of rank below β.
- **Pairs and unions** (`pair_name`, `union_name`): for names a, b of rank below α there are names of rank α that denote {a, b} and ⋃b. Call a stage λ of θ a **limit** if above every stage below λ there is another stage below λ (`IsLim`). **Limit levels are closed under pairs and unions** (`pair_lim`, `union_lim`).
- **Ordered pairs** (`opair_lim`, `opair_inj`): limit levels are closed under the ordered pair {{a}, {a, b}}, and two ordered pairs denote the same set only if their components do.
- **Foundation** (`eps_wf`): every set of U that contains a name and is closed under "denote the same set" has a member b such that no member of the set denotes a member of the set denoted by b. In particular no name denotes a member of the set it denotes (`epsStar_irrefl`).
- **Bounded formulas are absolute between the levels** (`d0_abs`). A set D of codes is a set of *bounded formulas* if each member is atomic, or the negation or conjunction of members, or of the form ∀v (v ε w → c) with c a member and v ≠ w (`IsD0`; such sets are built by `isD0_empty`, `isD0_insert`). Let γ be a stage above the least one, α a later stage, c ∈ D, and t a sequence whose values at the variables up to c are the same at the two stages. Then c is true at stage γ under t if and only if it is true at stage α under t. The proof is an induction on codes; the quantifier step uses that "denote the same set" is a congruence and that the members of a name of rank below γ are denoted by names of rank below γ.
- **Separation for bounded formulas at limit levels** (`sep_d0`, `bound_lim`, `sep_lim`). Finitely many names of rank below a limit stage λ, in the sense of the model (the entries up to n of a sequence, n a number of U), have rank below a common stage below λ. Hence: for a limit stage λ, a stage β below it, a bounded formula c and a sequence u of parameters, there are a stage γ with β ≤ γ < λ and a name of rank below λ whose members are the names x of rank below γ such that c is true *at stage λ* under (x, u). Taking c of the form v₀ ε v₁ ∧ c′ and γ above the rank of the value of v₁ gives the usual statement.
- **The ordinals of the hierarchy** (`ordName_mem`, `ordN_ordName`, `ordName_members`, `ord_is_ordName`, `ordName_lt`, `ordName_inj`). Say that a name denotes an *ordinal* if the set it denotes is transitive and all its members are transitive (`OrdN`); this is expressed by a bounded formula (`cOrd`, `hier_ordN`). For a stage ξ let o_ξ be the name of rank ξ given by that formula, so that its members are the names of rank below ξ that denote ordinals. Then: o_ξ denotes an ordinal; every member of o_ξ denotes the same set as o_ζ for some ζ below ξ; o_ζ is a member of the set denoted by o_ξ if and only if ζ is strictly below ξ; o_ζ and o_ξ denote the same set only if ζ = ξ; and every name of rank ρ that denotes an ordinal denotes the same set as o_ξ for some ξ ≤ ρ. So the ordinals of L_α are the o_ξ with ξ below α, ordered as the stages: L_α ∩ Ord = α.
- **Each level is a set structure in the sense of §3.1, and the two truth definitions agree** (`hier_structure`, `exists_asg_of_seq`, `level_models`). Let α be a stage above the least one. Let U_α have every sort equal to the set of names of rank below α, and let E_α interpret every relation symbol as membership between the denoted sets. Then (U_α, E_α) is a set structure; every sequence t has an assignment s with the same values; and for every code c that the structure decides (in particular every code built from atomic formulas by ¬, ∧ and ∀ over variables of the form used in §3.1), c is true at s in the sense of §3.1 if and only if c is true at stage α under t. The proof is an induction on codes; in general it gives: true at s implies true at stage α, and false at s implies not true at stage α.
- **Successor and limit stages** (`exists_succ_stage`, `ordName_zero`, `ordName_succ`, `ordName_lim`). Above every stage that is not the last there is a least stage. The ordinal name of the least stage denotes the empty set; o_{ζ+1} denotes o_ζ ∪ {o_ζ}; and for a limit stage λ, every member x of o_λ has its successor x ∪ {x} among the members of o_λ.
- **Axioms as coded sentences** (`hier_ext`, `hier_found`, `hier_pairing`, `hier_union`, `hier_inf`; `limit_level_axioms`, `level_infinity`, `limit_level_zf0`). Write x ≈ y for the formula ∀z (z ε x ↔ z ε y). The sentences are: extensionality, ∀x∀y (x ≈ y → ∀w (x ε w → y ε w)); foundation, ∀a (∃x x ε a → ∃x (x ε a ∧ ∀y (y ε x → ¬ y ε a))); pairing, ∀a∀b∃c∀x (x ε c ↔ (x ≈ a ∨ x ≈ b)); union, ∀b∃c∀x (x ε c ↔ ∃y (x ε y ∧ y ε b)); infinity, ∃w (∃e (e ε w ∧ ∀u ¬ u ε e) ∧ ∀x (x ε w → ∃y (y ε w ∧ ∀u (u ε y ↔ (u ε x ∨ u ≈ x))))). Extensionality and foundation are true at every stage. Pairing and union are true at every limit stage. Infinity is true at every stage above a limit stage that is not the least stage; the witness is the ordinal name of that limit stage. With the agreement of the two truth definitions, for a limit stage λ that is not the least the first four hold in (U_λ, E_λ) in the sense of §3.1, and infinity holds in (U_α, E_α) for α above such a λ; so all five hold in (U_α, E_α) when α is itself a limit stage above such a λ. The statements are for the assignment that comes from a fixed sequence; that a sentence has the same truth value at all assignments is not proved here.

So the names of rank below α, taken up to "denote the same set", with membership between denoted sets, form an extensional well-founded structure whose ordinals are the stages below α, truth at stage α is truth in that structure in the sense of §3.1, and the names of rank α denote exactly its subsets that are definable with parameters. This is the recursion that defines L_α.

Three remarks on what these Lean statements are. First, the structure (U_α, E_α) is the structure of names, with "denote the same set" as a congruence; the quotient is not formed. Second, the least stage is excluded from `hier_structure` because its level is empty and a one-sorted structure of §3.1 with an empty sort has no assignments. Third, the statements about limit stages are about any limit stage of any θ. That such stages exist is proved for the Hartogs well-ordering of a rung: it has a limit stage that is not the least, namely the point whose predecessors are the image of ℕ (`exists_limit_stage`, `hartogs_limit`), and above every stage it has a limit stage (`limit_above`; the stage whose predecessors are a copy of the predecessors of the given stage followed by a copy of ℕ) and a good stage, that is, a limit stage that is a limit of limit stages (`IsGood`, `good_above`; the predecessors are a copy of the predecessors of the given stage followed by ℕ × ℕ in the lexicographic order). These are the multiples of ω², the good δ of the text below. Putting the pieces together (`exists_zf0_level`): in every ladder with a pairing and rungs i, i+1, i+2, the hierarchy along the Hartogs well-ordering of rung i, with names in rung i+2, has a limit level whose set structure satisfies extensionality, foundation, pairing, union and infinity in the sense of §3.1, and the level can be taken at a good stage (`exists_good_level`). The stages below the first limit stage of the Hartogs well-ordering are the numbers of U: there is a set function that is an isomorphism of (ℕ, ≤) onto them (`exists_omega_stage`), so the members of the ordinal name of that stage are the ordinal names o_ξ with ξ the stage numbered by a number of U (`omega_members`). This is the form in which "the numbers of the constructible structure are the numbers of U" is available; the statement of step (9), about the map defined by recursion inside the structure, has not been derived from it.

**The rest of the argument does not follow the textbook route.** The textbook proof of Lemma 3.2 codes satisfaction over a level inside later levels, defines Skolem hulls there, and works with the cardinals of L. Coding satisfaction inside the levels would need formulas and assignments as members of the levels and a second truth definition for them. The Lean proof avoids this. The canonical well-ordering is made a relation symbol of the hierarchy; a hull is a set of names, a set of U, closed under rules that are stated with the truth definition of step (3) directly; condensation is proved for such sets on the side of U; and in place of the next cardinal of L there is "the least stage that is not small over ν". Steps (4)–(9) are what Lean proves; they are in `ConNF/NF/NFUConstr.lean`.

**(4) The canonical order.** **[Lean]** The hierarchy of step (3) has two more relation symbols than ε. The atomic formula with relation symbol 2 means "the set denoted by the first value comes before the set denoted by the second in the canonical well-ordering" (`Lt`, `hier_lt`): names are ordered by rank, then formula number, then lexicographically by their parameters (`IsPrec`, `pr_iff`); this order is a total preorder in which every set containing a name has a least member (`pr_total`, `pr_trans`, `pr_least`, by a lexicographic-minimum lemma `lex_min` proved by induction on a number of the model); names that are each at most the other denote the same set (`tie_sim`); the least names are the *canonical names* (`IsCan`, `exists_can`, `can_vals`); and the induced relation on the denoted sets is a well-ordering (`lt_tri`, `lt_least`). The relation symbol 1 was meant for satisfaction at earlier stages; it is not used, and when the hierarchy is built with an empty oracle, as it is in step (8), it is never true (`hier_T_false`). Whether the structure is still L is discussed in remark 8 of step (9); it is not proved in Lean and not needed. Every other relation symbol means membership, as before.
- *Hulls and condensation, on the side of U.* Satisfaction is not coded inside the levels. A hull is a set of names closed under six rules (`ClosedR`): the marker of the rank of a member; the values of the parameters of a member; every name whose rank has its marker in the set and whose parameters have values in the set; the canonical names; the least witnesses, at the top stage and at every stage whose marker is in the set, for every formula and both truth values; and a rule that brings in the generators recorded for small stages (`IsSig`, `Gen`, `Small`). For a set N of names closed under the rules, the stages whose markers are in N are collapsed (`IsColl`), the collapse is extended to names (`IsPi`, `PiRel`), and **condensation** is proved (`cond_all`): the collapsing map is defined exactly on N (`pi_mem`, `pi_tot`), preserves the order of the names (`pi_pr`), "denote the same set" and membership in both directions (`step_sim`, `step_eps`), is onto the level at the collapsed stage up to "denote the same set" (`step_surj`), preserves canonical names and the canonical well-ordering (`step_can`, `step_can_img`, `step_lt`), and every formula is true at a stage of N under a sequence with values in N if and only if it is true at the collapsed stage under the images (`step_elem`). The quantifier case is the Tarski–Vaught test, which holds because N contains least witnesses (`cond_lw_pos`, `cond_lw_neg`).

**(5) Hulls and condensation.** **[Lean]** Satisfaction is not coded inside the levels. A hull is a set of names closed under six rules (`ClosedR`): the marker of the rank of a member; the values of the parameters of a member; every name whose rank has its marker in the set and whose parameters have values in the set; the canonical names; the least witnesses, at the top stage and at every stage whose marker is in the set, for every formula and both truth values; and a rule that brings in the generators recorded for small stages (`IsSig`, `Gen`, `Small`). For a set N of names closed under the rules, the stages whose markers are in N are collapsed (`IsColl`), the collapse is extended to names (`IsPi`, `PiRel`), and **condensation** is proved (`cond_all`): the collapsing map is defined exactly on N (`pi_mem`, `pi_tot`), preserves the order of the names (`pi_pr`), "denote the same set" and membership in both directions (`step_sim`, `step_eps`), is onto the level at the collapsed stage up to "denote the same set" (`step_surj`), preserves canonical names and the canonical well-ordering (`step_can`, `step_can_img`, `step_lt`), and every formula is true at a stage of N under a sequence with values in N if and only if it is true at the collapsed stage under the images (`step_elem`). The quantifier case is the Tarski–Vaught test, which holds because N contains least witnesses (`cond_lw_pos`, `cond_lw_neg`).

**(6) Small stages, absorption, Separation and Collection.** **[Lean]** Fix a stage ν. A stage ρ above ν is *generated* from ν and a name b of rank below ρ when every set of names that contains the names of rank below ν, the name b and the default name, and is closed under the six rules at ρ, contains every name of rank below ρ (`Gen`); a stage is *ν-small* when some stage at or above it is generated (`Small`); κ is the least stage that is not ν-small (`IsNext`). Proved: κ is a limit stage above ν (`next_lim`, `next_gt`); the collapse of a hull taken at a stage δ above κ is generated, so the collapsed stage is small (`hull_collapse`); **absorption** (`next_absorb`): a name of any rank below δ all of whose members are denoted by names of rank below some fixed stage below κ denotes the same set as a name of rank below κ; **Separation at κ in semantic form** (`next_sep`): for every formula number, sequence and name a of rank below κ there is a name of rank below κ whose members are exactly the members y of a at which the formula is true at κ; **Collection at κ in semantic form** (`next_coll`): if for every member y of a there is a name z of rank below κ at which the formula is true at κ, then there is one stage γ below κ such that z can always be taken of rank below γ.

As coded sentences (`cSep`, `hier_sep`; `cColl`, `hier_coll`): for every code φ, every variable a other than v₀ and every variable b larger than the code of v₀ ε a ∧ φ, the sentence ∀a ∃b ∀v₀ (v₀ ε b ↔ (v₀ ε a ∧ φ)) is true at κ under every sequence; and for every code φ, variables a, y, z and a variable b larger than φ and different from a, y, z, with a ≠ y, the sentence ∀a (∀y (y ε a → ∃z φ) → ∃b ∀y (y ε a → ∃z (z ε b ∧ φ))) is true at κ under every sequence. The witness b for Collection is the level at the stage γ given by `next_coll`. A variable larger than a code does not occur in it; that is how "b is not free in φ" is said. The canonical order, as coded sentences true at every stage (`hier_wlin`, `hier_wirr`, `hier_wtrans`, `hier_wcong`, `hier_wleast`): ∀x∀y (x <* y ∨ x ≈ y ∨ y <* x); ∀x ¬ x <* x; ∀x∀y∀z (x <* y → y <* z → x <* z); ∀x∀y (x ≈ y → ∀w ((x <* w → y <* w) ∧ (w <* x → w <* y))); and ∀a (∃x x ε a → ∃x (x ε a ∧ ∀y (y ε a → ¬ y <* x))).

**(7) The count.** **[Lean]** A lower rung of a ladder maps one-to-one into every higher rung (`rung_lift`, by induction on the height with the singleton map). The members of a generated stage are counted by **terms**: a term is a tuple, in a rung i, of a tag, an arity, a number, an atom and a sequence of terms; the tag selects one of thirteen rules (`RuleR`): an atom for a stage below ν, the generator, the default name, and the six rules for hulls, the rule for least witnesses in four forms and the rule for recorded generators in two. The evaluation relation is the least relation closed under the rules (`EvData`, `exists_evSet`, `ev_step`, `ev_inv`). Each rule is a function up to the order of names (`rule_fun`), so evaluation is (`ev_fun`); the set of values of terms is closed under the six rules and contains the names of rank below ν, the generator and the default name (`evX_closed`, `evX_all`); so if ρ is generated from ν, every name of rank below ρ is the value of a term. Sending a stage below ρ to the set of terms that evaluate to its marker gives: **if the stages below ν map one-to-one into the rung i, the stages below a stage generated from ν map one-to-one into the rung i+1** (`gen_small`, `gen_count`). With the Hartogs well-ordering of the rung i+1, which lives on the rung i+3, this gives (`next_exists`): if the well-ordering of the stages is longer than every well-ordering of a part of a rung L with i+3 ≤ L, then the least stage κ that is not ν-small exists, and the stages below κ map one-to-one into the rung i+3.

This is the only place where sizes in U are compared, and it is where the height of the ladder is used. A generated stage is counted in the rung i+1 because a stage is sent to the *set* of the terms that evaluate to its marker; choosing one term would need a well-ordering of the terms, which was not constructed. The comparison with the Hartogs well-ordering of the rung i+1 costs two more rungs.

**(8) The sequence of stages, the power sets, the numbers.** **[Lean]** Let L = 3(m+1), let θ be the Hartogs well-ordering of the rung L, whose points are members of the rung L+2 = 3m+5, and build the hierarchy of step (3) along θ with names in the rung L+2 and with an empty oracle for the symbol 1. Let ν₀ be the first limit stage of θ. The stages below ν₀ are the numbers of U (`exists_omega_stage`), so they map one-to-one into the rung 0.

*The stages* (`stage_seq_raw`, `StageSeq`, `exists_stageSeq`). By induction on k ≤ m+1, for a stratified condition, there is a set W that assigns to each i ≤ k a stage νᵢ and a name Pⁱ such that: νᵢ₊₁ is the least stage that is not νᵢ-small; the stages below ν_k map one-to-one into the rung 3k; P⁰ is the ordinal name of ν₀; and Pⁱ⁺¹ is the name of rank νᵢ₊₁ given by the formula ∀z (z ε v₀ → z ε v₁) with the parameter Pⁱ, so that its members are the names x of rank below νᵢ₊₁ every member of which is a member of Pⁱ (`sub_name_mem`). The step is `next_exists` with i = 3k, which needs 3k + 3 ≤ L. Put κ = ν_{m+1}. Then ν₀ < ν₁ < … < κ, every νᵢ₊₁ is a limit stage, and Pⁱ has rank νᵢ, which is below κ for i ≤ m (`sat_lt`, `top_lim`, `sat_rank`, `sat_inN`).

*The power sets* (`pow_of_next`, `PowNames`, `exists_powNames`). For i < m and every name x of rank below κ: x denotes a member of the set denoted by Pⁱ⁺¹ if and only if every member of the set denoted by x is a member of the set denoted by Pⁱ. From left to right this is the definition of Pⁱ⁺¹. From right to left it is absorption at νᵢ₊₁: the members of x are members of Pⁱ, so they are denoted by names of rank below νᵢ; hence x denotes the same set as a name of rank below νᵢ₊₁, and that name is a member of Pⁱ⁺¹.

*The numbers* (`NumNames`, `exists_numNames`). Let N be the isomorphism of the numbers of U onto the stages below ν₀ and let ω̂ = o_{ν₀} = P⁰. The map i ↦ o_{N(i)} is one-to-one up to "denote the same set"; its values are, up to that relation, exactly the members of ω̂; o_{N(0)} has no members; and the members of o_{N(i+1)} are the members of o_{N(i)} together with o_{N(i)}.

*The sequence as a member of the level* (`exists_inner_seq`). By induction on k ≤ m there is a name of rank below κ whose members are exactly, up to "denote the same set", the ordered pairs ⟨o_{N(i)}, Pⁱ⟩ with i ≤ k. The step adds one pair, by closure of limit levels under pairs and unions; that two names for the ordered pair of the same sets denote the same set is `opairN_congr`.

**(9) Lemma 3.2 as a Lean theorem.** **[Lean: `Lemma32`, `lemma_3_2`, `lemma_3_2_calm`, `l32_holds`, `l32_sep_holds`, `l32_coll_holds`]**

*Statement.* In every model of NFU + Infinity, over every ladder of height n ≥ 3(m+1)+2, there are a pairing family, a well-ordering θ of members of the rung 3(m+1)+2, a solution of the recursion of step (3) along θ, a limit stage κ of θ, and sets U_κ, E_κ, Nm, Pw of U and names ω̂, s of rank below κ, such that the following hold.

(a) (U_κ, E_κ) is the level at κ as a set structure in the sense of §3.1: every sort is the set of names of rank below κ, and E_κ interprets the symbols as in step (3). For every code c, every assignment s′ and every sequence t with the same values at the variables up to c: if c is true in the structure at s′ then c is true at κ under t, and if c is false in the structure at s′ then c is not true at κ under t.

(b) These are true at κ under every sequence: extensionality, foundation, pairing, union and infinity, in the forms of step (3); every instance of Separation and every instance of Collection, in the forms of step (6), for arbitrary codes φ; and the five sentences of step (6) about <*. No atomic formula with the symbol 1 is true.

(c) Every set of U that contains a name of rank below κ and is closed under "denote the same set" has a member b such that no member of the set denotes a member of the set denoted by b.

(d) Nm is the map i ↦ o_{N(i)} of step (8), with the four properties stated there, and ω̂ has rank below κ.

(e) Pw assigns to each i ≤ m a name of rank below κ; Pw(0) = ω̂; and for i < m and every name x of rank below κ, x denotes a member of the set denoted by Pw(i+1) if and only if every member of the set denoted by x is a member of the set denoted by Pw(i).

(f) The members of s are exactly, up to "denote the same set", the ordered pairs ⟨Nm(i), Pw(i)⟩ with i ≤ m.

`lemma_3_2_calm`: if 3(m+1)+2 is calm, then by Lemma 3.1 (`lemma_3_1`) a ladder of that height exists, and so do all of the above.

*From truth at κ to truth in the structure* (`l32_holds`). Let c be a code that the structure decides, that is, at every assignment it is true or false in the sense of §3.1 (`Form`; this holds for every code built from atomic formulas by ¬, ∧ and ∀ over variables of the form used in §3.1). If c is true at κ under every sequence, then c is true in (U_κ, E_κ) at every assignment all of whose values are names of rank below κ. So each sentence of (b) with variables of that form holds in the structure at every such assignment; for Separation and Collection this is written out (`l32_sep_holds`, `l32_coll_holds`), for every φ that the structure decides.

*Proof.* The ladder has a pairing family (`exists_pairing`). θ is the Hartogs well-ordering of the rung 3(m+1) (`hartogs`); it has a first limit stage ν₀, which is not its least stage (`exists_omega_stage`), and no last stage (`limit_above`). The hierarchy exists along θ (`exists_hierData`, with the empty set as the oracle); it has markers (`exists_isMark`) and a record of generators (`exists_sig`). Step (8) gives the stages, κ, Pw, Nm and s. κ is a limit stage above ν₀, so (a) is `hier_structure`, and extensionality, foundation, pairing, union and infinity are `hier_ext`, `hier_found`, `hier_pairing`, `hier_union`, `hier_inf`. κ is the least stage that is not ν_m-small, and there are two stages of θ above it, so Separation and Collection are `hier_sep` and `hier_coll`. The sentences about <* are true at every stage. (c) is `eps_wf`. ∎

*What this statement is, compared with the sentence at the head of the section.*

1. *The language.* 𝔏 is a structure for ε and <* (and the symbol 1, which is never true). Separation and Collection are for all codes φ in that language, where a code is any number of U, standard or not. A number that is not the code of a formula is never true, and the instances for it are true for trivial reasons.
2. *The well-ordering principle.* What Lean proves is that <* is a linear order of 𝔏, compatible with ≈, in which every set that has a member has a least member. That every set of 𝔏 has a well-ordering that is a member of 𝔏 follows from this inside 𝔏 (form a × a by Collection and cut out <* on it by Separation). This last derivation is ordinary reasoning in the theory and is not carried out in Lean. For the use in §4.3 a definable global well-ordering is what is wanted.
3. *The iterated power sets are given from outside.* (e) and (f) say that there are members P⁰, …, Pᵐ of 𝔏, each the power set of the one before in the sense of 𝔏, with P⁰ the set of numbers of 𝔏, and a member of 𝔏 whose members are the pairs ⟨i, Pⁱ⟩. The single sentence of set theory "there is a function f on m+1 with f(0) = ω and f(i+1) the power set of f(i)" is not written as a coded sentence and evaluated in 𝔏. When m is standard the two are the same thing; when m is not, (f) is the form in which the sequence is available to an argument inside U.
4. *The numbers.* (d) is the statement "the natural numbers of 𝔏 are isomorphic to ℕ": the finite ordinals of 𝔏 are the o_{N(i)}, in the order of the numbers i of U.
5. *Names, not sets.* As in step (3), the structure is the structure of names, with "denote the same set" as a congruence; the quotient is not formed.
6. *Separation has its comprehension variable fixed* as the variable 0, and b must be larger than the code of the formula. Every instance of the scheme has a variant of this form by renaming bound variables; the renaming is not formalised.
7. *Assignments.* Truth at κ is proved under every sequence. For the structure in the sense of §3.1 it is transferred to the assignments whose values are all members of the structure. An assignment of §3.1 is only required to have such values at the numbers that are variables.
8. *Is 𝔏 a level of L?* The hierarchy is the constructible hierarchy for the language with <*. In ZF I expect its limit levels to be those of L, because the canonical well-ordering of a limit level is definable over it in the usual way, and I expect the least stage that is not ν-small to be the successor cardinal of ν in the sense of L. Neither is proved here, and I have not checked them in detail; neither is used: nothing later needs to know that 𝔏 is L.

The stages ν₁ < ν₂ < … do the work that the cardinals of L do in the textbook proof. Lean never speaks of cardinals of L; the only comparison of sizes is the one in step (7), in U.

---

## 4. Tangles

### 4.1 Definition

A **tangle with n sorts** is a set structure with sorts τ₀,…,τ_{n−1}, a membership relation ∈_{j,i} ⊆ τⱼ × τᵢ for each j < i, satisfying extensionality for each pair j < i and the typed forms of the existence axioms of NF₀ for every descending chain of sorts. For an increasing sequence h = (h₀ < … < h_k) of sorts, the **strand** 𝔗[h] is the typed structure with sorts τ_{h₀},…,τ_{h_k}, membership ∈_{hᵢ,hᵢ₊₁} between consecutive ones, and true equality. Every stratified typed version of an axiom of NF₀ with types in {0,…,k} holds in every strand. Every sort with two sorts below it is nonempty (by the axiom for the set of all singletons).

### 4.2 The Lean theorem **[Lean]**

*Not on the path to the theorem (see the status paragraph).*

`exists_finite_tttModel`: for every D there is a tangle with D+1 sorts, each of size at most ℶ_{D+4}. It is obtained from the con-nf formalisation of the Holmes–Wilshaw construction by replacing "Λ has no maximum, μ is a strong limit" by "Λ is finite, μ^{<κ} = μ, and there are cardinals θ_β < μ, closed under powers below κ, with 2^κ ≤ θ_β and 2^{θ_γ} ≤ θ_β for γ < β", and instantiating κ = ℵ₁, θᵢ = ℶᵢ₊₃, μ = ℶ_{D+4}.

### 4.3 The Transfer Lemma **[inspection]**

*Not needed any more: §4.5 proves what this lemma asserted, in the form the proof uses.*

**Transfer Lemma.** There is a standard c such that ZFC⁻ proves: for every D, if the c·(D+1)-th iterated power set of ω exists, then there is a tangle with D+1 sorts.

This is the one step that is not a proof in the strict sense. The Lean theorem is a theorem of Lean's type theory. What is needed is a derivation in ZFC⁻ in which D is a variable, because §6 applies it inside 𝔏 at a height that may be nonstandard. No general theorem turns a Lean proof into such a derivation: Lean's logic is stronger than ZFC⁻ with boundedly many power sets, so the conversion depends on what the particular proof uses. The grounds for the lemma are these.

1. *Uniformity.* The Lean proof is one proof for all D. The height enters only through the instance of the parameter class; everything else is proved for an arbitrary finite Λ.
2. *Where the objects live.* The construction defines a fixed list of kinds of object from Λ, κ, μ: atoms, litters, near-litters, base and structural permutations, paths, trees, enumerations, supports, structural sets, codes, the sets and permutations of each new level, tangles, coding functions, specifications and the auxiliary objects of the counting. Each is formed by products, function spaces with countable or level-indexed domains, subsets, quotients, finite sequences and power sets, and power sets are nested once per level. With μ = ℶ_{D+4} everything at height D lies within about 2D + d power sets of ω, for a small standard d.
3. *Recursion.* The levels are built by recursion on the finitely many elements of Λ. In ZFC⁻, once the bounding power set exists, this is a recursion of length D+1 inside a set, justified by induction on numbers for arbitrary formulas. Inside each level the proofs use well-founded induction on sets (positions, supports), which ZFC⁻ has.
4. *Cardinal arithmetic.* The facts about ℵ₁ and the ℶₙ used in the instance (regularity of ℵ₁, König's inequality, (2^λ)^{ℵ₀} = 2^λ) and the general cardinal arithmetic used in the counting concern cardinals within the same bound and are theorems of ZFC⁻ once the relevant power sets exist.
5. *Choice.* Lean's choice principle is applied to sets within the bound. ZFC⁻ has the well-ordering principle; 𝔏 even has a definable well-ordering.

What has not been done: the roughly two thousand lemmas of the formalisation, and the parts of Mathlib they rest on, have not been examined one by one for uses of the universe that exceed bounded rank. A rigorous version would be either a formalisation of the finite-height construction in a system with a known interpretation in ZFC⁻ with boundedly many power sets (higher-order logic of order c·(D+1), with D a variable), or a metatheorem for the fragment of Lean actually used. Neither exists.

The exact value of c is irrelevant below: any bound elementary in D would serve, since calm numbers are closed under exponentiation.

### 4.4 The Lean formalisation of §4.1 **[Lean]**

*Not on the path to the theorem.*

File `ConNF/NF/Tangle.lean` (1,361 lines; it depends on the con-nf development, so it is not standalone). No `sorry`, replayed in the kernel checker, axioms `propext`, `Classical.choice`, `Quot.sound` only. Build with `lake build ConNF.NF.Tangle`.

**The axioms as formulas.** `nfAxioms` is a list of seventeen sentences: four equality axioms (reflexivity, the Euclidean property, congruence for ∈ on each side), extensionality, and the twelve existence axioms. They are written with terms for singletons and pairs, for example

`∀x³ ∃y⁵ ∀p⁰ q⁰ r⁰ (⟨{{p}}, ⟨q, r⟩⟩ ∈ y ↔ ⟨p, r⟩ ∈ x)`

for insertion two, and `rel` eliminates the terms, introducing one existential quantifier for each subterm that is not a variable. `nfTyped` is the list of typed sentences so obtained, with types in {0,…,5}, and `nfUntyped` is their erasure. This is the NF₀ of §1.

**The statements.**

| Statement | Lean |
|---|---|
| What `rel φ` means in a structure with singleton and pair operations | `ev_rel` |
| The typed sentences are well typed and closed | `nfTyped_wf`, `nfTyped_closed` |
| Every axiom holds in the strand along any seven sorts of a finite-height model | `flat_sem`, `strand_holds` |
| On the sorts 2,…,ht a finite-height model is a tangle for `nfTyped` | `tangle_of_flat` |
| A model of height `sortsNeeded 5 n + 1` excludes cut-free refutations of `nfUntyped` of size n | `nf_no_refutation` |
| `nfUntyped` has no cut-free refutation | `nf_cutfree_consistent` |
| A structure satisfying `nfUntyped`, with = read as identity, is a model of NF and satisfies stratified comprehension | `nfModel_of_axioms`, `isNF_of_axioms` |
| Every model of NF satisfies `nfUntyped` | `axioms_of_nfModel` |

The last two rows are a check on the list itself: with = read as identity, the seventeen sentences have exactly the models of NF in the sense of the earlier files, and by Hailperin's theorem (§1) these satisfy every instance of stratified comprehension.

`nf_no_refutation` is the Main Lemma for NF in external form. It is the statement that a refutation of size n is excluded by a model whose height is an explicit function of n; `nf_cutfree_consistent` follows because models of every height exist (§4.2).

**What this does not give.** The same as in §5.6 and §6.1: these are theorems of Lean's logic about actual finite derivations and actual models. The Main Lemma needs the argument inside U, at a possibly nonstandard n, with the model obtained from the constructible structure through the Transfer Lemma. Lean's `nf_cutfree_consistent` is also not new as a consistency result, since the earlier files already give a model of NF; what is new is that it is obtained by the route of §§5–6, with the height bounded in terms of n.

### 4.5 The construction inside a host **[Lean]**

This replaces §4.2–§4.4. Files `Host.lean` and the first part of `NFUTerm.lean`.

A **host** is a structure (W, ∈, <*) satisfying extensionality, pairing, union, infinity, Separation and Collection for every first-order formula, in which <* is a linear order with x ∈ y → x <* y and every nonempty definable class has a <*-least element (`Host`). A **ladder of closed levels** of height d, for a number d ≥ 1 of the host, is a function Λ of the host defined exactly on 0, …, d + 1, with transitive values, each a member of the next, such that ω ∈ Λ(1) and each of Λ(1), …, Λ(d + 1) contains every subset of each of its members, satisfies Collection for definable relations from a member of it into it, and for each of its members a has a member that includes {b : b <* a}.

**Theorem 4.5.1** (`Host.tower_of_ladder`, with `ext_ax`, `sing_ex`, `up_ex`, `inter_ex`, `compl_ex`, `cardinalOne_ex`, `vCross_ex`, `converse_ex`, `subset_ex`, `singletonImage_ex`, `insertion2_ex`, `insertion3_ex`, `typeLower_ex`). Let Λ be a ladder of closed levels of height d in a host. Then there is a tangle with levels 1, …, d in the sense of §4.1, given by definable relations of the host: extensionality holds between any two levels, and the typed forms of the twelve existence axioms hold for every descending chain of levels.

The construction is the overlapping one of your exposition `nf_consistency_exposition.tex`: atoms and labels with prescribed adjacency, positions given by <*, paths, tokens and supports, and the stages defined level by level by Separation. Because d is an element of the host and every step is Separation, Collection or induction in the host, the theorem applies when d is not a standard number. That is the content of the Transfer Lemma.

**Theorem 4.5.2** (`Model.exists_host_tower`). In U, if 3(d₀ + 3) + 2 is calm, there are a host, a tangle in it with d₀ + 1 levels as in Theorem 4.5.1, and a map num from the numbers of U onto the numbers of the host that takes 0 to ∅, successor to successor and < to ∈.

*Proof.* The host is the structure 𝔏 of Lemma 3.2 (`Model.host`): Separation, Collection and the properties of <* are §3.3 (4) and (6), here for every formula (`s_sep`, `s_coll`, `s_least`). The closed levels are the levels at the stages ν₁ < ν₂ < … of §3.3 (8), each the least stage that is not small over the one before: transitivity and closure under subsets are `next_absorb`; Collection inside a level is the proof of Collection at a stage, with the formula evaluated at a later stage (`next_coll_at`); the initial segments of <* are covered because <* compares ranks first (`cover_lim`). ∎

In addition, +, × and 2ˣ are definable in this host and agree with those of U through num (`Model.arith`), and induction over the numbers of U holds for definable relations of the host along set functions of U (`Model.mixed_ind`).

---

## 5. From an untyped refutation to typed sentences

*Not on the path to the theorem since 15 November 2026 (see the status paragraph). Kept unchanged.*

This section is syntax. Everything in §§5.1–5.4 is a statement about finite syntactic objects proved by induction on them, hence a theorem of PA, hence available in U for derivations of nonstandard length (§2.1). The one semantic statement is Lemma 5.5(c), which is proved in U for set structures. The conversion is Crabbé's (1978, Lemmas 1 and 2); I have written the proofs out and added the bounds. The whole section is also formalised in Lean; §5.6 says exactly what the Lean theorems state and where they differ from the text.

### 5.1 The calculi

*Untyped.* Variables are names x, y, z, …. Formulas are built from atoms x ∈ y, x = y and the constant ⊤ by ¬, ∧, ∨, →, ∀x, ∃x. Derivations are in Gentzen's sequent calculus **without cut**: sequents Γ ⊢ Δ of finite lists of formulas; initial sequents A ⊢ A with A atomic, and ⊢ ⊤; the structural and propositional rules; and

- ∀-left: from Γ, A(y) ⊢ Δ infer Γ, ∀x A(x) ⊢ Δ; ∃-right dually;
- ∀-right: from Γ ⊢ A(z), Δ infer Γ ⊢ ∀x A(x), Δ, where the *eigenvariable* z is not free in the conclusion; ∃-left dually.

A **cut-free refutation of NF₀** is a cut-free derivation of the sequent whose left side lists the axioms of NF₀ and whose right side is empty. Every formula in such a derivation is a subformula of an axiom with variables substituted for variables.

*Typed.* Variables are xⁱ (a name with a type i ∈ ℕ). Atoms are xⁱ ∈ yⁱ⁺¹, xⁱ = yⁱ and ⊤. **Typed logic** is the many-sorted sequent calculus with the same rules, plus cut; in ∀-left and ∃-right the instantiating variable has the type of the quantified one. It has no non-logical axioms. A typed structure has a nonempty set for each type that occurs and relations for ∈ and = between the appropriate sorts. Soundness holds as in §3.1.

G⁺ is G with every type raised by one. |·| counts symbol occurrences. W = {0,…,5}.

### 5.2 Typed versions and lifts

The **erasure** of a typed formula deletes the types. A typed formula G is a **typed version** of an untyped A if its erasure is A and erasing does not change which quantifier binds which occurrence. So in a typed version all occurrences bound by one quantifier carry that quantifier's type, while free occurrences of one name may carry different types. A typed version of a sequent replaces each formula by a typed version of it.

Let G′ and G″ be typed versions of the same formula. G″ is a **lift** of G′ if at every variable occurrence the type in G″ is the type in G′ or one more. The occurrences where it is one more are **shifting**. A quantifier shifts together with the occurrences it binds. A **pair** is (G′, G″) with G″ a lift of G′.

Two facts are used without comment. If Γ′ ⊢ Δ′ is a typed version of the conclusion of a rule of the cut-free calculus, the types are inherited by the premises, which become typed versions of the premises, and the typed form of the same rule leads from them to Γ′ ⊢ Δ′. (For ∀-left with principal formula ∀xⁱ A′, the premise receives A′(yⁱ).) The eigenvariable conditions remain satisfied, because an eigenvariable name does not occur free in the untyped conclusion at all. What fails is only this: an initial sequent x ∈ y ⊢ x ∈ y may become xᵃ ∈ yᵃ⁺¹ ⊢ xᵇ ∈ yᵇ⁺¹ with a ≠ b.

### 5.3 The conversion

**Lemma 5.1 (Crabbé's Lemma 1).** **[proved]** Let (F′, F″) be a pair, and suppose typed logic derives Γ, F′ ⊢ Δ and ⊢ F″. Let x be a name and k a type such that no xʲ with j ≠ k is free in Γ, Δ. Then there is a pair (G′, G″) such that typed logic derives Γ, G′ ⊢ Δ and ⊢ G″, no xʲ with j ≠ k is free in G′, every variable free in G′ is free in F′, the types occurring in G′ are those occurring in F′, and G′ is F′ with at most two quantifiers prefixed for each j ≠ k such that xʲ is free in F′.

*Proof.* Induction on the number of j ≠ k with xʲ free in F′. If there is none, take (F′, F″). Otherwise choose r as follows: if some such j exceeds k, let r be the greatest; if not, let r be the least. Take new names v, w. Let D′ be F′ with each non-shifting free occurrence of xʳ replaced by vʳ and each shifting one by wʳ. Let D″ be F″ with the corresponding occurrences replaced by vʳ and wʳ⁺¹. Then (D′, D″) is a pair, and

F′ = D′[vʳ := xʳ, wʳ := xʳ],  F″ = D″[vʳ := xʳ, wʳ⁺¹ := xʳ⁺¹].

Since F″ is a lift of F′, a free occurrence of xʲ in F″ sits where F′ has xʲ or xʲ⁻¹.

*Case r > k.* By the choice of r, xʳ⁺¹ is not free in F′. So xʳ⁺¹ is free in F″ only at the shifting occurrences of xʳ, and is not free in D″[vʳ := xʳ]. From ⊢ F″, ∀-right with eigenvariable xʳ⁺¹ gives ⊢ ∀wʳ⁺¹ D″[vʳ := xʳ], and ∃-right gives ⊢ ∃vʳ ∀wʳ⁺¹ D″. From Γ, F′ ⊢ Δ, ∀-left gives Γ, ∀wʳ D′[vʳ := xʳ] ⊢ Δ. Now xʳ is not free in Γ, Δ (as r ≠ k) nor in D′, so ∃-left with eigenvariable xʳ gives Γ, ∃vʳ ∀wʳ D′ ⊢ Δ. Put G′ = ∃vʳ ∀wʳ D′ and G″ = ∃vʳ ∀wʳ⁺¹ D″.

*Case r < k.* Then all j in question are below k, and xʳ⁻¹ is not free in F′. So xʳ is free in F″ only at the non-shifting occurrences of xʳ, and is not free in D″[wʳ⁺¹ := xʳ⁺¹]. From ⊢ F″, ∀-right with eigenvariable xʳ gives ⊢ ∀vʳ D″[wʳ⁺¹ := xʳ⁺¹], and ∃-right gives ⊢ ∃wʳ⁺¹ ∀vʳ D″. From Γ, F′ ⊢ Δ, ∀-left gives Γ, ∀vʳ D′[wʳ := xʳ] ⊢ Δ, and ∃-left with eigenvariable xʳ gives Γ, ∃wʳ ∀vʳ D′ ⊢ Δ. Put G′ = ∃wʳ ∀vʳ D′ and G″ = ∃wʳ⁺¹ ∀vʳ D″.

In both cases (G′, G″) is a pair, xʳ is no longer free in G′, and nothing new is free in G′. Apply the induction hypothesis. ∎

**Lemma 5.2 (removing a name).** **[proved]** In the situation of Lemma 5.1 suppose in addition that no xʲ with j ≠ k is free in F′. Let D′, D″ be defined as above with r = k. Then (∀vᵏ ∀wᵏ D′, ∀vᵏ ∀wᵏ⁺¹ D″) is a pair, typed logic derives ⊢ ∀vᵏ ∀wᵏ⁺¹ D″, and from Γ, F′ ⊢ Δ it derives Γ, ∀vᵏ ∀wᵏ D′ ⊢ Δ.

*Proof.* Neither xᵏ⁺¹ nor xᵏ⁻¹ is free in F′. So in F″ the variable xᵏ⁺¹ is free only at the shifting occurrences of xᵏ and xᵏ only at the non-shifting ones. Two applications of ∀-right, with eigenvariables xᵏ⁺¹ and then xᵏ, give ⊢ ∀vᵏ ∀wᵏ⁺¹ D″. Two applications of ∀-left give the other sequent. ∎

**Lemma 5.3 (Crabbé's Lemma 2, with bounds).** **[proved]** There is a standard c₀ such that the following holds. Let π be a cut-free derivation of Γ ⊢ Δ and let Γ′ ⊢ Δ′ be a typed version of Γ ⊢ Δ with all types in W. Then there is a pair (F′, F″) such that

1. all types in F′ are in W (so all types in F″ are in {0,…,6});
2. typed logic derives Γ′, F′ ⊢ Δ′ and ⊢ F″, with all types in {0,…,6};
3. |F′| ≤ c₀·|π|.

*Proof.* Induction on π.

*Initial sequents.* For ⊢ ⊤ take (⊤, ⊤). Otherwise the sequent is R ⊢ R with R an atom x ∈ y or x = y. Write Rᵢ for its typed version in which x has type i. The typed version of the sequent is Rₐ ⊢ R_b. If a = b take (⊤, ⊤). If a < b take

F′ = ⋀_{a ≤ i < b} (Rᵢ → Rᵢ₊₁),  F″ = ⋀_{a ≤ i < b} (Rᵢ₊₁ → Rᵢ₊₁).

F″ is the lift of F′ in which the antecedents shift. Typed propositional logic derives Rₐ, F′ ⊢ R_b and ⊢ F″. If b < a take

F′ = ⋀_{b ≤ i < a} (Rᵢ₊₁ → Rᵢ),  F″ = ⋀_{b ≤ i < a} (Rᵢ₊₁ → Rᵢ₊₁),

where the consequents shift. At most five conjuncts occur, since the types lie in W.

*One-premise rules without eigenvariable.* The typed premise is determined (§5.2). Take the pair given by the induction hypothesis for the premise and apply the typed rule with F′ as a side formula.

*Two-premise rules.* Let (E′, E″) and (D′, D″) be the pairs for the premises. Take (E′ ∧ D′, E″ ∧ D″). By ∧-left and weakening both typed premises are derivable with E′ ∧ D′ in place of E′ and of D′; apply the typed rule. And ⊢ E″ ∧ D″ by ∧-right.

*Eigenvariable rules.* Consider ∀-right, from Γ ⊢ A(x), Π to Γ ⊢ ∀y A(y), Π; ∃-left is the same. Let the typed conclusion be Γ′ ⊢ ∀yᵏ A′(yᵏ), Π′, so the typed premise is Γ′ ⊢ A′(xᵏ), Π′. The induction hypothesis gives a pair (E′, E″) with Γ′, E′ ⊢ A′(xᵏ), Π′ and ⊢ E″. The name x is not free in Γ, Π, so no xʲ is free in Γ′, Π′, and only xᵏ is free in A′(xᵏ). Lemma 5.1 applies and gives (G′, G″) with no xʲ, j ≠ k, free in G′. Lemma 5.2 then gives the pair

F′ = ∀vᵏ ∀wᵏ D′,  F″ = ∀vᵏ ∀wᵏ⁺¹ D″

with ⊢ F″ and Γ′, F′ ⊢ A′(xᵏ), Π′. Now xᵏ is not free in Γ′, F′, Π′, and ∀-right gives Γ′, F′ ⊢ ∀yᵏ A′(yᵏ), Π′.

*Types and size.* No step introduces a type into F′ that was not already present in the typed end sequent or in a typed initial sequent, and these lie in W. Each initial sequent contributes a formula of bounded size, each two-premise rule one connective, and each eigenvariable rule at most two quantifiers for each of the six types. The number of initial sequents and of inferences is at most |π|. ∎

**Lemma 5.4 (closing).** **[proved]** In Lemma 5.3, if Γ′ and Δ′ consist of sentences, then F′ and F″ can be taken to be sentences, with |F′| ≤ c₀·|π| for a larger standard c₀.

*Proof.* For each name x free in F′ apply Lemma 5.1 (any k will do, as Γ′, Δ′ are closed) and then Lemma 5.2. This adds at most twelve quantifiers per name. F″ has the same free names as F′, so it becomes closed as well. ∎

### 5.4 Pieces

From now on only sentences are involved, and types can be attached to names. Let (F′, F″) be a pair of sentences. Rename bound variables in their common erasure so that different quantifiers bind different names, and call the result C. Then F′ and F″ are, up to renaming of bound variables, C^{σ′} and C^{σ″}, where σ′ and σ″ assign to each name of C the type of its quantifier in F′ and in F″, and C^σ denotes C read with x of type σ(x). We have σ′ ≤ σ″ ≤ σ′ + 1. Call σ a **typing** of a formula G if G^σ is a typed formula, that is, σ(y) = σ(x) + 1 for each atom x ∈ y of G and σ(x) = σ(y) for each atom x = y.

For an untyped formula G in which no quantifier on a name lies in the scope of another quantifier on the same name, define by recursion a finite set Π(G) of formulas, the **pieces** of G, and a Boolean function β_G of truth assignments to Π(G).

- G an atom other than ⊤: Π(G) = {G}, β_G(e) = e(G). Π(⊤) = ∅, β_⊤ = 1.
- Π(¬G₁) = Π(G₁) with β negated; Π(G₁ ∘ G₂) = Π(G₁) ∪ Π(G₂) with β_G = β_{G₁} ∘ β_{G₂}, for ∘ among ∧, ∨, →.
- G = ∀x G₁. Let X be the set of pieces of G₁ in which x is free and Y the rest. If X = ∅, put Π(G) = Π(G₁) and β_G = β_{G₁}. Otherwise, for each u : X → {0,1} let κ_u be the disjunction over P ∈ X of P if u(P) = 0 and of ¬P if u(P) = 1; so κ_u fails exactly when the pieces in X take the values u. Put Π(G) = Y ∪ {∀x κ_u : u ∈ {0,1}^X}, and β_G(e) = 1 iff e(∀x κ_u) = 1 for every u with β_{G₁}(u, e↾Y) = 0.
- ∃x G₁ is treated as ¬∀x ¬G₁.

Call a formula **connected** if it contains an atom other than ⊤ and the graph on its names, with an edge between two names that occur in a common atom, is connected.

**Lemma 5.5.** **[proved]** (a) |Π(G)| ≤ t(|G|). (b) Every piece of G is connected, its atoms are atoms of G, and its free variables are free in G; so the pieces of a sentence are sentences. (c) Let σ be a typing of G, 𝔐 a typed set structure with nonempty sorts, and a an assignment. Then G^σ is true in 𝔐 under a iff β_G(e) = 1, where e(P) is the truth value of P^σ in 𝔐 under a.

*Proof.* (a) Let s be the number of connectives and quantifiers of G; we show |Π(G)| ≤ t(s). Atoms: 1 ≤ t(0). Binary connectives: t(s₁) + t(s₂) ≤ 2·t(max) ≤ t(max + 1). Quantifiers: |Y| + 2^{|X|} ≤ 2^{|X|+|Y|} ≤ 2^{t(s₁)} = t(s₁ + 1). (b) By induction. In ∀x κ_u every disjunct is connected and contains x, so the union is connected. (c) By induction on G; this is an induction for a stratified condition, since satisfaction is a set. In the quantifier case with X ≠ ∅: for b in the sort of x let u_b be the values of the pieces in X under a[x := b]. The pieces in Y do not contain x free, so their values e↾Y do not depend on b. By the induction hypothesis ∀x G₁ is true iff β_{G₁}(u_b, e↾Y) = 1 for all b, iff no u with β_{G₁}(u, e↾Y) = 0 is of the form u_b, iff ∀x κ_u is true for every such u. If X = ∅ the value of G₁ does not depend on b, and the sort is nonempty. ∎

**Lemma 5.6.** **[proved]** Let C be a sentence, σ′ and σ″ typings of C with σ′ ≤ σ″ ≤ σ′ + 1, and P a piece of C. Then P^{σ″} is P^{σ′} or (P^{σ′})⁺.

*Proof.* σ″ − σ′ takes the same value on two names that occur in a common atom, by the definition of typing. P is connected, so σ″ − σ′ is constant on the names of P, with value 0 or 1. ∎

### 5.5 Summary of the syntax

Fix once and for all a typed version, with types in W, of each axiom of NF₀, and let Γ₀ be the list of them.

**Proposition 5.7.** **[proved]** There is a standard c₁ such that U proves the following. For every cut-free refutation π of NF₀ there are typed sentences F′ and F″, derivations in typed logic of Γ₀, F′ ⊢ and of ⊢ F″ with all types in {0,…,6}, and typed sentences A₁,…,A_N with types in W, where N ≤ t(c₁·|π|), such that for every typed set structure 𝔐 with nonempty sorts 0,…,6:

if 𝔐 ⊨ Aᵢ ⇔ 𝔐 ⊨ Aᵢ⁺ for all i ≤ N, then 𝔐 ⊨ F′ ⇔ 𝔐 ⊨ F″.

*Proof.* Lemmas 5.3 and 5.4 with Γ′ = Γ₀ and Δ′ empty give F′, F″ and the derivations. Form C, σ′, σ″ as in §5.4 and let the Aᵢ be the sentences P^{σ′} for P ∈ Π(C). By Lemma 5.5(a), N ≤ t(|C|) ≤ t(c₀|π|) with c₀ from Lemma 5.4; take c₁ = c₀. By Lemma 5.5(c), F′ is true in 𝔐 iff β_C(e′) = 1 and F″ iff β_C(e″) = 1, where e′(P), e″(P) are the truth values of P^{σ′}, P^{σ″}. By Lemma 5.6, e″(P) is the truth value of P^{σ′} or of (P^{σ′})⁺. Under the hypothesis e′ = e″. ∎

### 5.6 The Lean formalisation **[Lean]**

File `ConNF/NF/Crabbe.lean` (also contained in the standalone `CrabbeMainLemma.lean`, which needs only Mathlib). About 2,470 lines, no `sorry`, replayed in the kernel checker, axioms `propext`, `Classical.choice`, `Quot.sound` only. To check it: apply `con-nf-finite-height-full.patch` to con-nf at commit `edbce7e` and run `lake build ConNF.NF.Crabbe`, or compile the standalone file against Mathlib. The file ends with a worked example (`ex_crabbe`): the refutable theory ∀x∀y (x ∈ y), ∀x∀y ¬(x ∈ y), with its two axioms typed at different levels.

**The final statement** (`Crabbe.crabbe`). Let Γ₀ be a list of well-typed sentences with types in {0,…,w} whose erasures have a cut-free refutation with n inferences. Then there is a list 𝒜 of well-typed sentences with types in {0,…,w}, of length at most `tower (bound w n)`, such that no typed structure with nonempty levels satisfies Γ₀ and satisfies A ↔ A⁺ for every A in 𝒜. Here `bound w n = (2w+2)n + (2w+2)(2((2w+2)n+1))`, so for the window of six types the bound is t(300n + 24).

| Text | Lean |
|---|---|
| §5.2, types are inherited by premises | `typeUp` |
| Lemma 5.1 and Lemma 5.2 | `inv_EA`, `inv_EB`, `inv_AA`, `inv_elim` |
| Lemma 5.3 | `conv` |
| Lemma 5.4 | `inv_closeAll`, `conversion` |
| Lemma 5.5(a) | `length_pieces` |
| Lemma 5.5(b) and Lemma 5.6 | `free_pieces`, `pieces_wf`, `map_f2_of_unif` |
| Lemma 5.5(c) | `ev_pieces` |
| Proposition 5.7 | `crabbe` |

**How the Lean version differs from the text.**

1. *Semantic form.* Where the text says "typed logic derives ⊢ F″" and "typed logic derives Γ′, F′ ⊢ Δ′", Lean proves "F″ is true in every typed structure at every assignment" and "in every typed structure, at every assignment where F′ holds, the sequent Γ′ ⊢ Δ′ is true". This is what Step 7 of §6 uses. It also shows that the typed derivations are not needed: in §6 one can argue directly with truth in the strand, and the appeal to soundness for the typed derivations disappears.
2. *A pair is one formula.* A pair (F′, F″) is a single formula whose variables and quantifiers carry a type and a shift bit; F′ and F″ are its two readings. "F″ is a lift of F′" then holds by construction. Bound variables are de Bruijn indices, so there is no renaming and no capture.
3. *The calculus.* Rules are in absorbed form (the principal formula is kept) with one general structural rule (any sequent may be enlarged, as lists up to inclusion). Gentzen's cut-free rules are instances, each costing at most two inferences. Equality is an ordinary binary predicate.
4. *Lemma 5.1 with a fixed schedule.* Lean adds the two quantifiers for every type of the window whether or not the variable occurs with that type: 2w+2 quantifiers per eigenvariable inference, which is the twelve of the text for w = 5. Vacuous quantifiers do no harm.
5. *Connectedness.* The graph argument of Lemma 5.6 is replaced by an invariant proved by induction: all shift bits inside one piece agree. The reason is the one in the text: the pieces under a quantifier all contain the quantified variable.
6. *Empty X.* When no piece of the body contains the quantified variable, Lean adds the piece ∀x ⊥ instead of using that the sort is nonempty. The count in Lemma 5.5(a) is unaffected.

**What the Lean theorem does not give.** It is a theorem of Lean's logic about actual finite derivations. The Main Lemma needs the same statement inside U for derivations whose size is a nonstandard number of U. The Lean proof is by structural recursion with explicit constructions, which is the kind of argument that goes through in PA for the syntax and in U for the truth clause, but Lean does not certify that step. Also, the Lean statement asks for every level of the structure to be nonempty; for a strand with seven sorts one adds one dummy element at each higher level, which does not affect sentences with types in {0,…,6}.

---

## 6. The main lemma

*Not on the path to the theorem since 15 November 2026 (see the status paragraph). Kept unchanged.*

**Lemma 6.1 (finite Ramsey).** **[textbook]** There is a standard e such that PA proves: for every N ≥ 1 there is q, at most the result of applying e exponentials to N, such that every colouring of the 6-element subsets of {0,…,q−1} by subsets of {1,…,N} has a homogeneous set of 7 elements.

This is the Erdős–Rado stepping-up bound r_{k+1}(m) ≤ c^{r_k(m−1)^k}, starting from the pigeonhole principle; each step is an induction on finite sets. By §2.1 it holds in U for colourings that are sets.

**Main Lemma.** U proves: no number in 𝖪 is a cut-free refutation of NF₀.

*Proof.* Work in U. Let π ∈ 𝖪 be a cut-free refutation of NF₀.

**Step 1 (syntax).** Proposition 5.7 gives F′, F″, the two typed derivations, and A₁,…,A_N with N ≤ t(c₁|π|).

**Step 2 (sizes).** Let q be as in Lemma 6.1. Then q ≤ t(c₁|π| + e). Since |π| ≤ π ∈ 𝖪, Lemma 2.3 shows that q is calm. Let c be the constant of the Transfer Lemma and m = c·(q+2). The calm numbers are closed under addition and multiplication, so 3m+5 is calm.

**Step 3 (the constructible structure).** By Lemma 3.2 there is a well-founded set structure 𝔏 ⊨ ZFC⁻ whose numbers are isomorphic to ℕ and in which the m-th iterated power set of ω exists. (Lemma 3.2 is now a Lean theorem; its exact form is in §3.3 (9). The Transfer Lemma has to be read with that form: a structure with a global well-ordering <*, Separation and Collection for formulas with <*, and the iterated power sets given together with their finite sequence.)

**Step 4 (the tangle).** The Transfer Lemma is a theorem of ZFC⁻ with a standard proof, and every axiom of ZFC⁻ holds in 𝔏, so its statement holds in 𝔏. Apply it in 𝔏 with D+1 = q+2. This gives an element of 𝔏 which 𝔏 believes to be a tangle with q+2 sorts. Its sorts and membership relations are elements of 𝔏; replacing each by the set of its ε-members gives a set structure 𝔗 in U, with sorts indexed by the numbers below q+2. The defining properties of a tangle form a fixed finite list of statements in which every quantifier ranges over a sort or over the index set. Such statements mean the same in 𝔏 and in U. So 𝔗 is a tangle in U. Discard sorts 0 and 1 and renumber; 𝔗 now has q sorts, all nonempty (§4.1).

**Step 5 (Ramsey).** For a 6-element set H of sorts let χ(H) = {i ≤ N : 𝔗[H] ⊨ Aᵢ}, where type j of Aᵢ is read as the j-th element of H. The satisfaction relations of the strands form one set, by recursion on formulas, so χ is a set. By Lemma 6.1 there are sorts h₀ < … < h₆ all of whose 6-element subsets have the same colour.

**Step 6 (ambiguity).** Let 𝔐 = 𝔗[h₀,…,h₆]. A sentence with types in W is evaluated in 𝔐 exactly as in 𝔗[h₀,…,h₅], and Aᵢ⁺ is evaluated in 𝔐 exactly as Aᵢ in 𝔗[h₁,…,h₆]. By homogeneity, 𝔐 ⊨ Aᵢ ⇔ 𝔐 ⊨ Aᵢ⁺ for every i. By Proposition 5.7, 𝔐 ⊨ F′ ⇔ 𝔐 ⊨ F″.

**Step 7 (contradiction).** The sorts of 𝔐 are nonempty, so soundness applies to both typed derivations. From ⊢ F″ we get 𝔐 ⊨ F″, hence 𝔐 ⊨ F′. Every member of Γ₀ is a typed version of an axiom of NF₀ with types in W, so it holds in the strand 𝔐 (§4.1). But Γ₀, F′ ⊢ is derivable, so not all of Γ₀, F′ hold in 𝔐. Contradiction. ∎

Three remarks on the proof.

- The number of sorts needed is a tower of height about c₁|π| + e. A cut closed only under addition and multiplication does not reach that far. The calm cut is closed under exponentiation (Lemma 2.2), so one shortening to 𝖢₂ pays for the whole tower. This is the point where the argument uses that U is NFU and not just a theory of the same strength.
- The Transfer Lemma is used at D = q+1, which need not be standard. A proof of "for each standard D there is a tangle" would not do.
- Choice is not assumed in U. It is available inside 𝔏, which is why the tangle is built there.

### 6.1 The Lean formalisation of Steps 1 and 5–7 **[Lean]**

File `ConNF/NF/MainLemma.lean` (610 lines; also the second half of the standalone `CrabbeMainLemma.lean`). No `sorry`, replayed in the kernel checker, axioms `propext`, `Classical.choice`, `Quot.sound` only. Build with `lake build ConNF.NF.MainLemma`.

**Setting.** A *tangled structure* 𝔗 is a set of elements, each with a sort in ℕ, with the two relations between any two elements. Its *strand* along a finite set S of sorts is the typed structure in which the i-th smallest member of S is type i (`strandOf`). `IsTangle w q Γ₀ 𝔗` says: the sorts below q are inhabited, and Γ₀ holds in the strand along every set of w+2 of them. This is the property of tangles stated at the end of §4.1, for an arbitrary list Γ₀ of typed sentences.

**The statement** (`main_lemma`). Let Γ₀ be well-typed sentences with types in {0,…,w} whose erasures have a cut-free refutation with n inferences, and let 𝔗 be a tangled structure whose sorts below `sortsNeeded w n` are inhabited. Then Γ₀ fails in the strand of 𝔗 along some set of w+2 of these sorts. Hence (`no_refutation_of_tangle`) a tangle with `sortsNeeded w n` sorts excludes refutations of size n, and (`cutfree_consistent`) tangles with arbitrarily many sorts give cut-free consistency. The same holds for any finite set V of at least `sortsNeeded w n` inhabited sorts in place of the first ones (`main_lemma_on`, `no_refutation_of_tangle_on`); this is the form used in §4.4, where the two lowest sorts are left out.

The number of sorts is explicit:

`sortsNeeded w n = erR (2 ^ tower (bound w n)) (w+1) (w+2)`,

where `erR c k m` is the Erdős–Rado bound for colourings of k-element sets with c colours and a homogeneous set of m elements: `erR c 0 m = m` and `erR c (k+1) m = need c k 0 (erR c k m + 1)`, with `need c k i 0 = 0` and `need c k i (j+1) = c ^ C(i,k) · (need c k (i+1) j + 1)`. So each unit of k costs one exponential of a polynomial, as Lemma 6.1 requires. Lean defines this function and proves Ramsey's theorem for it. It does not prove the inequality "at most e exponentials applied to N"; that is read off the definition.

| Text | Lean |
|---|---|
| Lemma 6.1 | `build`, `ramsey` |
| Strands (§4.1) | `rank`, `strandOf`, `strand_levels` |
| Step 1 | `crabbe` (§5.6) |
| Step 5 | the colouring in `main_lemma`, `ramsey` |
| Step 6 | `ev_transfer`, `holds_lower`, `holds_upper` |
| Step 7 | the conclusion of `crabbe` |

Mathlib has no Ramsey theorem for sets of k elements, so it is proved here, by the end-homogeneous construction: before each new point is chosen the candidates are thinned to one class of the colour pattern over the k-element sets of points already chosen.

The file ends with a check that the hypotheses can be met (`ex_consistent`): the structure in which everything is related to everything is a tangle, with any number of sorts, for ∀x⁰∀y¹ (x ∈ y), so ∀x∀y (x ∈ y) has no cut-free refutation.

**What is not covered.**

1. *Steps 2–4.* The calm numbers, the constructible structure and the Transfer Lemma. In the Lean statement they are replaced by the hypothesis that a tangle with enough sorts is given.
2. *The step inside U.* As for §5, this is a theorem of Lean's logic about actual finite objects. The Main Lemma itself is the same argument inside U at a possibly nonstandard n.
3. *The link to the Lean finite-height models.* This was missing when this subsection was written and is now formalised: see §4.4. With it, Lean proves "no cut-free refutation of NF₀ of size n" directly from the model of height `sortsNeeded 5 n + 1` (`nf_no_refutation`).

---

## 7. From the Main Lemma to an interpretation

*Not on the path to the theorem since 15 November 2026 (see the status paragraph). Kept unchanged.*

**Sequentiality.** A theory is sequential if it directly interprets adjunctive set theory: for some definable membership relation on all its objects there is an empty set, and x ∪ {y} exists for all x, y. NF proves both for ∈, so NF₀ is a finitely axiomatised sequential theory.

**Restricted consistency.** For a standard n let Con_n(NF₀) say: no proof of a contradiction from NF₀ uses only formulas of depth of quantifier alternations at most n. Proofs here are in a standard calculus with cut.

**Lemma 7.1 (interpretation existence).** **[cited]** If A is a finitely axiomatised sequential theory and n is at least the alternation depth of A, then S¹₂ + Con_n(A) interprets A.

This is one half of the statement that S¹₂ + Con_{ρ(A)}(A) and A are mutually interpretable (Visser 2022, §1.2(c); the method is Pudlák 1985, and Visser 2017 is a detailed exposition). The proof is a Henkin construction carried out on a definable cut of the numbers of S¹₂ + Con_n(A): one decides the sentences of complexity ≤ n in turn, keeping the set decided so far n-consistent, and reads off a model of A from the resulting branch. The published statement is for n equal to the alternation depth of A. For larger n the hypothesis Con_n(A) is stronger, so the lemma holds as stated. Below, Con_n(NF₀) is obtained for every standard n, so nothing depends on the exact threshold.

**Lemma 7.2.** **[proved, using textbook proof theory]** For every standard n, U interprets S¹₂ + Con_n(NF₀).

*Proof.* (i) *Cut elimination.* There is a standard g, depending on n, such that PA proves: every proof p of a contradiction from NF₀ in which all formulas have alternation depth ≤ n can be transformed into a cut-free refutation of NF₀, in the calculus of §5.1, whose code is at most g exponentials applied to p (Gerhardy 2005; the height of the tower is governed by the alternation depth of the cut formulas, and g also absorbs the change of calculus and of coding). This holds in the arithmetic of U.

(ii) *Shortening.* For a definable cut I closed under + and ×, the class I₁ = {x : 2ˣ ∈ I} is a cut closed under +, and I₂ = {x : x·y ∈ I₁ for all y ∈ I₁} is a cut contained in I₁ and closed under + and ×. Iterating g+1 times from 𝖪 gives a cut I closed under + and × with g+1 exponentials applied to any x ∈ I lying in 𝖪. Let 𝖩 = {x : the binary length of x is in I}. Then 𝖩 is a cut closed under +, × and x ↦ 2^{|x|²}, and g exponentials applied to any x ∈ 𝖩 lie in 𝖪.

(iii) *The interpretation.* Take 𝖩 as domain, with the arithmetical operations of ℕ. S¹₂ has finitely many axioms. Bounded formulas mean the same in 𝖩 as in ℕ, and ℕ satisfies the least number principle for arithmetical formulas (§2.1), so 𝖩 satisfies the basic axioms and polynomial induction for bounded formulas. If p ∈ 𝖩 were a proof as in (i), then by (i) and (ii) there would be a cut-free refutation of NF₀ in 𝖪, contradicting the Main Lemma. Being a proof is a bounded condition, so Con_n(NF₀) holds relativised to 𝖩. ∎

**Theorem.** **[by this route: modulo the Transfer Lemma; by the route of §1: Lean]** NFU + Infinity interprets NF.

*Proof.* By Lemma 7.2 and Lemma 7.1, U interprets NF₀. Every axiom of NF is a theorem of NF₀ (§1), so the same interpretation interprets NF. ∎

---

## 8. Consequences

The interpretation of NF in U is now the Lean theorem of §1, and in the form of a statement about derivations it is `SetTheory.nfuInterpretsNF : 𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙` (`nf_syntactic_interpretation_2026-11-15.md`). Item 1 is in Lean as well. Items 2–4 are not formalised; they use, besides item 1, only facts cited from the literature.

1. **Mutual interpretability.** NF proves every axiom of NFU when everything is declared a set, and NF proves Infinity (Specker 1953). So NF interprets U by the identity, and NF and NFU + Infinity are mutually interpretable. **[Lean]** since 15 November 2026: `nf_infinity`, `nf_interprets_nfu_inf` and `nf_nfu_inf_mutually_interpretable`, in `NFSpecker.lean` and `MutualInterpretability.lean`; the proof is written out in `nf_infinity_not_choice_2026-11-15.md`. The same file proves that NF refutes Choice (`nf_not_choice`).
2. **Equiconsistency in weak arithmetic.** An interpretation translates proofs in polynomial time, so Con(NFU + Infinity) ↔ Con(NF) is provable in very weak arithmetic, in particular in PRA.
3. **Your chain.** You have Con(NF) ⇒ Con(C₀) ⇔ M198 never halts ⇒ Con(NFU + Infinity). With Con(NFU + Infinity) ⇒ Con(NF) the chain closes, and the four statements are equivalent over any base theory that proves your two implications and contains PRA. So C₀, NF and NFU + Infinity are equiconsistent, and M198 never halts iff NF is consistent.
4. **Mac Lane set theory.** NFU + Infinity is known to be equiconsistent with TST + Infinity and with Mac Lane set theory (Jensen 1969 for the upper bound; the lower bound also follows from the ladders of §3.2 at standard heights; Mathias 2001 for Mac and TST + Infinity). So Con(Mac) ↔ Con(NF), which is the statement of the v15 manuscript by R. Gutin and E. Glazer. This is equiconsistency. That Mac interprets NF is not shown here.

---

## 9. Ledger

| Step | Where | Status |
|---|---|---|
| NF₀ axiomatises NF (Hailperin) | §1 | Lean |
| Arithmetic of U: recursion, +, ×, 2ˣ, t, Peano arithmetic for ℕ; the operation T | §2.1–2.2 | Lean (`exists_prec`, `peano`, `pa_induction`, `T_succ`; recursion into an arbitrary set `exists_rec_set`; coding of finite sets and relations by numbers `exists_code`, `exists_code_rel`), for an arbitrary model of NFU + Infinity |
| Calm cut closed under exponentiation; tower absorption | §2.3 | Lean (`lemma_2_2`, `lemma_2_3`), for an arbitrary model of NFU + Infinity |
| Satisfaction for set structures and coded formulas | §3.1 | Lean (`satisfaction`), for an arbitrary model of NFU + Infinity |
| Soundness for coded derivations | §3.1 | Lean (`soundness`), for cut-free derivations with large eigenvariables, for an arbitrary model of NFU + Infinity |
| Ladders at calm heights | §3.2 | Lean (`lemma_3_1`), for an arbitrary model of NFU + Infinity |
| Pairing and finite sequences on rungs; relations coded on the next rung | §3.3 (1) | Lean (`exists_pairing`, `rel_code`, `exists_seq`, `seq_code`), for an arbitrary model of NFU + Infinity |
| Set well-orderings: comparability; the Hartogs well-ordering of a rung; sums and products | §3.3 (2) | Lean (`wo_compare`, `hartogs`, `hartogs_no_inj`, `wo_sum`, `wo_lex`, `seg_of_strict`) |
| Recursion along a set well-ordering | §3.3 (3), tool | Lean (`wo_rec`) |
| The constructible hierarchy along a well-ordering of a rung: names, truth at every stage, "denote the same set", the clauses; coincidence; transitivity of levels; equivalence, congruence, extensionality | §3.3 (3), definition and first facts | Lean (`exists_hierData`, `hier_rel`, `hier_neg`, `hier_and`, `hier_all_ex`, `hier_sim`, `coin_hier`, `eps_rank`, `eps_iff`, `sim_refl`, `sim_symm`, `sim_trans`, `inv_hier`, `sim_iff_ext`), in the form without equality described in §3.3 |
| The same: equality definable; definable subsets named; levels increase and are members of later levels; pairs and unions, closure of limit levels under them; foundation | §3.3 (3) | Lean (`hier_eq_sim`, `def_name`, `up_name`, `level_mem`, `pair_name`, `union_name`, `pair_lim`, `union_lim`, `eps_wf`) |
| Each level is a set structure in the sense of §3.1 and the two truth definitions agree | §3.3 (3) | Lean (`hier_structure`, `level_models`), for stages above the least |
| Bounded formulas absolute between levels; separation for bounded formulas at limit levels | §3.3 (3) | Lean (`d0_abs`, `sep_d0`, `bound_lim`, `sep_lim`) |
| The ordinals of the hierarchy are the ordinal names of the stages, ordered as the stages | §3.3 (3) | Lean (`ordName_members`, `ord_is_ordName`, `ordName_lt`, `ordName_inj`) |
| The stages below the first limit stage of the Hartogs well-ordering are the numbers of U | §3.3 (3); used in (9) | Lean (`exists_omega_stage`, `omega_members`) |
| Limit stages and good stages are cofinal in the Hartogs well-ordering | §3.3 (3) | Lean (`limit_above`, `good_above`) |
| Extensionality, foundation, pairing, union, infinity as coded sentences in the limit levels | §3.3 (3); first sentence of (8) | Lean (`limit_level_zf0`), for limit stages above a limit stage that is not the least; such a level, at a good stage, exists in every ladder with a pairing (`exists_zf0_level`, `exists_good_level`) |
| The canonical order of names; the relation symbol <* is a well-ordering of the denoted sets | §3.3 (4) | Lean (`pr_iff`, `pr_total`, `pr_least`, `tie_sim`, `exists_can`, `hier_lt`, `lt_tri`, `lt_least`) |
| Hulls as sets of names closed under six rules; condensation | §3.3 (5) | Lean (`ClosedR`, `exists_hull`, `exists_coll`, `cond_all`) |
| Small stages; the collapse of a hull is generated; absorption; Separation and Collection at the least stage that is not small, in semantic form and as coded sentences; the sentences about <* | §3.3 (6) | Lean (`hull_collapse`, `next_absorb`, `next_sep`, `next_coll`, `hier_sep`, `hier_coll`, `hier_wlin`, `hier_wirr`, `hier_wtrans`, `hier_wcong`, `hier_wleast`) |
| Lifting between rungs; the count of a generated stage by terms; the least stage that is not small exists | §3.3 (7) | Lean (`rung_lift`, `rule_fun`, `ev_fun`, `evX_all`, `gen_count`, `next_exists`) |
| The sequence of stages; the iterated power sets; their finite sequence as a member of the level; the numbers | §3.3 (8) | Lean (`exists_stageSeq`, `pow_of_next`, `exists_powNames`, `exists_inner_seq`, `exists_numNames`) |
| **Lemma 3.2** | §3.3 (9) | Lean (`lemma_3_2`, `lemma_3_2_calm`, `l32_holds`), in the form stated in §3.3 (9), for an arbitrary model of NFU + Infinity |
| A tangle inside a host with a ladder of closed levels, the height a number of the host | §4.5 | Lean (`Host.tower_of_ladder`; `ext_ax`, `sing_ex`, `up_ex`, `inter_ex`, `compl_ex`, `cardinalOne_ex`, `vCross_ex`, `converse_ex`, `subset_ex`, `singletonImage_ex`, `insertion2_ex`, `insertion3_ex`, `typeLower_ex`), for an arbitrary host |
| The structure of Lemma 3.2 is a host with such a ladder; +, ×, 2ˣ and induction transfer between U and the host | §4.5 | Lean (`exists_host_tower`, `arith`, `mixed_ind`) |
| Terms evaluated in a flat model along sequences of levels; the axioms N at shifted positions; locality | note T3–T5 | Lean (`val_tot`, `val_fun`, `n_e1`, …, `n_m13b`, `loc`, `tr_loc`) |
| Ramsey's theorem inside the host with the exponent a number of the host; deciding one atom | note T6 | Lean (`ram_zero`, `ram_step`, `decide_atom`) |
| For q in the cut 𝖪ₜ, a truth assignment satisfying N below q | note T7 | Lean (`Host.sound_core`, `Model.sound`) |
| Good and correct states; the cut I of the terms; the term model is an `NFModel` | note T8–T9 | Lean (`dichotomy`, `correct_succ`, `correct_unique`, `exists_model_state`, `termModel`, `termModel_isNF`) |
| δ, ε, η are formulas of the language of NFU without parameters | note T10 | Lean (`bholds_delta2`, `bholds_eps2`, `bholds_eta2`, `sat_trB`, `addSpec_iff`, `mulSpec_iff`, `expSpec_iff`, `twSpec_iff`, `sat_nfDelta`, `sat_nfEps`, `sat_nfEta`) |
| **NFU + Infinity interprets NF**, in the form of §1 | §1 | **Lean (`nfu_inf_interprets_nf`)** |
| NF proves Infinity; NF refutes Choice (Specker); the universe of NF has no well-ordering | §8, item 1 | Lean (`nf_infinity`, `not_wellOrdered_le`, `no_wellOrdering_univ`, `nf_not_choice`; for `IsNF`: `IsNF.univ_not_finite`, `IsNF.not_choice`) |
| A model of NF is a model of NFU in which every object is a set; **NF interprets NFU + Infinity**; mutual interpretability | §8, item 1 | **Lean (`modelOfNF`, `nf_interprets_nfu_inf`, `nf_nfu_inf_mutually_interpretable`)** |

"Note" is the companion note `nfu_inf_interprets_nf_term_model_2026-11-15.md`.

The following steps belong to the original plan. Their status is as it was on 14 November. The theorem does not use them.

| Step | Where | Status |
|---|---|---|
| Finite-height tangles exist | §4.2 | Lean |
| **Transfer Lemma: the same in ZFC⁻, height a variable** | §4.3 | **inspection only** |
| Crabbé's conversion with bounds | §5.1–5.3 | proved; Lean, in semantic form (`conv`, `conversion`) |
| Pieces and their ambiguity | §5.4–5.5 | proved; Lean (`ev_pieces`, `pieces_wf`, `length_pieces`, `crabbe`) |
| The same inside U for nonstandard derivations | §5, §6 Step 1 | by the remark that the proofs are inductions on syntax; not machine-checked |
| Finite Ramsey with elementary bound | §6 | Lean (`ramsey`), with the Erdős–Rado bound function; the closed-form estimate of that function is textbook |
| Main Lemma, Steps 1 and 5–7, external form | §6.1 | Lean (`main_lemma`) |
| Typed NF₀ axioms hold in the strands of the Lean models | §4.1, §4.4 | Lean (`tangle_of_flat`) |
| The seventeen sentences axiomatise NF | §1, §4.4 | Lean (`isNF_of_axioms`, `axioms_of_nfModel`) |
| Main Lemma for NF, external form | §4.4 | Lean (`nf_no_refutation`) |
| Main Lemma inside U | §6 | proved from the above; not machine-checked |
| Interpretation existence | §7, Lemma 7.1 | cited |
| Cut elimination bound; shortening | §7, Lemma 7.2 | textbook |

What Lean does not check:

1. (Resolved on 15 November, evening.) The passage from "the translations of the axioms of NF hold in every model of U" to "U proves them" is now in Lean, by the completeness theorem of the library Foundation: `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`, `𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜`, `𝗡𝗙𝗨𝗜 ⋈ 𝗡𝗙`, and `𝗡𝗙 ⊢ σ → 𝗡𝗙𝗨𝗜 ⊢ nfuInterpretsNF σ`, for theories stated in Foundation's formula type, with NFU in the language of ∈ and = alone (`NFTheories.lean`, `NFUInterpretsNFEq.lean`, `NFInterpretations.lean`, `NFUShift.lean`, `NFUJensen.lean`). What that leaves unchecked is listed in `nf_syntactic_interpretation_2026-11-15.md`, §9.
2. That the Lean definitions say what they are meant to say: `NFUCut.Fml` and `NFUCut.Model` (NFU), `Model.Infinity`, and `ConNF.NF.IsNF` (extensionality and stratified comprehension). Everything else in the statement is Lean's own logic. For the statements about derivations the definitions to read are instead those of `NFTheories.lean` (stratification, `𝗡𝗙`, Jensen's `𝗡𝗙𝗨`, the axiom that the universe is not finite), about sixty lines in the language of ∈ and =.
3. (Resolved on 15 November: the converse direction, that NF interprets NFU + Infinity, is now in Lean, with Specker's theorem.)
4. The remarks listed under §3.1 and §3.3 as not formalised (renaming of derivations, the well-ordering principle inside 𝔏, a single sentence for the sequence of power sets, renaming for Separation) concern the original plan and are not needed for the theorem: the host axioms, including Separation and Collection for every formula, are proved in Lean for 𝔏 (`s_sep`, `s_coll`, `s_least`).

On reproducibility: the six new files (`Host.lean`, `HostTerm.lean`, `NFUTerm.lean`, `NFUInterpretsNF.lean`, `NFSpecker.lean`, `MutualInterpretability.lean`) were compiled with Lean 4.35.0 directly, against a build of the con-nf repository containing the `ConNF.NF.*` files of §2.4. They are not yet modules of the lake project, and the result has not been replayed with an external checker. `ConNF.NF.Hailperin` imports the con-nf model files, but the theorem uses from them only the definition of `NFModel`. **Superseded on the evening of 15 November:** all twelve files (these six and `NFChoiceForms.lean`, `NFTheories.lean`, `NFUInterpretsNFEq.lean`, `NFInterpretations.lean`, `NFUShift.lean`, `NFUJensen.lean`) are now one library of a lake project that requires con-nf and 69 modules of the library Foundation (commit `fbcfee52`) as dependencies, and `lake build` builds them. Each of the twelve and each `ConNF.NF.*` file was replayed in Lean's kernel with `leanchecker`, and the main theorems with everything they depend on were checked by the external type checker nanoda (15,313 and 21,624 declarations, no errors, only the three standard axioms). Details and the remaining gaps are in `nf_syntactic_interpretation_2026-11-15.md`, §8–§9; the project is in `nf-interp-2026-11-15.tar.gz`.

Separately, the Lean development also contains a direct proof that NF has a model (`exists_nf`). That is a consistency proof in Lean's logic. It is independent of the present theorem and does not rest on the Transfer Lemma.

**Added on 16 November, 00:05:** the definition of `NFModel` is now in its own file `ConNF/NF/NFModel.lean`, and `ConNF/NF/Hailperin.lean` no longer imports the con-nf model files. Everything in this document except `exists_nf` builds without con-nf (the project `standalone/` of the tarball; §12 of `nf_syntactic_interpretation_2026-11-15.md`).

**Added late on 15 November:** a model of NFU + Infinity is now built in Lean in the manner of Jensen 1969 (`JensenNFU.exists_model`, `SetTheory.Jensen.consistent_nfuInfinity : Consistent 𝗡𝗙𝗨𝗜`; files `NFUJensenModel.lean`, `NFUConsistent.lean`). With the present theorem it gives `consistent_nf_of_jensen : Consistent 𝗡𝗙` (`NFConsistentViaNFU.lean`), a second consistency proof of NF in Lean's logic in which no constant of con-nf's construction occurs. See §11 of `nf_syntactic_interpretation_2026-11-15.md`.

---

## References

- M. Crabbé, Ambiguity and stratification, *Fundamenta Mathematicae* 101 (1978), 11–17.
- K. Devlin, *Constructibility*, Springer, 1984.
- P. Erdős, R. Rado, Combinatorial theorems on classifications of subsets of a given set, *Proc. London Math. Soc.* 2 (1952), 417–439.
- P. Gerhardy, The role of quantifier alternations in cut elimination, *Notre Dame J. Formal Logic* 46 (2005), 165–171.
- P. Hájek, P. Pudlák, *Metamathematics of First-Order Arithmetic*, Springer, 1993.
- T. Hailperin, A set of axioms for logic, *J. Symbolic Logic* 9 (1944), 1–19.
- M. R. Holmes, S. Wilshaw, NF is consistent, arXiv:1503.01406; Lean formalisation: leanprover-community/con-nf.
- R. B. Jensen, On the consistency of a slight (?) modification of Quine's New Foundations, *Synthese* 19 (1969), 250–263.
- A. R. D. Mathias, The strength of Mac Lane set theory, *Ann. Pure Appl. Logic* 110 (2001), 107–234.
- P. Pudlák, Cuts, consistency statements and interpretations, *J. Symbolic Logic* 50 (1985), 423–441.
- E. P. Specker, The axiom of choice in Quine's New Foundations for mathematical logic, *Proc. Nat. Acad. Sci.* 39 (1953), 972–975.
- E. P. Specker, Typical ambiguity, in *Logic, Methodology and Philosophy of Science*, Stanford, 1962, 116–124.
- A. Visser, The interpretation existence lemma, in *Feferman on Foundations*, Springer, 2017, 101–144.
- A. Visser, Friedman-reflexivity, *Ann. Pure Appl. Logic* 173 (2022), 103160; arXiv:2111.14413.
