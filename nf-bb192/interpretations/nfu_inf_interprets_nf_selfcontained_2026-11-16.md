# NFU + Infinity interprets NF: a self-contained proof

16 November 2026.

## 0. About this document

This is a proof, written for a reader, that Jensen's set theory NFU with the axiom of Infinity interprets Quine's New Foundations. It is meant to be read from the first page to the last without the Lean files or the earlier notes.

**Status.** The theorem is formalised in Lean 4. The formal proof is checked by Lean's kernel, replayed with `leanchecker`, and checked by the independent type checker nanoda. This text follows the formal proof step by step: every numbered statement corresponds to a Lean theorem, whose name is given in brackets like this [`lemma_3_1`]. The text was written from the Lean development and has not been refereed. Where the text gives a sketch, the Lean statement named is the authority. Appendix B lists the files.

**What is proved in full here and what is quoted.** The parts that are specific to this theorem are proved: the strongly cantorian numbers and ladders (§§2–3), the adaptation of the constructible hierarchy to NFU (§4), the model of tangled types at a height that need not be a standard number (§5), the term model on a cut (§§6–7) and the removal of parameters (§8). Four classical results are used in forms that are stated precisely, with the adaptation proved and the textbook part sketched: Hartogs' theorem, the basic theory of the constructible hierarchy, the finite Ramsey theorem, and Hailperin's finite axiomatisation of NF. The completeness theorem for first-order logic is quoted.

**The tangled model.** Section 5 is the construction of the exposition *A model of tangled type theory from overlapping generic litters* (29 October 2026), which simplifies the construction of Holmes and Wilshaw. Here it is carried out inside a structure that satisfies only Separation and Collection, and at finite height.

**Terminology.** Several terms differ from those of the exposition, of Holmes and Wilshaw, and of the Lean files, where the inherited words said little about what the things do. Appendix C gives the correspondence.

**Conventions.** Theorems of this document are numbered within sections. "Number" always means a natural number of the model under discussion, which may be nonstandard; a number of the metatheory is called *standard*. ∎ ends a proof.

---

## 1. The theories and the theorem

### 1.1 Stratification, NF and NFU

A formula in the language of ∈ and = is **stratified** if natural numbers (types) can be assigned to its variables, the same type to all occurrences of a variable, so that every atomic formula x ∈ y has type(y) = type(x) + 1 and every atomic formula x = y has type(x) = type(y).

**NF** (Quine) has the axioms of equality, **extensionality**

> ∀x ∀y (∀z (z ∈ x ↔ z ∈ y) → x = y),

and **stratified comprehension**: for every stratified formula φ in which y is not free, the universal closure of

> ∃y ∀x (x ∈ y ↔ φ).

**NFU** (Jensen) is the same with extensionality weakened to objects that have members:

> ∀x ∀y (∃z (z ∈ x) → ∀z (z ∈ x ↔ z ∈ y) → x = y).

So NFU allows many objects without members. Comprehension still provides, for every stratified φ, an object whose members are exactly the x with φ; when no x satisfies φ, it provides some object without members.

**Infinity.** Call an object *finite* if it belongs to every family that contains every object without members and is closed under adjoining one element. Infinity says that the universal set is not finite. As one sentence, there is a family that contains every object without members, is closed under adjoining one element, and contains no universal set:

> ∃F [∀e (∀z z ∉ e → e ∈ F) ∧ ∀s ∈ F ∀b ∀s′ (∀z (z ∈ s′ ↔ z ∈ s ∨ z = b) → s′ ∈ F) ∧ ∀u (∀z z ∈ u → u ∉ F)].

Write **NFUI** for NFU + Infinity. No form of Choice is assumed.

**The version with a predicate for sets.** Most of the proof is carried out in a formulation that is easier to work in. Its language has ∈, = and a unary predicate S ("is a set"). Its axioms are: only sets have members; sets with the same members are equal; and for every stratified φ there is a *set* whose members are exactly the x with φ. (S imposes no condition on types.) Here there is exactly one empty set, and the other objects without members are the urelements. Infinity is the same sentence with "the empty set" in place of "every object without members"; it is equivalent to: the universe belongs to no Frege natural number (§2.1). Write **U** for this theory. Section 8.4 shows that NFUI interprets U, so the difference does not matter in the end. Until then "NFU + Infinity" means U.

### 1.2 Interpretations and the theorem

An **interpretation** of a theory T₂ in a theory T₁, both with equality, is given by a formula δ(x) of T₁ (the domain) and, for each relation symbol of T₂, a formula of T₁ with the same number of free variables, all without parameters. The translation φ ↦ φ* replaces each atomic formula by the corresponding formula, keeps equality as equality, and restricts every quantifier to δ. It is an interpretation if T₁ proves ∃x δ(x) and proves φ* for every axiom φ of T₂. It then follows that T₁ proves φ* for every theorem φ of T₂, and that T₂ is consistent if T₁ is.

**Theorem A.** NFUI interprets NF. That is, there are formulas δ(x) and ε(x, y) in the language of ∈ and =, without parameters, such that NFUI proves the translation of every axiom of NF, when ∈ is read as ε, equality as equality, and quantifiers are restricted to δ. [`nfuInterpretsNF`]

By the completeness theorem, Theorem A is equivalent to its semantic form, and that is the form in which it is proved:

**Theorem A′.** There are formulas δ and ε as above such that in every model M of NFUI the structure ({x ∈ M : M ⊨ δ(x)}, ε^M) is a model of NF.

Two remarks, neither used later. NF proves Infinity (Specker), so NF proves every axiom of NFUI and the identity is an interpretation in the other direction; the two theories are mutually interpretable and equiconsistent. Jensen proved that NFUI is consistent, so Theorem A gives a proof that NF is consistent.

### 1.3 The finite axiomatisation

NF has a finite axiomatisation, of a kind first found by Hailperin. We use the following list. Write {x} and {x, y} for singletons and unordered pairs and ⟨x, y⟩ = {{x}, {x, y}} for the Kuratowski pair.

**Definition 1.1 (NF₀).** A structure (V, ∈) is a model of **NF₀** if it satisfies extensionality, every x has a singleton and all x, y have an unordered pair, and the following sets exist:

1. *intersection*: for all x, y, a set whose members are the z with z ∈ x and z ∈ y;
2. *complement*: for every x, a set whose members are the z with z ∉ x;
3. *singleton image*: for every x, a set y with ⟨{z}, {w}⟩ ∈ y ⇔ ⟨z, w⟩ ∈ x;
4. *insertion two*: for every x, a set y with ⟨{{p}}, ⟨q, r⟩⟩ ∈ y ⇔ ⟨p, r⟩ ∈ x;
5. *insertion three*: for every x, a set y with ⟨{{p}}, ⟨q, r⟩⟩ ∈ y ⇔ ⟨p, q⟩ ∈ x;
6. *cross product with the universe*: for every x, the set of all ⟨q, r⟩ with r ∈ x;
7. *type lowering*: for every x, the set of all p such that ⟨q, {p}⟩ ∈ x for every q;
8. *converse*: for every x, a set y with ⟨p, q⟩ ∈ y ⇔ ⟨q, p⟩ ∈ x;
9. *the set of all singletons*;
10. *inclusion*: a set y with ⟨p, q⟩ ∈ y ⇔ p ⊆ q.

With singletons and pairs these are twelve existence statements. [`NFModel`]

**Theorem 1.2 (Hailperin).** Every model of NF₀ satisfies every instance of stratified comprehension. So NF₀ and NF have the same models. [`NFModel.isNF`]

The proof is in Appendix A. It is the only use of the finite axiomatisation: to obtain a model of NF it suffices to verify twelve statements.

Each of the twelve statements is stratified. Its **typed form** assigns types to its variables; for instance the typed form of "every x has a singleton" says that every x of type n has a singleton of type n + 1. The typed forms mention at most six types.

### 1.4 The plan

Fix a model M of U. Every construction below takes place in M, and the final definitions do not depend on M.

1. **Arithmetic and the strongly cantorian numbers (§2).** M has natural numbers (Frege's), and they satisfy Peano arithmetic. A number is *strongly cantorian* if it has a member x on which the map a ↦ {a} is a set. These numbers form an initial segment 𝖲 of the numbers that is closed under addition, multiplication and exponentiation. In general 𝖲 is a proper class.
2. **Ladders (§3).** For every strongly cantorian n there is a *ladder* of height n: sets T₀, …, Tₙ of one type, where T₀ is a copy of the numbers and the subsets of Tᵢ are coded one-to-one by the members of Tᵢ₊₁. This is n iterated power sets of ℕ, available inside M although M has no such thing as the power set at the same type.
3. **A host (§4).** Over a ladder one builds a level of the constructible hierarchy. It is a structure 𝔏 = (L, ε, <*) that satisfies Separation and Collection for all formulas and has a definable well-ordering. Inside 𝔏 there are iterated "power sets" in a weak sense, one for every three rungs of the ladder.
4. **A tangled model (§5).** Inside 𝔏, with d of those power sets, one builds a model of *tangled type theory* with d types: for all types b < a, the objects of type a behave as sets of objects of type b, and the typed forms of the twelve statements hold along every descending chain of types. The number d may be nonstandard, because it is an element of 𝔏 and the construction uses only Separation, Collection and induction in 𝔏.
5. **Truth assignments (§6).** A model of NF₀ is the same thing as a set of true atomic sentences, in a language with a function symbol for each of the twelve operations and a few witness functions, that satisfies a finite list N of universal axioms. Closed terms are coded by numbers. Evaluating terms in the tangled model along an increasing sequence of types, and applying Ramsey's theorem inside 𝔏 to make truth values independent of the sequence, gives for every q in a certain cut 𝖪 a set of numbers that satisfies all instances of N whose atomic sentences have codes below q.
6. **The term model (§7).** No single truth assignment for all terms is available, because the tangled models exist only at strongly cantorian heights. So the model is built on a cut: a finite piece of a truth assignment is *extendable* if for every q ∈ 𝖪 it extends to an assignment that satisfies N below q. Deciding the atomic sentences one at a time, true whenever the result is still extendable, gives pieces that cohere, and the terms in a shorter cut I with these truth values are a model of NF₀.
7. **Formulas (§8).** All of this is defined from the arithmetic of M by formulas that do not depend on M. Taking the least code in each equality class makes equality the real equality.

A word on the shape of steps 5–7, as motivation only. NF proves every axiom of U, so by the second incompleteness theorem one should not expect U to prove that NF₀ is consistent and then to build a model by the completeness theorem inside U. What U does prove is that there are no *small* inconsistencies, in the form: for every q in the cut, N has an assignment below q. That is enough for a Henkin-style construction on a shorter cut.

---

## 2. Arithmetic in U

Fix a model M of U. "Set" means a set of M, and a *class* is a subcollection of M defined by a formula with parameters. By comprehension, a class defined by a stratified formula is a set.

### 2.1 Numbers

Pairs are Kuratowski pairs, and a triple ⟨a, b, c⟩ is ⟨⟨a, b⟩, ⟨c, c⟩⟩, so that its three components have one type. A relation is a set of pairs. A relation between objects of the same type that is defined by a stratified formula is a set.

The **natural numbers** are Frege's: 0 = {∅}, the successor of n is n + 1 = {x ∪ {y} : x ∈ n, y ∉ x}, and ℕ is the intersection of all sets that contain 0 and are closed under successor. So the number n is the set of all sets with n elements. Infinity says V ∉ n for every n ∈ ℕ; equivalently, every member of a number omits some object.

**Lemma 2.1.** [`nat_ind_fml`, `nat_cases`, `rem_mem_of_succ`, `nat_disjoint`, `succ_inj`]
(a) Induction on ℕ holds for every condition given by a stratified formula with parameters.
(b) Every number is 0 or a successor, and 0 is not a successor.
(c) If y ∈ n + 1 and c ∈ y, then y ∖ {c} ∈ n.
(d) Two numbers with a common member are equal.
(e) Every number has a member, and successor is injective.

*Proof.* (a) The numbers that satisfy the condition form a set, which contains 0 and is closed under successor. (b) By induction. (c) By induction on n: a member of n + 2 is x ∪ {b} with x ∈ n + 1 and b ∉ x; removing b gives x, and removing some c ∈ x gives (x ∖ {c}) ∪ {b}, which is in n + 1 by the induction hypothesis. (d) By induction on one number for all values of the other, using (b) and (c). (e) The first part is induction with Infinity: if x ∈ n, some b is not in x, and x ∪ {b} ∈ n + 1. If m + 1 = n + 1, take x ∈ m and b ∉ x; then x ∪ {b} ∈ n + 1, so x ∈ n by (c), and m = n by (d). ∎

A function F from numbers to numbers is a **set function** if its graph is a set. Equations and inequalities between set functions define sets of numbers, so induction applies to them.

**Lemma 2.2 (recursion).** For set functions h and g there is exactly one set function F with F(a, 0) = h(a) and F(a, b + 1) = g(a, F(a, b)). [`exists_prec`, `prec_unique`]

*Proof.* Let A be the intersection of all sets of triples that contain every ⟨a, 0, h(a)⟩ and contain ⟨a, b + 1, g(a, c)⟩ whenever they contain ⟨a, b, c⟩. By induction on b, A contains a triple ⟨a, b, c⟩ for every a. The triples in A that arise from one of the two clauses form a set closed under the clauses, so every triple of A arises from a clause; then by induction on b the third component is determined by the first two. Uniqueness of F is an induction on an equation. ∎

So addition, multiplication and 2ˣ are set functions.

**Theorem 2.3.** With these operations, ℕ satisfies the axioms of Peano arithmetic, with induction for every formula of arithmetic with parameters. [`peano`, `pa_induction`]

*Proof.* The algebraic laws are inductions on equations between set functions. For the induction scheme, write a formula of arithmetic with the atoms x + y = z and x · y = z, restrict its quantifiers to ℕ, and replace those atoms by membership of a triple in the graph of + or of ×. The result is stratified: every number variable gets one type, and the two graphs are parameters. Apply Lemma 2.1(a). ∎

In particular the usual coding of finite objects by numbers is available in M. We use the pairing ⟨x, y⟩ = (x + y)² + x on numbers, and the coding of finite sets of numbers by the binary digits of a number: every finite set of numbers, and every set function between finite sets of numbers, has a code. [`exists_code`, `exists_code_rel`] The same proof as for Lemma 2.2 gives recursion into an arbitrary set: for a set D, a ∈ D and a set function g : D → D there is a unique set function f : ℕ → D with f(0) = a and f(n + 1) = g(f(n)). [`exists_rec_set`]

### 2.2 Strongly cantorian numbers

The map a ↦ {a} raises type by one, so its graph is not given by a stratified formula and in general it is not a set. This is the basic obstacle to doing ordinary mathematics in NFU, and the following notion measures where the obstacle is absent.

**Definition 2.4.** A set x is **strongly cantorian** if the restriction of a ↦ {a} to x is a set. A number is **strongly cantorian** if it has a strongly cantorian member. 𝖲 is the class of strongly cantorian numbers. [`SC`, `InS`]

Neither notion is given by a stratified condition, and 𝖲 need not be a set.

For a number n let T(n) be the number that contains {{a} : a ∈ x} for x ∈ n; it exists, by induction on n, and is unique by Lemma 2.1(d). Then T(0) = 0 and T(n + 1) = T(n) + 1. [`exists_T`, `T_zero`, `T_succ`]

**Lemma 2.5.** [`sc_emp`, `sc_adj`, `sc_subset`, `sc_pow`, `simg_mem_of_sc`, `pow_mem_expN`]
(a) ∅ is strongly cantorian. If x is, so are x ∪ {b}, every subset of x, and the set P(x) of all subsets of x.
(b) If x ∈ n is strongly cantorian, then {{a} : a ∈ x} ∈ n. Hence T(n) = n for strongly cantorian n.
(c) If y ∈ m and {{a} : a ∈ y} ∈ n, then P(y) ∈ 2ⁿ.

*Proof.* (a) Let f be the graph of a ↦ {a} on x. For y ⊆ x the image f″y is the set of singletons of the members of y, so ⋃ f″y = y. Hence the graph of y ↦ {y} on P(x) is the set of pairs ⟨y, {⋃ f″y}⟩ with y ⊆ x. This is given by a stratified formula with f as a parameter, in which y and {⋃ f″y} receive the same type. The other claims are similar and easier. (b) The condition on m, "for all y ⊆ x, if y ∈ m then f″y ∈ m", is stratified because f is a parameter; prove it by induction on m. (c) This is the equation |P(y)| = 2^{|y|}, with the type shift made explicit. It is an induction on m for all n, with the graph of 2ˣ as a parameter: P(x ∪ {b}) is the disjoint union of P(x) and {z ∪ {b} : z ∈ P(x)}. ∎

**Theorem 2.6.** 𝖲 contains 0, is closed downwards, and is closed under successor, addition, multiplication and n ↦ 2ⁿ. [`lemma_2_2`]

*Proof.* Successor: if x ∈ n is strongly cantorian, Infinity gives b ∉ x, and x ∪ {b} ∈ n + 1 is strongly cantorian. Downwards: every member of a + c includes a member of a (induction on c), and subsets of strongly cantorian sets are strongly cantorian. Exponential: if x ∈ n is strongly cantorian then {{a} : a ∈ x} ∈ n by Lemma 2.5(b), so P(x) ∈ 2ⁿ by (c), and P(x) is strongly cantorian by (a). Sum and product: a + b ≤ 2^{b+1} and a · b ≤ 2^{2b} for a ≤ b. ∎

Closure under the exponential is the one place where the proof uses a special property of NFU. It is what lets the cuts below absorb the fast-growing functions that Ramsey's theorem needs.

### 2.3 Cuts

A **cut** is a class of numbers that contains 0 and is closed downwards and under successor. 𝖲 is a cut.

**Lemma 2.7 (shortening).** Let C be a cut. Then C₁ = {n : ∀m ∈ C (m + n ∈ C)} is a cut included in C and closed under addition, and C₂ = {n : ∀m ∈ C₁ (m · n ∈ C₁)} is a cut included in C₁ and closed under addition and multiplication. More generally, if f is a non-decreasing set function and {n : f(n) ∈ C} is closed under successor, the same two steps applied to {n : f(n) ∈ C} give a cut K, closed under addition and multiplication, with f(n) ∈ C for all n ∈ K. [`Shortening.absorb`]

*Proof.* Direct from the definitions and the laws of arithmetic. For instance, if n, n′ ∈ C₁ and m ∈ C then m + n ∈ C, so (m + n) + n′ ∈ C. ∎

Every standard number belongs to every cut. A cut may contain nonstandard numbers, and it may be a proper class.

---

## 3. Ladders

**Definition 3.1.** A **ladder of height n** consists of sets T₀, …, Tₙ (the *rungs*) and set relations Eᵢ between Tᵢ and Tᵢ₊₁ for i < n, such that

- every subset of Tᵢ is {a : a Eᵢ b} for exactly one b ∈ Tᵢ₊₁;
- T₀ carries a zero and an injective successor, the zero is not a successor, and every subset of T₀ that contains the zero and is closed under successor is T₀.

Formally the rungs are given by one set of pairs ⟨i, a⟩ with a ∈ Tᵢ, and the relations by one set of triples ⟨i, a, b⟩. [`IsLadder`]

So Tᵢ₊₁ is a full power set of Tᵢ, presented with its membership relation Eᵢ. The point of the definition is that all the rungs have **one type**: a statement that relates members of different rungs through the Eᵢ is stratified, and the sets and relations it defines exist. Inside a ladder one can therefore reason as in ordinary type theory, with the height n as a number of M.

**Theorem 3.2.** The bottom rung of a ladder is isomorphic to ℕ by a set function. For every strongly cantorian n there is a ladder of height n. [`lemma_3_1`, `ladder_base_iso`, `exists_ladder`]

*Proof.* The first claim is Dedekind's argument: the intersection of all sets of pairs that contain ⟨0, zero⟩ and are closed under ⟨k, a⟩ ↦ ⟨k + 1, successor of a⟩ is the graph of an isomorphism.

For the second, the class of heights of ladders is a set, since "there is a ladder of height n" is stratified. A ladder of height 0 is ℕ itself. Suppose there is a ladder of height n, and n is strongly cantorian. Replace each rung Tᵢ by {{a} : a ∈ Tᵢ} and each Eᵢ by the relation it induces, and put the set P(Tₙ) of all subsets of the old top rung on top, with {a} E b ⇔ a ∈ b. The new rungs again have one type, one higher than before. The step i ↦ {{a} : a ∈ Tᵢ} raises the type of the index, so what one obtains directly is a sequence indexed by T(i) for i ≤ n; but T(i) = i for i ≤ n, because n is strongly cantorian and 𝖲 is closed downwards (Lemma 2.5(b)). So there is a ladder of height n + 1.

Now let n be strongly cantorian and suppose there is no ladder of height n. The set of heights of ladders contains 0, so there is a least number m that is not a height; 0 < m ≤ n, so m − 1 is strongly cantorian and is a height, and then m is a height. Contradiction. ∎

The proof shows why ladders are tied to strongly cantorian numbers. To add a rung one must take a power set, which lives one type up, and to bring the old rungs up to the new type one needs the singleton map on them as a set.

---

## 4. A host inside U

A ladder gives iterated power sets, but nothing like the axioms of set theory: there is no Collection, and no well-ordering of the rungs. The construction of §5 needs both. They are obtained in the classical way, by passing to a constructible hierarchy.

### 4.1 Hosts and regular levels

**Definition 4.1.** A **host** is a structure H = (W, ∈, <*) that satisfies

- extensionality, pairing, union, and the existence of an inductive set;
- Separation and Collection for every first-order formula in ∈, <* and =, with parameters;
- <* is a linear order, x ∈ y implies x <* y, and every nonempty definable class has a <*-least element. [`Host`]

A host has no power set axiom. It satisfies foundation, because the <*-least member of a set is ∈-minimal. It has a least inductive set ω, whose members are *the numbers of H*; induction on ω holds for definable properties, definitions by recursion on ω and along <* are available, and "finite" means "in bijection with a number of H". These are the usual consequences of Separation and Collection, and they are used freely. A *definable* class or relation is one defined by a formula with parameters; formulas are standard, but the parameters, and in particular the numbers of H, need not be.

**Definition 4.2.** A set K of a host is a **regular level** if

- K is transitive and ω ∈ K;
- every subset of a member of K is a member of K;
- for every definable relation R and every a ∈ K: if every u ∈ a has some v ∈ K with R(u, v), then some b ∈ K contains such a v for every u ∈ a;
- for every a ∈ K some member of K includes {b : b <* a}. [`Closed`, `closed_of`]

A **chain of regular levels of height d**, for a number d ≥ 1 of H, is a function Λ of H defined on 0, …, d + 1 with transitive values, Λ(i) ∈ Λ(i + 1), such that Λ(1), …, Λ(d + 1) are regular levels.

A regular level is a substitute for a regular cardinal. The second clause makes {x ∈ K : x ⊆ y} the power set of y ∈ K as far as K and everything above it are concerned. The third clause is regularity. In §5, "of size less than μ" will be replaced by "is a member of a regular level".

**Theorem 4.3.** Let d₀ be a number of M such that 3(d₀ + 3) + 2 is strongly cantorian. Then there are a host H, a chain Λ of regular levels of height d₀ + 1 in H, and a bijection num from the numbers of M onto the numbers of H such that:

(a) num(0) = ∅, num(n + 1) is the successor of num(n), and m < n ⇔ num(m) ∈ num(n);
(b) for every set function g on the numbers of M and every number k, the set of pairs ⟨num(i), num(g(i))⟩ with i ≤ k is a set of H;
(c) for every set c of H, the class {i : num(i) ∈ c} is a set of M.

[`Model.host`, `numIso`, `exists_inner_graph`, `isPred_mem`, `l32x_calm`]

Properties (b) and (c) connect the two notions of set. With them one gets:

**Corollary 4.4.** In the situation of Theorem 4.3:
(a) *Arithmetic.* Addition, multiplication and 2ˣ are definable in H, and num commutes with them. [`Model.arith`]
(b) *Mixed induction.* Let Q be a definable relation of H and g a set function on the numbers of M. If Q(num(0), num(g(0))) and Q(num(b), num(g(b))) implies Q(num(b + 1), num(g(b + 1))) for all b, then Q(num(b), num(g(b))) for all b. [`mixed_ind`]

*Proof of (b).* Fix k. By 4.3(b) the graph of g up to k, transported by num, is a set of H. With it as a parameter, "Q(x, the value at x)" is a definable property of the numbers x ≤ num(k) of H, and induction in H applies. No instance of comprehension in M is used, which matters because Q is not a condition of M at all. Part (a) is proved the same way, from the recursion equations. ∎

### 4.2 Proof of Theorem 4.3

Put m = d₀ + 2 and L = 3(m + 1). The number L + 2 = 3(d₀ + 3) + 2 is strongly cantorian, so by Theorem 3.2 there is a ladder T₀, …, T_{L+2}. All inductions below are on numbers of M or along set well-orderings, for stratified conditions; this is where having all rungs at one type is used.

**Step 1: pairing and sequences.** Every rung carries a set injection Tᵢ × Tᵢ → Tᵢ: Cantor's pairing on T₀, and on Tᵢ₊₁ the map sending (x, y) to the set of all pairs (0ᵢ, a) with a ∈ x and (1ᵢ, b) with b ∈ y, for two fixed members 0ᵢ ≠ 1ᵢ of Tᵢ. The injections for all rungs form one set, by induction on i. [`exists_pairing`] Consequently every set relation on Tᵢ is coded by a member of Tᵢ₊₁, and members of a rung can be read as finite sequences of members of the rung, of any length that is a number of M. [`rel_code`, `seq_code`] A lower rung maps one-to-one into every higher rung. [`rung_lift`]

**Step 2: Hartogs.** A *set well-ordering* is a set relation, reflexive and linear on its field, in which every subset of the field that has a member has a least member. Any two set well-orderings are comparable: one is isomorphic to an initial segment of the other, by a unique set isomorphism. [`wo_compare`] The proof is the usual one; the union of all partial isomorphisms is a set because the condition is stratified.

**Lemma 4.5 (Hartogs on a ladder).** For every rung Tᵢ with two rungs above it there is a set well-ordering Hᵢ, whose points are members of Tᵢ₊₂, such that every set well-ordering of a subset of Tᵢ is isomorphic to a proper initial segment of Hᵢ, and every proper initial segment of Hᵢ is isomorphic to a set well-ordering of a subset of Tᵢ. In particular the field of Hᵢ does not inject into Tᵢ. [`hartogs`, `hartogs_no_inj`]

*Proof.* Well-orderings of subsets of Tᵢ are coded by members of Tᵢ₊₁ (Step 1). "Embeds in" is a set preorder on the codes. Its equivalence classes are subsets of Tᵢ₊₁, so they are coded by members of Tᵢ₊₂, and Hᵢ is the induced order on those. For a well-ordering w of a subset of Tᵢ, the map sending a point of w to the class of the initial segment below it is an isomorphism of w onto the predecessors of the class of w. If the field of Hᵢ injected into Tᵢ, transporting Hᵢ along the injection would make Hᵢ isomorphic to a proper initial segment of itself. ∎

In ZF this is the statement that every set has a Hartogs number. The classes that the proof uses lie two types above Tᵢ, and that is why the statement is about a ladder: on a ladder, two types up is two rungs up at the same type.

Let θ be H_L, the Hartogs well-ordering of the rung L; its points are members of the top rung T_{L+2}. The points of θ are called **stages**. θ has a least stage, every stage has a successor, and θ has a least limit stage ν₀, whose predecessors are isomorphic to ℕ by a set function N. [`exists_omega_stage`, `limit_above`]

**Step 3: names and truth.** The hierarchy is built from *names*, all members of the top rung. Fix a set injection n ↦ n̂ of ℕ into the top rung. Formulas of the language with two binary relation symbols ε and <* are coded by numbers of M, standard or not.

- A **name of rank β** is a member of the top rung of the form (β, (φ̂, u)): a stage β, the code φ of a formula, and any member u of the rung, read as a finite sequence of parameters.
- By one recursion along the product of θ with ℕ [`wo_rec`, `exists_hierData`], define for every stage α and every formula code c the set of sequences t under which **c is true at stage α**; the variables range over the names of rank below α. At the same time define when two names **denote the same set**, written a ≈ a′: every member of a is ≈ to a member of a′, and conversely.
- The **members** of the name (β, (φ̂, u)) are the names a of rank below β such that φ is true at stage β under the sequence (a, u).
- The atomic formula v ε w is true if some name ≈ to the value of v is a member of the value of w.

So a name of rank β denotes the subset of the level below β that φ defines with the parameters u, and truth at stage α is truth in the structure 𝔏_α of all names of rank below α, taken up to ≈. This is the definition of Gödel's L_α, arranged as a single recursion on objects that all live in one rung. Names are not required to be well formed, no quotient is formed, and ≈ is part of the recursion; each of these avoids a separate recursion.

The following are proved by induction along θ and on codes. [`coin_hier`, `eps_rank`, `sim_refl`, `sim_symm`, `sim_trans`, `inv_hier`, `sim_iff_ext`, `def_name`, `up_name`, `level_name`, `pair_lim`, `union_lim`, `eps_wf`, `ordName_lt`, `ord_is_ordName`]

- Truth depends only on the values of the variables that occur, and satisfies Tarski's clauses.
- The levels are transitive: members of a name of rank below α are names of rank below α.
- ≈ is an equivalence relation and a congruence for truth; two names are ≈ if and only if they have the same members up to ≈ (extensionality).
- The names of rank α denote exactly the subsets of 𝔏_α that are definable over 𝔏_α with parameters. The levels increase, and each level is denoted by a name of the next rank.
- Limit levels are closed under pairs and unions.
- Foundation: every set of names that has a member and is closed under ≈ has a member none of whose members is in the set.
- For every stage ξ there is a name o_ξ of rank ξ that denotes the ordinal ξ of the hierarchy: the names that denote transitive sets of transitive sets are, up to ≈, the o_ξ, and o_ζ is a member of o_ξ exactly when ζ is below ξ.

**Step 4: the canonical order.** Order the names by rank, then by the number of the formula, then lexicographically by the parameters. Every set of names that has a member has a least member in this order [`pr_least`], names that tie are ≈ [`tie_sim`], and the *canonical* name of a set is its least name. Put x <* y if the canonical name of x precedes that of y. This is the relation that the symbol <* of the language means, so <* is available in formulas from the start. It is a linear order of each 𝔏_α compatible with ≈, every set of 𝔏_α with a member has a <*-least member [`hier_wlin`, `hier_wleast`], and members precede the sets they belong to, because a member of a name has smaller rank.

**Step 5: hulls and condensation.** Steps 5–7 are given as sketches; the mechanism is the classical one, and the exact closure rules are in the Lean file. In the textbook treatment of L one codes satisfaction inside the levels and forms Skolem hulls there. Here hulls are formed outside, as sets of M, and the truth definition of Step 3 is used directly.

Fix a stage δ. A set N of names of rank below δ is a **hull at δ** if it is closed under: the canonical names of its members; the parameters of its members; every name built from a rank, a formula and parameters that N already has; and **least witnesses**: for every formula and all parameters in N, if some name of rank below δ makes the formula true at stage δ, then the <*-least such name is in N, and the same at every stage that N knows about. (N *knows about* a stage if it contains a fixed name that marks the stage. There is one more closure rule, of a bookkeeping kind: for every small stage that N knows about, in the sense defined in Step 6, N contains a recorded generator.) [`ClosedR`]

**Lemma 4.6 (condensation).** Let N be a hull at δ. The stages that N knows about are isomorphic, in their order, to the stages below some stage δ̄ ≤ δ, and this isomorphism extends to a map π from N to the names of rank below δ̄ which is onto up to ≈, preserves ≈, ε and <*, and preserves truth: a formula is true at δ under a sequence from N if and only if it is true at δ̄ under the image sequence. [`cond_all`, `step_elem`]

*Proof.* By induction on rank, π is defined and preserves members. Preservation of truth is an induction on formulas; the quantifier step is the Tarski–Vaught test, which holds because N contains least witnesses. ∎

**Step 6: small stages, absorption, Separation and Collection.** Fix a stage ν. A stage ρ above ν is **generated from ν** by a name b if the only hull at ρ that contains b and all names of rank below ν is the set of all names of rank below ρ. A stage is **ν-small** if some stage at or above it is generated from ν. The **next stage after ν** is the least stage that is not ν-small, if there is one. [`Gen`, `Small`, `IsNext`]

In the language of L, "ρ is ν-small" says that L_ρ has the size of L_ν in the sense of L, and the next stage after ν is the successor cardinal of ν in L. Lean never speaks of cardinals of L, and that this hierarchy is L is neither proved nor needed.

**Lemma 4.7.** Let κ be the next stage after ν, and suppose θ has at least two stages above κ. [`next_lim`, `next_absorb`, `next_sep`, `next_coll`, `hier_sep`, `hier_coll`]
(a) κ is a limit stage.
(b) *Absorption.* If a name of rank above κ has all its members among the names of rank below γ, for some stage γ below κ, then it is ≈ to a name of rank below κ.
(c) *Separation.* For every name a of rank below κ, every formula and all parameters of rank below κ, the set of members of a at which the formula is true at stage κ is denoted by a name of rank below κ.
(d) *Collection.* If for every member y of a there is a name z of rank below κ at which a formula is true at stage κ, then there is a stage γ below κ such that z can always be found with rank below γ.

*Proof (sketch).* (b) Let x be the name and δ a stage above its rank. Form the hull N at δ of the names of rank below ν and one further name from which x and the stage γ can be recovered. The stage γ is ν-small, and the bookkeeping rule is there so that N then contains every name of rank below γ. Apply condensation: π is the identity up to ≈ on the names of rank below γ, hence π(x) has the same members as x and π(x) ≈ x. The collapsed stage δ̄ is generated from ν [`hull_collapse`], so it is ν-small, so δ̄ is below κ, and π(x) has rank below δ̄.
(c) The set in question is definable over 𝔏_κ, so it is denoted by a name of rank κ, whose members are members of a and so have rank below the rank of a. Apply (b).
(d) is the corresponding regularity statement. It is proved by a hull argument of the same kind: a hull that contains a and the parameters contains a least witness for every member of a, and condensation shows that these witnesses have rank below a single stage below κ. ∎

**Step 7: the count.** It remains to see that next stages exist, and this is the one place where sizes are compared in M.

**Lemma 4.8.** Suppose the stages below ν map one-to-one into the rung Tᵢ by a set function, and i + 3 ≤ L. Then the next stage κ after ν exists, and the stages below κ map one-to-one into Tᵢ₊₃. [`gen_count`, `next_exists`]

*Proof.* If ρ is generated from ν by b, every name of rank below ρ is the value of a *term* built from names of rank below ν and b by the closure rules of a hull. Terms are finite sequences over a set that injects into Tᵢ, so they are coded in Tᵢ, and sending a stage below ρ to the set of terms whose value is o of that stage maps the stages below ρ one-to-one into Tᵢ₊₁. Hence the predecessors of any ν-small stage form a well-ordering isomorphic to a well-ordering of a subset of Tᵢ₊₁. By Lemma 4.5 the well-ordering Hᵢ₊₁, on Tᵢ₊₃, is longer than all of those, and it is itself isomorphic to a proper initial segment of θ, because Tᵢ₊₃ maps into T_L. So θ has a stage that is not ν-small; let κ be the least. The stages below κ are ν-small, so they embed in Hᵢ₊₁ and map one-to-one into Tᵢ₊₃. ∎

A stage is sent to a *set* of terms because choosing one term would need a well-ordering of the terms. That costs one rung, and the comparison with a Hartogs well-ordering costs two more. This is the reason for the factor 3.

**Step 8: the sequence of stages.** The stages below ν₀ map one-to-one into T₀. By induction on k ≤ m + 1, using Lemma 4.8 with i = 3k, there are stages ν₀ < ν₁ < … < ν_{m+1} with each νₖ₊₁ the next stage after νₖ, and the stages below νₖ map one-to-one into T_{3k}. The induction needs 3k + 3 ≤ L for k ≤ m, which is the choice L = 3(m + 1). [`exists_stageSeq`] Put **κ = ν_{m+1}**. Since θ has no last stage, there are stages above κ.

**Step 9: the host.** Let W be the set of names of rank below κ divided by ≈, with ε and <*. Then H = (W, ε, <*) is a host:

- extensionality, foundation, pairing and union hold at every limit stage, and κ is one (Step 3);
- the name o_{ν₀} denotes an inductive set, and ν₀ is below κ;
- Separation and Collection are Lemma 4.7(c) and (d) with ν = ν_m, for every formula;
- the properties of <* are Step 4.

For i ≤ m let Λ(i) be the set denoted by the name of the level at νᵢ; it is a member of H because νᵢ is below κ. Λ(0) ∈ Λ(1) ∈ … ∈ Λ(m), and each is transitive. For i ≥ 1, Λ(i) is a regular level: it contains the subsets of its members by absorption at νᵢ (Lemma 4.7(b) with ν = νᵢ₋₁, applied to subsets that are members of H); it satisfies the collection clause by the proof of Lemma 4.7(d), with the formula evaluated at stage κ instead of νᵢ [`next_coll_at`]; it covers the initial segments of <* because <* compares ranks first and νᵢ is a limit stage [`cover_lim`]; and ω, denoted by o_{ν₀}, is a member. Since m = d₀ + 2, Λ is a chain of regular levels of height d₀ + 1.

The numbers of H are the sets denoted by the o_ξ with ξ below ν₀, and num(i) is the set denoted by o_{N(i)}. Property (a) is Step 3. Property (b) is an induction on k in M, adding one pair at a time, by closure of limit levels under pairs and unions. Property (c) holds because all names lie in one rung, so "o_{N(i)} is a member of c" is a stratified condition on i. ∎

---

## 5. A tangled model of finite height in a host

Throughout this section H is a host and Λ a chain of regular levels of height d, where d ≥ 1 is a number of H. Everything is done inside H: "set", "finite", "function" are in the sense of H, and every induction is induction in H on a definable property. Nothing depends on d being standard. The level Λ(d) is called the **pool**: the atoms and labels of the construction are members of it. The objects of the model will be members of Λ(d + 1).

### 5.1 The target

**Definition 5.1.** A **tangled model of height d** in H consists of definable relations "x is an object of level a" and "z ∈ x between the levels b < a", for levels 1, …, d, such that

- every level has an object;
- *extensionality*: for all levels b < a, two objects of level a with the same members of level b are equal;
- *the twelve statements, typed*: for every descending chain of levels of the required length, the typed form of each statement of Definition 1.1 holds, with the types of the statement interpreted by the levels of the chain. [`FlatM`]

For example, the typed form of "singleton" for levels a > b says: for every object z of level b there is an object of level a whose only member of level b is z. The typed form of "intersection" for a > b says: for objects x, x′ of level a there is an object of level a whose members of level b are the common members of level b of x and x′. The others are formed in the same way and are written out in §6.2.

A tangled model is a model of tangled type theory with d types, presented in one sort. The essential point is that the same objects of level a serve as sets of objects of *every* lower level b, and are determined by their members at each one.

**Theorem 5.2.** Every chain of regular levels of height d in a host gives a tangled model of height d. [`Host.tower_of_ladder`, `Tower.flat`, `flat_ax`]

### 5.2 The idea

An object of level a must have an extension at every lower level b, and by Cantor's theorem it cannot be an arbitrary one. The model is a symmetric one, in the manner of Fraenkel and Mostowski: an object keeps its members *directly* at one lower level and *by proxy* at every other, and it has a finite *support*. Three devices make this work.

- **Direct and proxy extensions.** There is a bottom level 0 of *atoms*, which is scaffolding, and a set of *labels*, with an incidence relation between atoms and labels. Each label b gives an object at every level, its *label object*, whose members are the atoms incident to b. A label may carry inside it a description of an object x of some level; its label object at another level δ is then a **proxy** of x at δ, and x is its **original**. An object is given by its **direct extension**, a set D of objects of one lower level β. Its extension at any other lower level δ is the **proxy extension** of D: the set of all proxies at δ of the members of D. Every object has many proxies at every other level, and the proxies of different objects, or between different pairs of levels, are different; so D can be recovered from its proxy extension.
- **Parity.** A set Y of objects of level δ may be both a direct extension and the proxy extension of some D. Then two candidates have the same extension at δ. Call D the **source** of Y and follow the chain Y, D, … of sources; it is finite. Keep a candidate exactly when the source chain of its direct extension has even length. Of two clashing candidates exactly one is kept.
- **Paths.** In tangled type theory the members at level γ of an object x of level α and the members at level γ of a member y of x are unrelated. So a permutation must be able to act independently on atoms and labels "seen along" different descending chains of levels. A support entry is therefore an atom or a label together with a *path*, the chain of levels along which it is seen.

In the work of Holmes and Wilshaw and in the exposition, the label objects are called *litters*. Appendix C lists the correspondence of terms.

In the exposition the incidence structure is a saturated random bipartite graph of cardinality μ = ℵ_{ω+1}, and the construction is a recursion of length ω in ZFC + GCH. In a host there are no such cardinals. The changes are these.

| In the exposition | In a host |
|---|---|
| saturated random bipartite graph of size μ | an explicit bipartite graph in which each vertex lists its earlier neighbours (§5.3) |
| "of size less than μ" | "is a member of the regular level" |
| an injective map of the atoms and labels into μ, used to order them | the global order <* |
| a proxy family of μ labels for each original, allocated by a recursion of length μ | all labels that carry the original inside them |
| templates are equivariant functions, and are counted by beth numbers | templates are sets, a support and a pattern, and are members of the next regular level (§5.7) |
| recursion on ω, then Ramsey and compactness | induction on a number d of H; no model of infinite height is formed |
| full comprehension | the twelve statements |

### 5.3 The pool

**Definition 5.3.** An **atom** is a member of the pool of the form atom(X, η) = ⟨0, ⟨X, η⟩⟩, and a **label** is a member of the pool of the form label(r, ξ, X, η) = ⟨1, ⟨r, ⟨ξ, ⟨X, η⟩⟩⟩⟩. An atom a and a label b are **incident** if b ∈ X_a or a ∈ X_b, where X_v is the component X of v. [`atom`, `label`, `Adj`]

The component X of a vertex is the set of *earlier* vertices of the other kind that it is incident to: whatever X contains lies in the transitive closure of the vertex and therefore precedes it in <*. The components r and ξ of a label are its **route** and its **original**; they will say between which levels the label is a proxy, and of what. The component η is free.

**Lemma 5.4 (genericity).** Let K be a regular level and let P, N, Z ∈ K with P ∩ N = ∅. Then there is an atom in K that is incident to every label in P, to no label in N, and is not in Z. Likewise, for any r, ξ ∈ K there is a label in K with route r and original ξ that is incident to every atom in P, to no atom in N, and is not in Z. [`Closed.exists_atom`, `Closed.exists_label`]

*Proof.* Take a = atom(P, ⟨N, Z⟩); it is in K because regular levels are closed under pairs. It lists the labels in P. A label b ∈ N is not listed by a, and b does not list a, because b precedes a in <*. And a ∉ Z because Z precedes a. The same for labels. ∎

This one-line lemma replaces saturation. Two consequences: distinct labels are incident to different sets of atoms [`Closed.label_ext`], and the set L_b of atoms incident to b is a set, a member of Λ(d + 1).

### 5.4 Paths, tokens, proxy families

The **levels** are the numbers 0, …, d of H; the levels 1, …, d are *proper*. A **path** is a set p of proper levels; its **type** is its greatest element, or 0 if p = ∅. A **token at level β** is a pair ⟨t, p⟩ with p a path of type β and t an atom or, if p ≠ ∅, a label. For a set P of levels above the type of p, the token **raised by P** is ⟨t, p ∪ P⟩. A **tuple at level β** is a finite sequence of tokens at level β. [`IsPath`, `IsTok`, `IsTup`]

The construction proceeds by induction on the proper level α. When stage α begins, the following are available for every level β < α: the set τ_β of **objects of level β**; a group G_β of permutations of the tokens at level β, acting on τ_β; a set N_β of **templates**; and, for every template c ∈ N_β and every tuple S at level β of the right shape, an object obj_β(c, S) ∈ τ_β, **the object described** by c and S. A pair (c, S) is a **description** at β. At level 0, τ₀ is the set of atoms, the templates are the pairs (k, i) with i < k, a description is such a pair with a sequence of k atoms, and it describes the i-th of them.

**Definition 5.5.** Let γ ≠ δ be levels with δ proper and (c, S) a description at γ. The **proxy family** F_{γδ}(c, S) is the set of all labels with route ⟨γ, δ⟩ and original ⟨c, S⟩. A label in a proxy family is a **proxy label**, and the entries of S are its **dependencies**. A label in no proxy family is **free**.

Proxy families of different descriptions, or with different routes, are disjoint, since the route and the original are components of the label. By Lemma 5.4 every proxy family realises every incidence pattern, and so do the free labels. The dependencies of a label are inside it, so they precede it in <*.

### 5.5 The structure of a stage and freedom of action

Fix a proper level α. For a nonempty path p of type α let δ = min p and P = p ∖ {δ}.

**Definition 5.6.** A label token ⟨b, p⟩ at level α is **bound**, of **kind** (γ, δ, c) and with **dependencies** the entries of S raised by P, if b ∈ F_{γδ}(c, S), P ≠ ∅ and γ < min P. A set of tokens is **closed** if it contains the dependencies of its bound tokens. A **partial isomorphism** of stage α is an injective function between sets of tokens at level α, with closed domain, that preserves paths, the distinction between atoms and labels, incidence between tokens with the same path, and kinds together with dependencies, and that sends only bound tokens to bound tokens. An **automorphism** is a partial isomorphism that is a permutation of all the tokens at level α. G_α is the set of automorphisms. [`Col`, `PIso`, `IsAut`]

The token ⟨b, p⟩ stands for the label object of b at level δ, seen from level α along the chain P. That b is a proxy of an object of level γ matters for the object at level min P that it belongs to only if that object could have its direct extension at level γ, that is, if γ < min P; this is the condition in the definition. A proxy label is thus bound on some paths and not on others, and a free label is bound on none. Dependencies of a token have vertices that precede its own, so the closure of a finite set of tokens is finite, by induction along <*.

G_α is a set: an automorphism is a subset of a set in Λ(d + 1), hence a member of Λ(d + 1), and G_α is cut out of Λ(d + 1) by Separation. The same remark applies to every set formed below, and it is the reason the chain of regular levels has one more level than the model.

**Lemma 5.7 (one step).** Let K be a regular level included in the pool and θ a partial isomorphism whose range is included in a member of K. Let v be a token outside the domain of θ whose dependencies are in the domain and whose template, if v is bound, is in K, and let Z ∈ K. Then θ extends to v with a value in K outside Z. [`piso_step_atom`, `piso_step_flex`, `piso_step_col`, `piso_step`]

*Proof.* If v is an atom token, apply Lemma 5.4 with P the labels whose tokens on the same path are the θ-images of labels incident to v, and N the images of the others. If v is a label token that is not bound, the same with a route that belongs to no proxy family. If v is bound of kind (γ, δ, c) with dependencies S raised by P, the dependencies have images; lower them by P to get a tuple S′, and apply Lemma 5.4 with route ⟨γ, δ⟩ and original ⟨c, S′⟩. The proxy family F_{γδ}(c, S′) exists for *every* tuple S′ of the right shape, because a template describes an object for every such tuple. The new token has exactly the required kind and dependencies. ∎

**Theorem 5.8 (freedom of action).** Every partial isomorphism of stage α that is a member of the pool extends to an automorphism. [`foa`]

*Proof.* The tokens at level α form a set, well-ordered by <*. Define by recursion along it an increasing chain of partial isomorphisms, at each token extending first the domain to the token and to everything it depends on, dependencies first, and then the range, by Lemma 5.7 applied to the inverse. At every step the map built so far is defined on tokens below a given one, so by the covering and collection clauses of a regular level it is a subset of a member of the pool, and Lemma 5.7 applies. The union is an automorphism. ∎

In the exposition this is a back-and-forth of length μ, and regularity of μ keeps the intermediate maps small. Here the recursion is along <*, and the two clauses of Definition 4.2 that have not been used so far do that work.

Three consequences are used below.

- *Moving a token.* If the vertex of a token v comes after the vertices of a finite set S of tokens, some automorphism fixes S pointwise and moves v. [`move`]
- *Derivatives.* For π ∈ G_α and β < α, the tokens at level α whose path is u ∪ {α} with u of type β are permuted by π, and deleting α identifies them with the tokens at level β. The induced permutation π_β is in G_β, and (πσ)_β = π_β σ_β. [`der_aut`]
- *Conjugation into a lower level of the chain.* A partial isomorphism with range in Λ(α) extends to an automorphism that maps a given finite set of tokens into Λ(α). [`conj_into`]

### 5.6 Objects

**Definition 5.9.** A **candidate** of stage α is the *empty object*, or a pair ⟨β, D⟩ with β < α and D a nonempty subset of τ_β. Its extension at β is D, its **direct extension**. Its extension at a proper level δ < α, δ ≠ β, is the **proxy extension**

> Prox_δ(D) = { lab(b) : b ∈ F_{βδ}(c, S) for some description (c, S) at β with obj_β(c, S) ∈ D },

where lab(b) = ⟨0, L_b⟩ is the **label object** of b. An automorphism π acts by π · ⟨β, D⟩ = ⟨β, π_β[D]⟩. A finite set of tokens **supports** a candidate if every automorphism that fixes the tokens fixes the candidate. [`IsAlt`, `IsLit`, `ActRaw`, `SuppSet`]

**Lemma 5.10.** [`alt_sub`, `alt_transport`, `good_all`]
(a) *Injectivity.* Prox_δ(D) determines β and D.
(b) *Transport.* π_δ[Prox_δ(D)] = Prox_δ(π_β[D]) for π ∈ G_α.
(c) *Finite chains.* There is no infinite sequence Y₀, Y₁, … of nonempty sets with each Yᵢ a proxy extension of Yᵢ₊₁.

*Proof.* (a) The routes of the labels give β, their originals give the descriptions of members of D, and every object of level β has a description (Lemma 5.14(c) at stage β). (b) On the path {δ, α} the token of a label b ∈ F_{βδ}(c, S) is bound of kind (β, δ, c) with dependencies S raised by {α}. An automorphism preserves kinds and dependencies, so it sends b into F_{βδ}(c, π_β[S]); and obj_β(c, π_β[S]) = π_β(obj_β(c, S)) because description is equivariant. (c) If Y₀ = Prox_δ(Y₁) and Y₁ is itself a proxy extension, the members of Y₁ are label objects. Let lab(b) ∈ Y₀ with b least in <*. Its original describes some lab(c) ∈ Y₁, and then the token of c is among the tokens that b depends on, so c precedes b. So the least label strictly decreases along the chain. ∎

For Y a set of objects of a proper level δ < α, a **source** of Y at stage α is a candidate ⟨β, X⟩ with β ≠ δ and Prox_δ(X) = Y; it is unique by (a). Iterating gives the **source chain** of Y, finite by (c).

**Definition 5.11.** A candidate ⟨β, D⟩ is **kept** if the source chain of D has even length. An **object of level α** is a kept candidate with a finite support. τ_α is the set of objects of level α. [`Retained`, `IsObj`]

**Theorem 5.12.** [`ext_stage`, `symm_comp`]
(a) *Extensionality.* Two objects of level α with the same nonempty extension at a proper level δ < α are equal, and a nonempty object has a nonempty extension at every proper lower level.
(b) *Symmetric comprehension.* Let β < α and let X be a set of objects of level β that is mapped to itself, through π ↦ π_β, by every automorphism fixing a finite set S of tokens. Then X is the extension at β of an object of level α supported by S.

*Proof.* (a) Let x = ⟨β, D⟩ and y = ⟨β′, D′⟩. If β = β′ = δ, the extensions are D and D′. If neither is δ, use Lemma 5.10(a). If β = δ ≠ β′, then D = Prox_δ(D′), so ⟨β′, D′⟩ is the source of D and the two source chains differ in length by one; x and y are not both kept. (b) If the source chain of X has even length, take ⟨β, X⟩. Otherwise take the source of X, whose chain is shorter by one. By Lemma 5.10(b) and (a) the automorphisms fixing S fix this candidate. ∎

So the empty object, singletons, pairs and label objects exist at every level above their members. A singleton is never a proxy extension, because every proxy family is infinite.

### 5.7 Templates

It remains to define the templates of stage α and the objects they describe, so that the later stages have proxies for the objects of level α. In the exposition a template is an equivariant function, and one counts the templates to see that there is room for their proxy families. Here a template must be a *set that is a member of the pool*, because it has to occur inside labels.

Say that a token is **in the sub-pool** if its vertex is a member of Λ(α).

**Definition 5.13.** Let x = ⟨β, D⟩ be an object of level α. Its **pattern** is the pair of β and the set of all descriptions (c′, U) at β, with U a tuple in the sub-pool, that describe a member of D. A **template** of stage α is a pair c = ⟨S₀, pat⟩ of a tuple S₀ in the sub-pool and the pattern of an object x that S₀ supports. For a tuple S at level α of the shape of S₀,

> obj_α(c, S) = g · x if S = g S₀ for some g ∈ G_α, and the empty object otherwise. [`IsPat`, `IsName`, `IsDec`]

**Lemma 5.14.** [`pat_inj`, `dec_surj_stage`, `dec_equi_low`]
(a) Two objects supported by the same tuple of the sub-pool and with the same pattern are equal. So a template determines its object, and obj_α is well defined.
(b) obj_α is equivariant, and obj_α(c, S) is supported by the entries of S.
(c) Every object of level α is described by some description.
(d) Every template of stage α is a member of Λ(α + 1).

*Proof.* (a) Let x = ⟨β, D⟩ and y = ⟨β, D′⟩ be supported by S₀ and have the same pattern, and let z ∈ D. By (c) at stage β, z = obj_β(c′, U′) for some description. By conjugation into Λ(α), some automorphism g fixes S₀ and moves the tokens of U′ raised by {α} into the sub-pool; put U = g_β U′. Then g fixes x, so obj_β(c′, U) = g_β z ∈ D; the description (c′, U) is in the pattern of x, hence of y; so g_β z ∈ D′, and z ∈ D′ because g fixes y. (b) If g S₀ = g′ S₀ then g⁻¹g′ fixes S₀ and hence x. (c) An object has a finite support; conjugate it into the sub-pool. (d) S₀ is a member of Λ(α). The pattern is a set of pairs of a template of a lower stage, which is a member of Λ(α) by induction, and a tuple in Λ(α); so it is a subset of a member of Λ(α + 1), and regular levels contain the subsets of their members. ∎

Part (d) is what replaces the count of templates. For α < d the templates of stage α are members of the pool, so by Lemma 5.4 the proxy families F_{αδ}(c, S) are available at all later stages. The set τ_α itself is a member of Λ(d + 1).

### 5.8 The induction

The data of a stage (τ_α, G_α, the action, N_α, obj_α) are defined from the data of the lower stages by formulas, so by recursion in H there is a function that assigns to every proper level its data. The statements of §§5.5–5.7 for stage α use only those statements for lower stages. Their conjunction is a definable property of α, and induction in H on α ≤ d proves it for every proper level. [`invT_step`, `invT_all`]

This is the step that the con-nf formalisation does not provide: there, the height is an ordinal of the metatheory. Here d is an element of H, and it may be a nonstandard number.

### 5.9 The twelve statements

For levels b < a put z ∈ x, between the levels b and a, if z is in the extension of x at b. Extensionality is Theorem 5.12(a). Membership is preserved by the action: the extension at b of π · x is the image of the extension of x under π_b. [`mem_equi`]

Fix a descending chain of proper levels t₀ > t₁ > … > tₙ. The group G_{t₀} acts on the objects of every level of the chain by iterated derivatives along the chain, and every object of a level of the chain has a finite set of tokens at level t₀ whose pointwise stabiliser fixes it. [`supp_raise`]

**Lemma 5.15 (predicative comprehension).** Let φ be a formula in which every variable ranges over one of the levels t₁, …, tₙ and membership is between levels of the chain. Then for all parameters, the set of objects of level t₁ that satisfy φ is the extension at t₁ of an object of level t₀. [`pred`, `sat_equi`]

*Proof.* Satisfaction of φ is invariant under the action of G_{t₀}, by induction on φ. So the set is fixed by the stabiliser of the union of the supports of the parameters; apply Theorem 5.12(b). ∎

Eleven of the twelve statements are instances of Lemma 5.15: the set whose existence is asserted is defined by a formula whose variables range over levels below the level of the set. [`sing_ex`, `up_ex`, `inter_ex`, `compl_ex`, `cardinalOne_ex`, `vCross_ex`, `converse_ex`, `subset_ex`, `singletonImage_ex`, `insertion2_ex`, `insertion3_ex`]

The exception is *type lowering*: the set {p : ∀q ⟨q, {p}⟩ ∈ x} lies three levels below x, and its definition mentions x. For it one needs:

**Lemma 5.16 (lowering).** Let α > β > γ be proper levels and X a set of objects of level γ. If the set of singletons, at level β, of the members of X is the extension at β of an object y of level α, then X is the extension at γ of an object of level β. [`lower`]

*Proof.* Let S be a finite closed support of y, and let S_β be the set of tokens of S whose path has second greatest element β, with α deleted from their paths. We show that S_β supports X at stage β; then Theorem 5.12(b) applies. Let π ∈ G_β fix S_β and let x ∈ X. Take a finite closed set T of tokens at level β that supports {x}. The map that is the identity on S and sends each token of T raised by {α} to its π-image raised by {α} is a partial isomorphism of stage α: the two parts agree where they overlap, because a token of S with a path through β is in S_β raised and is fixed by π; and raising by {α} makes no token of T bound that was not bound before, since that happens only to labels on the one-element path {β}, and T has none of those. [`piso_raise`, `piso_bun`] By freedom of action it extends to π* ∈ G_α. Then π* fixes y, and (π*)_β agrees with π on T, so the singleton of π_γ(x) is in the extension of y, and π_γ(x) ∈ X by extensionality. ∎

*Type lowering, typed.* Define the set of triple singletons of the wanted members at the level just below x by Lemma 5.15, and apply Lemma 5.16 three times. [`typeLower_ex`]

This proves Theorem 5.2: the objects of level a are the members of τ_a, membership between levels is membership in the extension, and both are definable in H from the function of §5.8. ∎

---

## 6. Terms and truth assignments

We return to the model M of U. This section produces, for every number q in a cut 𝖪, a "model of NF₀ up to q": a truth assignment for the atomic sentences with codes below q.

### 6.1 The language of terms and the axioms N

Take a language with eighteen function symbols, one for each operation of NF₀ and six for witnesses.

| tag | symbol | reads | tag | symbol | reads |
|---|---|---|---|---|---|
| 0 | sing(x) | {x} | 9 | CV(x) | converse |
| 1 | up(x, y) | {x, y} | 10 | C1 | the set of all singletons |
| 2 | IN(x, y) | x ∩ y | 11 | SB | the inclusion relation |
| 3 | CO(x) | complement | 12 | D(x, y) | a point where x and y differ |
| 4 | SI(x) | singleton image | 13 | P1(p) | first component of the pair p |
| 5 | I2(x) | insertion two | 14 | P2(p) | second component of p |
| 6 | I3(x) | insertion three | 15 | EL(p) | the member of the singleton p |
| 7 | VC(x) | V × x | 16 | WT(p, x) | a counterexample to p ∈ TL(x) |
| 8 | TL(x) | type lowering | 17 | WS(p, q) | a counterexample to p ⊆ q |

Write op(x, y) for up(sing(x), up(x, y)).

**Codes.** Closed terms are coded by numbers of M, with ⟨x, y⟩ = (x + y)² + x: the term f(x, y) has the code ⟨f, ⟨x, y⟩⟩ + 1. All symbols are treated as binary, a symbol of smaller arity ignoring the extra arguments. *Every number is a term*: a number not of the form ⟨f, ⟨x, y⟩⟩ + 1 with f < 18 is a constant with no properties. This avoids a predicate "is a term". The atomic sentence t ∈ t′ has the code 2⟨t, t′⟩ and t = t′ has the code 2⟨t, t′⟩ + 1. Arguments have smaller codes than the term, and terms have smaller codes than the atomic sentences in which they occur. [`tm`, `aIn`, `aEq`]

**The axioms N.** For all terms in place of the variables:

- (E1) x = x. (E2) x = y ∧ x = z → y = z. (E3) x = x′ ∧ y = y′ ∧ x ∈ y → x′ ∈ y′. (E4) x = x′ → sing(x) = sing(x′), and x = x′ ∧ y = y′ → up(x, y) = up(x′, y′).
- (M1) (D(x, y) ∈ x ↔ D(x, y) ∈ y) → x = y.
- (M2) y ∈ sing(x) ↔ y = x. (M3) z ∈ up(x, y) ↔ z = x ∨ z = y. (M4) z ∈ IN(x, y) ↔ z ∈ x ∧ z ∈ y. (M5) z ∈ CO(x) ↔ ¬ z ∈ x.
- (M6) op(sing z, sing w) ∈ SI(x) ↔ op(z, w) ∈ x.
- (M7) op(sing sing p, op(s, r)) ∈ I2(x) ↔ op(p, r) ∈ x. (M8) op(sing sing p, op(s, r)) ∈ I3(x) ↔ op(p, s) ∈ x.
- (M9) p ∈ VC(x) → p = op(P1 p, P2 p) ∧ P2 p ∈ x; and p = op(s, r) ∧ r ∈ x → p ∈ VC(x).
- (M10) p ∈ TL(x) → op(s, sing p) ∈ x; and op(WT(p, x), sing p) ∈ x → p ∈ TL(x).
- (M11) op(p, s) ∈ CV(x) ↔ op(s, p) ∈ x.
- (M12) p ∈ C1 → p = sing(EL p); and p = sing s → p ∈ C1.
- (M13) op(p, s) ∈ SB ∧ r ∈ p → r ∈ s; and (WS(p, s) ∈ p → WS(p, s) ∈ s) → op(p, s) ∈ SB.

These are the statements of Definition 1.1 with the inner existential quantifiers replaced by the witness symbols, and extensionality in the form (M1). Each is a propositional combination of at most four atomic sentences. Split into implications there are 22 clauses.

A **truth assignment** is a set τ of numbers of M, read as the set of codes of true atomic sentences.

**Definition 6.1.** τ **satisfies N below q** if every instance of every clause, all of whose atomic sentences have codes below q, is true under τ. [`NSat`]

This depends only on the part of τ below q, and it is preserved when q decreases.

### 6.2 Evaluating terms in a tangled model

Let H be a host as in Theorem 4.3, so that the numbers of M and of H are identified by num and arithmetic agrees. Let a tangled model of height D in H be given.

A **level sequence** is an increasing sequence v of levels, a function of H defined on the numbers below some L. A term is evaluated at a *position* k < L, and its value is an object of level v(k). The arguments of a symbol are evaluated at shifted positions k + s:

| symbol | shift of the arguments | symbol | shift |
|---|---|---|---|
| sing, up | −1 | CV | 0 |
| IN, CO | 0 | D, WS | +1 |
| SI | −1 | P1, P2 | +2 |
| I2, I3, VC | −2 | EL | +1 |
| TL | +3 | WT | −1 and +3 |

The shifts are those that the typed forms of the statements dictate: a singleton lives one level above its member, the argument of TL three levels above the result, and so on. For an object y of level a = v(k) and values c₁, c₂ of the arguments, the condition θ_f(y; c₁, c₂) says that y is what the term f(c₁, c₂) should denote. Write aⱼ = v(k − j) and uⱼ = v(k + j); let {x}_b and {x, y}_b be the singleton and pair at level b, and ⟨x, y⟩_{b,c} = {{x}_c, {x, y}_c}_b.

| f | θ_f(y; c₁, c₂) |
|---|---|
| sing | y = {c₁}_a |
| up | y = {c₁, c₂}_a |
| IN | for all z of level a₁: z ∈ y ⇔ z ∈ c₁ ∧ z ∈ c₂ |
| CO | for all z of level a₁: z ∈ y ⇔ z ∉ c₁ |
| SI | for all z, w of level a₄: ⟨{z}_{a₃}, {w}_{a₃}⟩_{a₁,a₂} ∈ y ⇔ ⟨z, w⟩_{a₂,a₃} ∈ c₁ |
| I2 | for all p, q, r of level a₅: ⟨{{p}_{a₄}}_{a₃}, ⟨q, r⟩_{a₃,a₄}⟩_{a₁,a₂} ∈ y ⇔ ⟨p, r⟩_{a₃,a₄} ∈ c₁ |
| I3 | the same with ⟨p, q⟩_{a₃,a₄} on the right |
| VC | for all p of level a₁: p ∈ y ⇔ p = ⟨q, r⟩_{a₁,a₂} for some q, r of level a₃ with r ∈ c₁ |
| TL | for all p of level a₁: p ∈ y ⇔ for all q of level a: ⟨q, {p}_a⟩_{u₂,u₁} ∈ c₁ |
| CV | for all p, q of level a₃: ⟨p, q⟩_{a₁,a₂} ∈ y ⇔ ⟨q, p⟩_{a₁,a₂} ∈ c₁ |
| C1 | for all p of level a₁: p ∈ y ⇔ p = {q}_{a₁} for some q of level a₂ |
| SB | for all p, q of level a₃: ⟨p, q⟩_{a₁,a₂} ∈ y ⇔ every member of level a₄ of p is in q |
| D | y ∈ c₁ and y ∈ c₂ do not both hold or both fail |
| P1 | c₁ = ⟨y, r⟩_{u₂,u₁} for some r of level a |
| P2 | c₁ = ⟨q, y⟩_{u₂,u₁} for some q of level a |
| EL | c₁ = {y}_{u₁} |
| WT | ⟨y, {c₁}_a⟩_{u₂,u₁} ∉ c₂ |
| WS | y ∈ c₁ and y ∉ c₂ |

For the symbols 0–11 the condition is the matrix of the typed form of the corresponding statement, so by the axioms of a tangled model some y satisfies it. These rows are the typed forms promised in §5.1.

**Definition 6.2.** The **value** of the term n at the position k of v is the <*-least object y of level v(k) with θ_f(y; values of the arguments), if n = f(n₁, n₂), the shifted positions are positions of v, and there is such a y; otherwise it is the <*-least object of level v(k). [`Val`, `vl`]

The definition is by recursion on the code, in H. It can be stated without a recursion theorem: the value is c if (n, k, c) belongs to some set all of whose members satisfy the clause relative to the set.

**Lemma 6.3.** For a level sequence v, every number n and every position k of v there is exactly one value; it is an object of level v(k); and when the positions that the symbol reaches lie in v, it satisfies its condition θ_f in the cases 0–11, and in the cases 12–17 whenever something does. [`val_tot`, `val_fun`, `val_ob`, `val0_spec`–`val17_spec`]

*Proof.* Induction on n in H, for all k at once. ∎

The atomic sentence t ∈ t′ **is true at the position k** of v if the value of t at k is a member of the value of t′ at k + 1; t = t′ is true at k if the values of t and t′ at k are equal. [`Tin`, `Teq`]

**Lemma 6.4 (N in a tangled model).** For every level sequence long enough around a base position, each clause of N holds when its atomic sentences are evaluated at the following positions relative to the base. [`n_e1`, …, `n_m13b`]

| axiom | positions |
|---|---|
| (E1), (E2), (M2)–(M5), (M11), (M12) | all at 0 |
| (E3) | x = x′ at 0, y = y′ at 1, the memberships at 0 |
| (E4) | premises at −1, conclusion at 0 |
| (M1) | D ∈ x and D ∈ y at 0, x = y at 1 |
| (M6) | … ∈ SI(x) at 0, op(z, w) ∈ x at −1 |
| (M7), (M8) | … ∈ I2(x) at 0, op(p, r) ∈ x at −2 |
| (M9) | p ∈ VC(x) and p = op(…) at 0, the memberships in x at −2 |
| (M10) | p ∈ TL(x) at 0, the others at +3 |
| (M13) | op(p, s) ∈ SB at 0, the others at −3 |

*Proof.* The positions are chosen so that every term is evaluated at one position throughout the clause. Each clause is then Lemma 6.3 for the symbol concerned, with the injectivity of singletons and pairs between levels. For (M1): if the values of x and y at position 1 differ, extensionality in the tangled model gives an object of the level below that is in exactly one of them, so the value of D(x, y) is such an object, and the premise fails. For the second halves of (M10) and (M13): if the selected "counterexample" is not one, there is none. ∎

So in a tangled model the axioms N hold *with shifts*. The shifts are the stratification of NF₀ showing through. To get rid of them one needs the truth of an atomic sentence not to depend on the position, and that is what Ramsey's theorem will give.

**Lemma 6.5 (locality).** The truth value of the atomic sentence with code i at a position of a level sequence depends only on the 2(5i + 6) + 1 levels of the level sequence around that position. That is: if two level sequences agree on windows of that size around positions p and p′, the atomic sentence is true at p in the one if and only if it is true at p′ in the other. [`loc`, `tr_loc`]

*Proof.* Induction on the code in H. One symbol reaches at most five positions away, and arguments have smaller codes. ∎

### 6.3 Ramsey's theorem in the host

For numbers r, q, Q of H let **Ram(r, q, Q)** be the statement: for every set c and every increasing sequence F of length Q there is an increasing subsequence g of F of length q such that all r-element sets of values of g agree about membership in c. Let **rstep(x) = 2 · 2^{2^{x+1} · (x+1)}**. [`Ram`, `rstep`]

**Lemma 6.6.** Ram(0, q, q); and if Ram(r, q, Q₀) and rstep(Q₀) ≤ l, then Ram(r + 1, q, l). [`ram_zero`, `ram_step`]

*Proof.* The step is the usual proof of Ramsey's theorem. From a sequence of length l extract a subsequence of length Q₀ + 1 that is *pre-homogeneous*: whether B ∪ {x} is in c, for an r-element set B and a later value x, does not depend on x. This takes Q₀ + 1 rounds, each of which fixes the next value and halves the remainder once for every r-element subset of the values fixed so far; rstep bounds the length needed. Then apply Ram(r, q, Q₀) to the colouring of r-element sets B by "B ∪ {x} ∈ c for later x". All of this is finite combinatorics about sets of H and is carried out in H. ∎

For an increasing sequence e of levels, a code i and a radius R, say that **i is decided true on e** if the atomic sentence i is true at the position p of w, for every increasing subsequence w of e and every position p of w at distance at least R from both ends of w. *Decided false* is the same with "false". [`AllT`, `AllF`]

**Lemma 6.7.** If 5i + 6 ≤ R, e′ is an increasing sequence of levels of length Q, and Ram(2R + 1, q, Q), then e′ has an increasing subsequence of length q on which i is decided, true or false. [`decide_atom`]

*Proof.* Colour each set B of 2R + 1 values of e′ by the truth value of i at the middle position of the increasing enumeration of B. Take a homogeneous subsequence g. For a subsequence w of g and a position p as above, the window of w around p is such a set B, and by locality the truth value at p in w is the colour of B. ∎

### 6.4 Truth assignments exist

**Lemma 6.8.** Let e be an increasing sequence of levels of length at least 2R + 6 on which every i < q is decided at radius R. Then the set of the i < q that are decided true satisfies N below q. [`nsat_of_dec`]

*Proof.* Given an instance of a clause with atomic sentences below q, evaluate it in the level sequence e, shifted as in Lemma 6.4, with a base position chosen so that every position used is at distance at least R from both ends; the length of e allows this. The truth value of each atomic sentence at its position is then the decided one. Lemma 6.4 gives the clause. ∎

Now the fast-growing function. Let **tw** be the set function on the numbers of M with tw(0) = 0 and tw(b + 1) = rstep(tw(b)) (Lemma 2.2). The class {n : tw(n) ∈ 𝖲} is a cut, by Theorem 2.6, since rstep is built from addition, multiplication and the exponential. Let **𝖪** be the cut obtained from it by shortening (Lemma 2.7). So 𝖪 is closed under addition and multiplication, and tw(n) is strongly cantorian for every n ∈ 𝖪. [`tw`, `InKt`, `kt_add`, `kt_mul`, `kt_tw`]

**Theorem 6.9.** For every q ∈ 𝖪 there is a set of numbers of M that satisfies N below q. [`Model.sound`]

*Proof.* Put R = 5q + 6, m = 2R + 6 and n₀ = m + (2R + 1) · q. Then n₀ ∈ 𝖪, so d₀ = tw(n₀) is strongly cantorian, and so is 3(d₀ + 3) + 2. Theorem 4.3 gives a host H with a chain of regular levels of height d₀ + 1, and Theorem 5.2 a tangled model in H of height d₀ + 1.

*Ramsey numbers.* By mixed induction (Corollary 4.4(b)) on j, with Lemma 6.6: Ram(j, tw(a), tw(a + j)) holds in H for all a, j. Mixed induction is needed because tw is a set function of M and Ram is a statement of H.

*Deciding the atomic sentences below q.* By mixed induction on k ≤ q: every increasing sequence of levels of length tw(m + (2R + 1) · k) has a subsequence of length tw(m) on which every i < k is decided at radius R. The step applies Lemma 6.7 to the code k, with Ram(2R + 1, tw(m + (2R + 1)k), tw(m + (2R + 1)(k + 1))); a code that is decided on a sequence stays decided on its subsequences.

*Conclusion.* The sequence of all levels has length d₀ + 1 ≥ tw(m + (2R + 1) · q). So there is a sequence e of levels of length tw(m) ≥ 2R + 6 on which every i < q is decided. By Lemma 6.8 the set of the num(i), i < q, decided true on e satisfies N below q in H. It is a set of H by Separation, so by Theorem 4.3(c) the set τ of the corresponding numbers of M is a set of M; and it satisfies N below q, because num respects the coding of terms. [`Host.sound_core`] ∎

This is the only place where the tangled model, the host and Ramsey's theorem are used. What comes out is a statement of pure arithmetic with set parameters: *for every q ∈ 𝖪 some set satisfies N below q*.

---

## 7. The term model on a cut

From here on everything is arithmetic in M, with sets of numbers as parameters.

A **state** is a pair (k, S) of a number and a set of numbers; only the members of S below k matter. Two sets **agree below k** if they have the same members below k.

**Definition 7.1.** [`Sat1`, `Good`, `T1`, `Correct`, `InJ`, `InI`]
- (k, S) is **extendable** if for every q ∈ 𝖪 some set agrees with S below k and satisfies N below q.
- **Add(k, S)** holds if some S′ agreeing with S below k has k ∈ S′ and (k + 1, S′) extendable. ("The atomic sentence k can be made true.")
- (k, S) is **greedy** if (i, S) is extendable for all i ≤ k and, for every i < k: i ∈ S ⇔ Add(i, S).
- J is the class of k ∈ 𝖪 for which some state (k, S) is greedy.
- **I** is the cut obtained from J by shortening (Lemma 2.7).

A greedy state decides the atomic sentences in the order of their codes, making each one true whenever that can be done while staying extendable. This is Henkin's construction, with "consistent" replaced by "extendable".

**Lemma 7.2 (dichotomy).** If (k, S) is extendable, then Add(k, S) holds or some S′ agreeing with S below k has k ∉ S′ and (k + 1, S′) extendable. [`dichotomy`]

*Proof.* Otherwise (k + 1, S ∪ {k}) is not extendable, witnessed by some q₁ ∈ 𝖪, and (k + 1, S ∖ {k}) is not extendable, witnessed by some q₀ ∈ 𝖪. Since (k, S) is extendable and q₀ + q₁ ∈ 𝖪, some τ agrees with S below k and satisfies N below q₀ + q₁. If k ∈ τ, then τ agrees with S ∪ {k} below k + 1 and satisfies N below q₁; otherwise it agrees with S ∖ {k} and satisfies N below q₀. Contradiction. ∎

**Lemma 7.3.** [`correct_zero`, `correct_succ`, `correct_unique`, `inJ_hyp`, `i_add`, `i_mul`, `i_sub`, `i_tm`]
(a) (0, ∅) is greedy.
(b) A greedy state of length k has a greedy extension of length k + 1.
(c) Two greedy states agree below the smaller of their lengths.
(d) J is a cut, and I is a cut closed under addition and multiplication with I ⊆ J ⊆ 𝖪. Hence I is closed under the eighteen term constructors, and atomic sentences between terms in I have codes in I.

*Proof.* (a) is Theorem 6.9: that (0, ∅) is extendable says exactly that for every q ∈ 𝖪 some set satisfies N below q. (b) is the dichotomy: add k if Add(k, S) holds, leave it out otherwise. (c) By induction on i for "the two states agree below i", which is a condition on i given by a stratified formula because the two states are sets. At each step, membership of i in either state is equivalent to Add(i, ·), and Add(i, S) depends only on S below i. (d) J is closed under successor by (b) and downwards by definition; the rest is Lemma 2.7, and the term constructors are polynomials. ∎

Note where induction is and is not used. "Extendable" quantifies over the class 𝖪 and is not a stratified condition, so there is no induction on it. Lemma 7.3(b) is a single step, (c) is an induction on a set condition, and the passage from J to I by shortening replaces the induction one would like to have.

**Definition 7.4.** For terms t, t′: **ε(t, t′)** holds if some greedy state of length i + 1 contains i, where i is the code of t ∈ t′; **η(t, t′)** is the same with the code of t = t′. [`Eps`, `Eta`]

**Lemma 7.5.** For every finite list of numbers in I there are k and a set S that satisfies N below k, such that every number of the list is below k and, for every atomic sentence of the list, its code is in S if and only if ε, respectively η, holds of its terms. [`exists_model_state`]

*Proof.* Take k ∈ I above the list. Then k ∈ J, so there is a greedy state (k, S′); it is extendable and k ∈ 𝖪, so some S agrees with S′ below k and satisfies N below k. By Lemma 7.3(c), the greedy states of length i + 1 agree with S′ at i, for every i < k. ∎

**Theorem 7.6.** The relation η is an equivalence relation on I and a congruence for ε and for the term constructors sing and up, and the quotient of I by η with the relation induced by ε is a model of NF₀. Hence it is a model of NF. [`termModel`, `termModel_isNF`]

*Proof.* Every clause of N holds for ε and η at terms in I: an instance has at most four atomic sentences, all between terms in I; apply Lemma 7.5 to the list of their codes and read the clause off Definition 6.1. Now (E1)–(E4) say that η is an equivalence relation and a congruence; (M1) is extensionality; (M2) and (M3) give singletons and pairs; and each of (M4)–(M13) gives one of the ten sets of Definition 1.1, the term constructors providing the sets and the witness symbols the inner existential quantifiers. The last sentence is Hailperin's theorem (Theorem 1.2). ∎

---

## 8. From the model to an interpretation

### 8.1 No parameters

The conditions "t ∈ I", ε(t, t′) and η(t, t′) of §7 were defined in M from the following ingredients only: the set ℕ with 0 and 1; addition and multiplication; the function tw; the class 𝖲 of strongly cantorian numbers; quantification over numbers; and quantification over sets of numbers (the states and the assignments).

Each ingredient is defined in M by a formula of the language of U without parameters. ℕ is the intersection of the sets that contain 0 and are closed under successor. The graph of addition is the unique set that is a total function on ℕ × ℕ and satisfies the two recursion equations; it exists by Lemma 2.2, and it is unique by an induction that is available because any candidate is a set. The same for multiplication, 2ˣ and tw, each from the earlier graphs. "n is strongly cantorian" is: n ∈ ℕ and some member of n is strongly cantorian. So:

**Theorem 8.1.** There are formulas δ₀(x), ε₀(x, y), η₀(x, y) of the language of U, without parameters and not depending on M, such that in every model M of U: δ₀ defines I, and ε₀ and η₀ define ε and η on it. Consequently, in every model of U the structure defined by δ₀ and ε₀, divided by the relation defined by η₀, is a model of NF. [`NFUCut.nfu_inf_interprets_nf`, `nfDelta`, `nfEps`, `nfEta`]

The formulas are large and are never written out. In the formal proof they are produced by a translation from a two-sorted language of arithmetic, in which they have a few thousand symbols before the terms are expanded, and every fact about them is proved by recursion on their construction.

### 8.2 Equality

In Theorem 8.1 the equality of NF is interpreted by the relation η. To interpret it by equality, choose representatives.

**Theorem 8.2.** Let δ(x) say: δ₀(x), and no number y < x has η₀(y, x). Then in every model M of U, the structure ({x : M ⊨ δ(x)}, ε₀^M) is a model of NF. [`dom_isNF`, `exists_minTm`, `minTm_unique`]

*Proof.* Every η-class in I has a least member. The class {y ≤ x : η(y, x)} is not obviously a set, because η is defined with a quantifier over 𝖪. But by Lemma 7.5 there is a *set* S that gives every atomic sentence y = x with y ≤ x the truth value that η gives it, since the codes of these sentences are below a common bound in I. So the class is a set, and the least number principle applies. The representatives form a structure isomorphic to the quotient of Theorem 7.6. ∎

### 8.3 Derivations

By Theorem 8.2, for every axiom φ of NF, the translation φ* under (δ, ε₀) holds in every model of U. By the completeness theorem, U proves φ*. Also U proves ∃x δ(x). So:

**Theorem 8.3.** U, that is NFU + Infinity with a predicate for sets, interprets NF. [`SetTheoryU.interpretsNF`]

The derivations are obtained from the completeness theorem and are not exhibited.

### 8.4 Jensen's NFU, without a predicate for sets

It remains to pass from NFUI, in the language of ∈ and = alone, to U.

In a model of NFUI the objects with members behave as the sets of U, but there is a difficulty with the empty set. U has exactly one set without members. NFUI has many objects without members, extensionality says nothing about them, and in general none of them is definable. An interpretation has no parameters, so one cannot say "let the empty set be this one". The empty set of the interpreted structure must therefore be an object *with* members; its members must then be given to another object; and so on. This is Hilbert's hotel, and it needs an infinite definable sequence of sets. Infinity supplies one: the positive Frege numbers.

Work in a model of NFUI. The number **1** is the set of all singletons, and the successor of a number k is the set of all x ∪ {y} with x ∈ k and y ∉ x; let **P** be the intersection of all sets that contain 1 and are closed under successor. These are defined from ∈ alone, and they do not mention an empty set. By Infinity every member of P has a member, the members of P are pairwise distinct, and successor is injective on P (as in Lemma 2.1).

**Definition 8.4.** x ∈′ y if either y = k + 1 for some k ∈ P and x ∈ k, or y ∉ P and x ∈ y. Let S′(y) say that y has a member, in the original sense. [`MemS`]

So 1 has no members in the new sense; the number k + 1 has the old members of k; and every object outside P keeps its members.

**Theorem 8.5.** In every model of NFUI, the structure with the same universe, the membership ∈′ and the predicate S′ is a model of U. Hence NFUI interprets U. [`not_memS_one`, `memS_succ_succ`, `memS_ext`, `exists_codeS`, `shift_infinity`, `setModel_models_nfus`, `interpretsNFUs`]

*Proof.* *Only sets have members.* An object without old members is not in P, so it has no new members.

*Extensionality.* Let y, y′ have old members and the same new members. If neither is in P, they have the same old members and are equal. If y = k + 1 and y′ = k′ + 1, then k and k′ have the same members, so k = k′. If y = k + 1 and y′ ∉ P, then y′ has the members of k, so y′ = k ∈ P, a contradiction. If y = 1, it has no new members, while every other object with old members has new ones: k + 1 because k has a member, and an object outside P because it keeps its own.

*Comprehension.* Let φ be a stratified formula of the language of U. Replacing ∈ by the formula for ∈′ and S by "has a member" gives a formula that is again stratified, with all types raised by one, because the definition of x ∈′ y mentions members of x. So there is an object c whose old members are exactly the objects that satisfy φ in the new structure. If nothing satisfies φ, the required set is 1. If c is a member k of P, it is k + 1. Otherwise it is c itself, which has members and is not in P.

*Infinity.* The new structure is a model of NFU with a predicate for sets, and its universe is not finite in its own sense; this is checked directly, with the code of the set of codes of finite sets as the witness. ∎

**Proof of Theorem A.** Compose the interpretation of U in NFUI (Theorem 8.5) with the interpretation of NF in U (Theorem 8.3). ∎

### 8.5 Remarks

1. **The converse.** NF proves Infinity, by Specker's theorem that NF refutes Choice. Every other axiom of NFUI is an axiom of NF or follows from one. So the identity interprets NFUI in NF, and the two theories are mutually interpretable. This is formalised as well [`nfInterpretsNFU`, `nfuMutualNF`], but it is not part of this document.
2. **Consistency.** With a model of NFUI, Theorem A′ gives a model of NF. Jensen's theorem that NFUI is consistent is formalised by a direct construction [`Jensen.consistent_nfuInfinity`], and with it the consistency of NF [`consistent_nf_of_jensen`].
3. **What the theorem does not say.** An interpretation gives a proof of Con(NFUI) → Con(NF) in a weak arithmetic, by a general argument. That argument is not carried out here or in Lean.
4. **Choice.** No form of Choice in M is used anywhere. The well-ordering needed in §5 is the order <* of the constructible hierarchy, and the only choices made in M are least elements of sets of numbers.

---

## Appendix A. Hailperin's theorem

**Theorem 1.2.** Every model (V, ∈) of NF₀ satisfies stratified comprehension.

*Sketch.* The proof is the classical one, organised as follows. [`NFModel.comprehension`]

*Relations.* By the axioms, the sets of ordered pairs in V are closed under intersection and complement (relative to V × V, which is the cross product with the universe of the universe), converse, and the cross product with the universe on either side. From the inclusion relation one obtains the membership relation {⟨{x}, y⟩ : x ∈ y} [`NFModel.exists_memRel`], and from the set of singletons and the Boolean operations the identity relation. Insertion two and insertion three turn a set of pairs into a set of triples in which a new coordinate is inserted, and type lowering, with complement, gives projection: {p : ∃q ⟨q, {p}⟩ ∈ x}. Singleton image raises the type of a relation by one.

*Assignments.* Fix a list of variables with types. An assignment of values a₁, …, aₙ to them is coded by one element of V: the right-nested tuple ⟨a₁′, ⟨a₂′, … ⟩⟩, where aᵢ′ is aᵢ under as many iterated singletons as are needed for the two components of each pair to have the same type. The types of the variables determine how many.

*Induction on formulas.* For every formula φ that is stratified with the given types, the set of codes of assignments that satisfy φ exists. For the atomic formulas xᵢ ∈ xⱼ and xᵢ = xⱼ, start from the membership or identity relation, raise it by singleton image to the level of the codes, and insert the remaining coordinates. For ¬ and ∧ use complement and intersection. For a quantifier, the set for ∀x φ in a context is obtained from the set for φ in the context extended by x, by projection.

*Comprehension.* Given a stratified φ(x) with parameters, take the set of codes of satisfying assignments, intersect with the codes whose parameter coordinates are the given parameters, and project to the coordinate of x. The result is, up to iterated singletons, the set {x : φ(x)}, and type lowering removes the singletons. ∎

The classical source is Hailperin's paper. The list of Definition 1.1 is the one used in the Lean formalisation of the Holmes–Wilshaw proof; it is not Hailperin's original list.

---

## Appendix B. The Lean files

The numbered statements above correspond to Lean theorems in these files. All of them compile with Lean 4.35.0 and Mathlib without `sorry`; the theorems depend on the axioms `propext`, `Classical.choice`, `Quot.sound` only; and the project builds from Mathlib and the library Foundation (first-order logic and the completeness theorem) alone.

| Part of this document | File | Lines |
|---|---|---|
| §2: numbers, arithmetic, strongly cantorian numbers, cuts | `ConNF/NF/NFUCut.lean`, `NFUArith.lean` | 1,242 + 1,987 |
| §3: ladders; coding of finite sets and of formulas | `ConNF/NF/NFULadder.lean`, `NFUSat.lean`, `NFUSound.lean` | 1,554 + 1,084 + 1,502 |
| §4.2, Steps 1–3: pairing, Hartogs, the hierarchy | `ConNF/NF/NFUHartogs.lean` | 8,537 |
| §4.2, Steps 4–9: the canonical order, hulls, the stages | `ConNF/NF/NFUConstr.lean` | 7,705 |
| §4.1 and §5: hosts, regular levels, the tangled model | `Host.lean` | 8,453 |
| §6.1–§6.3 and Lemma 6.8: terms, evaluation, Ramsey | `HostTerm.lean` | 4,392 |
| Theorem 4.3, Corollary 4.4, Theorem 6.9 | `NFUTerm.lean` | 3,622 |
| §7 and §8.1 | `NFUInterpretsNF.lean` | 1,799 |
| §8.2 | `NFUInterpretsNFEq.lean` | 262 |
| §1.1 (the theories), §8.3 | `NFTheories.lean`, `NFInterpretations.lean` | 315 + 1,196 |
| §8.4 | `NFUShift.lean`, `NFUJensen.lean` | 393 + 734 |
| Appendix A | `ConNF/NF/NFModel.lean`, `Hailperin.lean` | 106 + 914 |

The directory name `ConNF/NF` is historical; none of these files uses the con-nf formalisation.

**Differences between this text and the Lean proof.** They are of presentation. The Lean proof is about an arbitrary model M of U throughout, as here. The host is a Lean structure built from M; its formulas are standard formulas. In §4 the Lean statements are about names and the relation "denote the same set"; the quotient is formed only when the host is assembled. In §5 the Lean development defines the data of all stages first, by Separation, and then proves the properties by induction; the text presents them together. In Appendix A the Lean proof uses de Bruijn indices.

**What Lean does not check.** That the definitions of NF and NFU + Infinity in `NFTheories.lean` are the intended theories. That is a matter of reading that file; §1.1 states them as they are defined there.

---

## Appendix C. Terminology

Terms of this document, with the terms they replace and the Lean names. "Exposition" is the exposition of 29 October 2026; where Holmes and Wilshaw use the same word it is theirs.

| This document | Exposition, Holmes–Wilshaw, earlier notes | Lean |
|---|---|---|
| label | litter label | `IsLabel`, `label` |
| the atoms incident to a label | litter | `Adj` |
| label object | literal litter | `IsLit` |
| proxy label; free label | label in a fibre; flexible label | |
| original (of a proxy) | parent | the component `ξ` of `label` |
| route | reservoir | the component `r` of `label` |
| proxy family | fibre | |
| direct extension | distinguished extension | |
| proxy extension | alternate extension | `IsAlt` |
| source, source chain | inverse, chain of inverses, depth | `IsInv`, `Retained` |
| candidate; kept | pre-object; retained | `Retained`, `IsObj` |
| template | code; in the Lean files, name | `IsName` |
| description; the object described | descriptor; decoded value | `IsDec` |
| bound; kind; dependencies | coloured; colour; coordinates | `Col` |
| regular level | closed level | `Closed` |
| chain of regular levels | ladder of closed levels | the field `Λ` of `Tower`, `tower_of_ladder` |
| tangled model of height d | tower; flat model | `Tower`, `FlatM` |
| level sequence | placement | `Plc` |
| strongly cantorian number | calm number | `InS` |
| extendable state; greedy state | good state; correct state | `Good`, `Correct` |
| Add(k, S) | T1 | `T1` |

Unchanged: atom, path, token, tuple, pattern, support, host, ladder and rung (§3), stage, hull, cut.

---

## References

- Th. Hailperin, A set of axioms for logic, *Journal of Symbolic Logic* 9 (1944), 1–19.
- F. Hartogs, Über das Problem der Wohlordnung, *Mathematische Annalen* 76 (1915), 438–443.
- M. R. Holmes, The equivalence of NF-style set theories with "tangled" type theories; the construction of ω-models of predicative NF (and more), *Journal of Symbolic Logic* 60 (1995), 178–190.
- M. R. Holmes and S. Wilshaw, New Foundations is consistent, arXiv:1503.01406.
- R. B. Jensen, On the consistency of a slight (?) modification of Quine's New Foundations, *Synthese* 19 (1968/69), 250–263.
- W. V. Quine, New foundations for mathematical logic, *American Mathematical Monthly* 44 (1937), 70–80.
- F. P. Ramsey, On a problem of formal logic, *Proceedings of the London Mathematical Society* 30 (1930), 264–286.
- E. Specker, The axiom of choice in Quine's New Foundations for mathematical logic, *Proceedings of the National Academy of Sciences of the USA* 39 (1953), 972–975.
- *A model of tangled type theory from overlapping generic litters: an expository proof of the consistency of New Foundations*, 29 October 2026 (`nf_consistency_exposition.tex`).
- For the constructible hierarchy and condensation: K. J. Devlin, *Constructibility*, Springer, 1984. For cuts and their shortening: P. Hájek and P. Pudlák, *Metamathematics of First-Order Arithmetic*, Springer, 1993.
