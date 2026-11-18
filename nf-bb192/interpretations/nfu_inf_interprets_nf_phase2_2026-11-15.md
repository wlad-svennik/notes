# NFU + Infinity interprets NF: the term model on a cut (Phase 2)

15 November 2026. This is a paper proof. Nothing in it is machine-checked. It replaces §5, §6 and §7 of `nfu_inf_interprets_nf_proof_2026-11-13.md` ("the main document"): the syntactic conversion, the Main Lemma inside U, cut elimination with bounds and the interpretation existence lemma are no longer used. Section numbers "§n" refer to the main document; sections of this note are T0–T9.

Tags: **[proved]** full proof here; **[textbook]** standard, with the adaptation explained; **[Lean]** compiled and kernel-checked; **[open]** not yet proved anywhere.

---

## T0. What is proved, and from what

U is NFU + Infinity. The argument takes place inside U and uses three things.

**(A) Arithmetic of U.** ℕ is a set; +, ×, 2ˣ are set functions; induction and the least number principle hold for every condition given by a stratified formula with parameters (Lemma 2.0, Theorem 2.1; **[Lean]**). The calm numbers 𝖲 form a definable cut closed under +, × and 2ˣ (Lemma 2.2; **[Lean]**). 𝖲 is not known to be a set. From the first sentence, Peano arithmetic holds in ℕ, so finite sequences of numbers and finite syntactic objects are coded by numbers in the usual way, and every set function from an initial segment {0,…,n−1} into ℕ has a code (induction on n). This coding is **[textbook]**; it is not in the Lean files, where sequences are set functions. T9 says where codes can be avoided.

**(B) Set structures.** Sets C, E, … of U with first-order conditions on them. Any condition on numbers and elements of C that is first-order in given sets is stratified once numbers and elements of C are given the same type, so it defines a set and can be used in induction.

**(F) Flat models at calm heights. [Lean except for the reading-off step; see T9]** For every calm h ≥ 1 there is a flat model of height h in the sense of T2.

**Theorem.** From (A), (B), (F): there are formulas δ(x), ε(x, y), η(x, y) of the language of NFU, without parameters, such that U proves the relativisation to δ of every sentence of NF₀, with ∈ read as ε and = read as η. Hence U interprets NF₀, and NF (Hailperin's theorem, **[Lean]** `NFModel.comprehension`).

The proof is a Henkin construction in which a consistency property replaces a proof calculus. The elements of the interpretation are closed terms in a finite signature. An atomic sentence between closed terms has a truth value in a flat model once the terms are placed on levels. A finite assignment of truth values to atoms is *good* if, for every calm q, some flat model has q levels on which every assigned atom has its assigned value at every placement. Ramsey's theorem shows that a good assignment can be extended to one more atom. The lengths for which the leftmost good assignment exists form a cut, and the term model lives on a sub-cut.

---

## T1. The signature

Eighteen function symbols. The first twelve are the operations of the Lean structure `NFModel` and one witness for each of its existence axioms. The last six are Skolem functions for the remaining quantifiers.

| | symbol | arity | reads |
|---|---|---|---|
| 1 | sing | 1 | {x} |
| 2 | up | 2 | {x, y} |
| 3 | IN | 2 | x ∩ y |
| 4 | CO | 1 | complement of x |
| 5 | SI | 1 | singleton image of x |
| 6 | I2 | 1 | insertion two |
| 7 | I3 | 1 | insertion three |
| 8 | VC | 1 | V × x |
| 9 | TL | 1 | type lowering |
| 10 | CV | 1 | converse of x |
| 11 | C1 | 0 | the set of all singletons |
| 12 | SB | 0 | the inclusion relation |
| 13 | D | 2 | a point where x and y differ |
| 14 | P1 | 1 | first component of p |
| 15 | P2 | 1 | second component of p |
| 16 | EL | 1 | the element of the singleton p |
| 17 | WT | 2 | a counterexample for p ∈ TL(x) |
| 18 | WS | 2 | a counterexample for p ⊆ q |

op(x, y) abbreviates up(sing(x), up(x, y)).

**Closed terms** are coded by numbers, with code(f(t₁,…,tₙ)) = ⟨f, ⟨t₁, …⟩⟩ + 1 for the pairing ⟨x, y⟩ = (x + y)² + x of §3.1. So the code is a polynomial in the codes of the arguments, every proper subterm has a smaller code, and the depth of a term is at most its code. "t is a closed term" is an arithmetical condition. From now on a term is its code.

**Atoms** are the expressions t ∈ t′ and t = t′ for closed terms t, t′, with codes 2⟨t, t′⟩ and 2⟨t, t′⟩ + 1. For a number i let αᵢ be the atom with code i, and let αᵢ be C1 = C1 if i is not the code of an atom.

**The axioms N.** These are the following conditions on a structure for the signature with ∈ and =, for all values of the variables. They are the axioms of `NFModel` with the inner quantifiers replaced by the Skolem functions.

- (E1) x = x. (E2) x = y ∧ x = z → y = z. (E3) x = x′ ∧ y = y′ ∧ x ∈ y → x′ ∈ y′. (E4) x = x′ → sing(x) = sing(x′), and x = x′ ∧ y = y′ → up(x, y) = up(x′, y′).
- (M1) (D(x,y) ∈ x ↔ D(x,y) ∈ y) → x = y.
- (M2) y ∈ sing(x) ↔ y = x. (M3) z ∈ up(x,y) ↔ z = x ∨ z = y.
- (M4) z ∈ IN(x,y) ↔ z ∈ x ∧ z ∈ y. (M5) z ∈ CO(x) ↔ ¬ z ∈ x.
- (M6) op(sing z, sing w) ∈ SI(x) ↔ op(z, w) ∈ x.
- (M7) op(sing sing p, op(q, r)) ∈ I2(x) ↔ op(p, r) ∈ x. (M8) the same with I3 and op(p, q).
- (M9) p ∈ VC(x) → p = op(P1 p, P2 p) ∧ P2 p ∈ x; and p = op(q, r) ∧ r ∈ x → p ∈ VC(x).
- (M10) p ∈ TL(x) → op(q, sing p) ∈ x; and op(WT(p,x), sing p) ∈ x → p ∈ TL(x).
- (M11) op(p, q) ∈ CV(x) ↔ op(q, p) ∈ x.
- (M12) p ∈ C1 → p = sing(EL p); and p = sing q → p ∈ C1.
- (M13) op(p, q) ∈ SB ∧ r ∈ p → r ∈ q; and (WS(p,q) ∈ p → WS(p,q) ∈ q) → op(p, q) ∈ SB.

**Lemma T1.1. [proved]** Let 𝔐 be a structure for the signature in which = is interpreted by a relation ≈ and N holds. Then ≈ is an equivalence relation, and the quotient of 𝔐 by ≈ with ∈, sing, up is an `NFModel`. So every sentence of NF₀ holds in 𝔐 with = read as ≈.

*Proof.* (E1)–(E4) make ≈ a congruence for ∈, sing and up. Each field of `NFModel` follows from the axiom of the same number, with the witness given by the corresponding term: for `ext` use (M1) at z = D(x, y); for `vCross` the two halves of (M9); for `typeLower`, `cardinalOne`, `subset` likewise. An `NFModel` satisfies extensionality and every instance of stratified comprehension (`NFModel.isNF`, **[Lean]**), in particular every sentence of NF₀. ∎

The proof of Lemma T1.1 is a fixed finite piece of first-order reasoning. It therefore applies to a structure given by formulas δ, ε, η and the term constructors inside U.

---

## T2. Flat models

A **flat model of height h** is a set structure 𝔗 = (C, λ, E, ≺), where h ≥ 1 is a number, λ is a function from C onto a subset of {1,…,h}, E ⊆ C × C, and ≺ ⊆ C × C, with the properties (F0)–(F12) below. Write C_a = {x : λ(x) = a} (level a), and for x ∈ C_a and b < a write x↓b = {z ∈ C_b : z E x}. Numbers and elements of C have the same type; nothing else about the elements of C is used.

- (F0) ≺ is a strict linear order of C, and every C_a has a ≺-least element.
- (F1) If b < a, x, y ∈ C_a and x↓b = y↓b, then x = y.
- (F2) If b < a and x, y ∈ C_b, some p ∈ C_a has p↓b = {x, y}.

By (F1) the p of (F2) is unique. Write {x, y}_a for it, {x}_a for {x, x}_a, and for c < b < a and x, y ∈ C_c write ⟨x, y⟩_{a,b} = {{x}_b, {x, y}_b}_a.

**Lemma T2.1. [proved]** {x}_a = {x′}_a implies x = x′, and ⟨x, y⟩_{a,b} = ⟨x′, y′⟩_{a,b} implies x = x′ and y = y′. (The usual argument for Kuratowski pairs, from (F1) and (F2). In the abstract setting this is `sing_inj`, `op_inj'` of `Host.lean`.) ∎

A **placement** is a strictly increasing function v from an interval [A, B] of integers into {1,…,h}, coded by a number. For each symbol f of arity n the table gives integers s₁,…,sₙ (**offsets**), an interval [−ℓ, u] (**reach**), and a **selection condition** θ_f(y; y₁,…,yₙ; k, v) on y ∈ C_{v(k)}, where yᵢ ∈ C_{v(k+sᵢ)} and [k−ℓ, k+u] ⊆ dom v. In the table a = v(k), and v(k−1), v(k−2), … are written a′, a″, …; v(k+1), v(k+2), … are written a⁺, a⁺⁺, ….

| f | offsets | reach | θ_f(y; y₁, y₂; k, v) |
|---|---|---|---|
| sing | −1 | [−1, 0] | y↓a′ = {y₁} |
| up | −1, −1 | [−1, 0] | y↓a′ = {y₁, y₂} |
| IN | 0, 0 | [−1, 0] | y↓a′ = y₁↓a′ ∩ y₂↓a′ |
| CO | 0 | [−1, 0] | y↓a′ = C_{a′} ∖ y₁↓a′ |
| SI | −1 | [−4, 0] | for all z, w ∈ C_{v(k−4)}: ⟨{z}_{v(k−3)}, {w}_{v(k−3)}⟩_{a′,a″} E y ⇔ ⟨z, w⟩_{a″,v(k−3)} E y₁ |
| I2 | −2 | [−5, 0] | for all p, q, r ∈ C_{v(k−5)}: ⟨{{p}_{v(k−4)}}_{v(k−3)}, ⟨q, r⟩_{v(k−3),v(k−4)}⟩_{a′,a″} E y ⇔ ⟨p, r⟩_{v(k−3),v(k−4)} E y₁ |
| I3 | −2 | [−5, 0] | the same with ⟨p, q⟩_{v(k−3),v(k−4)} on the right |
| VC | −2 | [−3, 0] | for all p ∈ C_{a′}: p E y ⇔ there are q, r ∈ C_{v(k−3)} with p = ⟨q, r⟩_{a′,a″} and r E y₁ |
| TL | +3 | [−1, 3] | for all p ∈ C_{a′}: p E y ⇔ for all q ∈ C_a: ⟨q, {p}_a⟩_{a⁺⁺,a⁺} E y₁ |
| CV | 0 | [−3, 0] | for all p, q ∈ C_{v(k−3)}: ⟨p, q⟩_{a′,a″} E y ⇔ ⟨q, p⟩_{a′,a″} E y₁ |
| C1 | | [−2, 0] | for all p ∈ C_{a′}: p E y ⇔ p = {q}_{a′} for some q ∈ C_{a″} |
| SB | | [−4, 0] | for all p, q ∈ C_{v(k−3)}: ⟨p, q⟩_{a′,a″} E y ⇔ p↓v(k−4) ⊆ q↓v(k−4) |
| D | +1, +1 | [0, 1] | y E y₁ ⇎ y E y₂ |
| P1 | +2 | [0, 2] | y₁ = ⟨y, r⟩_{a⁺⁺,a⁺} for some r ∈ C_a |
| P2 | +2 | [0, 2] | y₁ = ⟨q, y⟩_{a⁺⁺,a⁺} for some q ∈ C_a |
| EL | +1 | [0, 1] | y₁ = {y}_{a⁺} |
| WT | −1, +3 | [−1, 3] | not ⟨y, {y₁}_a⟩_{a⁺⁺,a⁺} E y₂ |
| WS | +1, +1 | [0, 1] | y E y₁ and not y E y₂ |

Each θ_f is first-order in (C, λ, E) with the yᵢ and finitely many levels as parameters. The remaining properties of a flat model are:

- (F3)–(F12) For each of the ten symbols IN, …, SB, for every placement and all arguments in the indicated levels, some y ∈ C_{v(k)} satisfies θ_f.
- (F0, continued) For each of the eighteen symbols, every placement and all arguments: if some y ∈ C_{v(k)} satisfies θ_f, there is a ≺-least such y.

(F1)–(F12) are the typed forms, for every descending chain of levels, of extensionality and the existence axioms; the positions of the variables in the chains are those of `FlatTTT` in `Flat.lean`. (F0) holds in particular when ≺ is a well-ordering of C. It is stated in this weaker form because that is what T9 can deliver.

---

## T3. Evaluation of terms

Fix a flat model 𝔗. For a closed term define integers lo(t) ≤ 0 ≤ hi(t) by recursion: for t = f(t₁,…,tₙ) with offsets sᵢ and reach [−ℓ, u],

lo(t) = min(−ℓ, minᵢ (sᵢ + lo(tᵢ))),  hi(t) = max(u, maxᵢ (sᵢ + hi(tᵢ))).

Since ℓ ≤ 5, u ≤ 3 and −2 ≤ sᵢ ≤ 3, induction gives −5·depth(t) ≤ lo(t) and hi(t) ≤ 3·depth(t).

**Lemma T3.1 (evaluation). [proved]** There is a unique set Val of quadruples (t, k, v, c), with t a closed term, k an integer, v a placement with [k + lo(t), k + hi(t)] ⊆ dom v, and c ∈ C, such that:

1. for all such t, k, v there is exactly one c with (t, k, v, c) ∈ Val; write c = val(t, k, v); it lies in C_{v(k)};
2. for t = f(t₁,…,tₙ): val(t, k, v) is the ≺-least y ∈ C_{v(k)} satisfying θ_f(y; val(t₁, k+s₁, v), …; k, v) if there is one, and the ≺-least element of C_{v(k)} otherwise;
3. (locality) val(t, k, v) depends only on the restriction of v to [k + lo(t), k + hi(t)];
4. (shift) val(t, k + j, v⁺ʲ) = val(t, k, v), where v⁺ʲ(i) = v(i − j).

For the symbols sing, …, SB the first case of clause 2 always applies.

*Proof.* Clause 2 is a closure condition on a set of quadruples. It is first-order in C, λ, E, ≺ and arithmetic, hence stratified, so the intersection of all sets closed under it exists. Call it Val. That for given t, k, v there is at least one c is proved by induction on the code t for all k, v at once, using (F0); that there is at most one is the same induction applied to the set obtained from Val by removing a second value. The arguments have the right levels because val(tᵢ, k+sᵢ, v) ∈ C_{v(k+sᵢ)}, and the domain condition for tᵢ follows from the one for t by the definition of lo and hi. The last sentence is (F2)–(F12). Clauses 3 and 4 are inductions on t: θ_f mentions v only at k−ℓ,…,k+u, and the whole of clause 2 is invariant under translating k and v together. ∎

For an atom α = (t ∈ t′) put lo(α) = min(lo(t), 1 + lo(t′)) and hi(α) = max(hi(t), 1 + hi(t′)); for α = (t = t′) put lo(α) = min(lo(t), lo(t′)), hi(α) = max(hi(t), hi(t′)). The **span** of α is [lo(α), hi(α)] and its **width** is w(α) = hi(α) − lo(α) + 1. By the bounds above and depth ≤ code,

w(αᵢ) ≤ 8i + 8 for every i.  (1)

For an integer j and a placement v whose domain includes j + span(α), define the truth value of α **at shift j**:

𝔗 ⊨ᵛⱼ (t ∈ t′) ⇔ val(t, j, v) E val(t′, j+1, v);  𝔗 ⊨ᵛⱼ (t = t′) ⇔ val(t, j, v) = val(t′, j, v).

Write 𝔗 ⊨ᵛ α for shift 0. By clauses 3 and 4:

𝔗 ⊨ᵛⱼ α ⇔ 𝔗 ⊨ʷ α, where w(i) = v(i + j) for i ∈ span(α).  (2)

The relation "𝔗 ⊨ᵛⱼ α" is a set of triples (α, j, v), because Val is a set.

---

## T4. The axioms N at shifted placements

**Lemma T4.1. [proved]** Let 𝔗 be a flat model, let x, y, z, w, p, q, r, x′, y′ be closed terms, and let v be a placement whose domain includes every shifted span that occurs below. Then each axiom of N holds when its atoms are read at the following shifts.

| axiom | shifts |
|---|---|
| (E1), (E2) | all atoms at 0 |
| (E3) | (x = x′)₀, (y = y′)₁, (x ∈ y)₀, (x′ ∈ y′)₀ |
| (E4) | (x = x′)₋₁, (y = y′)₋₁; conclusions at 0 |
| (M1) | (D ∈ x)₀, (D ∈ y)₀, (x = y)₁ |
| (M2)–(M5), (M11), (M12) | all atoms at 0 |
| (M6) | (op(sing z, sing w) ∈ SI(x))₀, (op(z, w) ∈ x)₋₁ |
| (M7), (M8) | (… ∈ I2(x))₀, (op(p, r) ∈ x)₋₂; likewise I3 |
| (M9) | (p ∈ VC(x))₀, (p = op(…))₀, (P2 p ∈ x)₋₂, (r ∈ x)₋₂ |
| (M10) | (p ∈ TL(x))₀, (op(q, sing p) ∈ x)₃, (op(WT(p,x), sing p) ∈ x)₃ |
| (M13) | (op(p, q) ∈ SB)₀, (r ∈ p)₋₃, (r ∈ q)₋₃, (WS ∈ p)₋₃, (WS ∈ q)₋₃ |

*Proof.* Each line is a reading of clause 2 of Lemma T3.1. The shifts are chosen so that every term is evaluated at one index throughout the axiom. Four cases show the pattern.

(M1). Let X = val(x, 1, v) and Y = val(y, 1, v), both in C_{v(1)}. The term D(x, y) at index 0 has its arguments at index 1, so val(D(x,y), 0, v) is the least element of C_{v(0)} that is E-related to exactly one of X, Y, if there is one. If X ≠ Y there is one, by (F1), and the premise of (M1) fails. If X = Y the conclusion holds at shift 1.

(M6). At shift 0 the term SI(x) is at index 1, so x is at index 0, and Y = val(SI(x), 1, v) satisfies θ_SI with y₁ = val(x, 0, v) and the levels v(1) > v(0) > v(−1) > v(−2) > v(−3). The term op(sing z, sing w) at index 0 has sing z, sing w at index −2 and z, w at index −3; its value is ⟨{Z}_{v(−2)}, {W}_{v(−2)}⟩_{v(0),v(−1)} with Z = val(z, −3, v), W = val(w, −3, v). The term op(z, w) at index −1 has z, w at index −3 and value ⟨Z, W⟩_{v(−1),v(−2)}. So θ_SI at these Z, W is the equivalence (M6), with the second atom at shift −1.

(M9). Let P = val(p, 0, v), X = val(x, −1, v), and Y = val(VC(x), 1, v), which satisfies θ_VC with the levels v(1) > v(0) > v(−1) > v(−2). If P E Y then P = ⟨Q, R⟩_{v(0),v(−1)} with Q, R ∈ C_{v(−2)} and R E X, and Q, R are unique by Lemma T2.1. The terms P1 p, P2 p at index −2 have p at index 0, so their values are Q and R. Hence val(op(P1 p, P2 p), 0, v) = P, and (P2 p ∈ x) holds at shift −2. The second half is θ_VC read from right to left.

(M10). Let P = val(p, 0, v), X = val(x, 4, v), and Y = val(TL(x), 1, v), which satisfies θ_TL with the levels v(4) > v(3) > v(2) > v(1) > v(0). The term op(q, sing p) at index 3 has q and sing p at index 1 and p at index 0, so its value is ⟨Q, {P}_{v(1)}⟩_{v(3),v(2)} with Q = val(q, 1, v). This gives the first half. The term WT(p, x) at index 1 has p at index 0 and x at index 4; its value is the least Q ∈ C_{v(1)} with ⟨Q, {P}_{v(1)}⟩ not E-related to X, if there is one. If ⟨val(WT(p,x), 1, v), {P}⟩ E X, there is none, so P E Y.

The other cases are the same computation with the offsets of the table in T2: (E3) and (E4) because equal values give equal selection sets; (M2)–(M5) and (M11) directly; (M7), (M8) like (M6); (M12) like (M9) with Lemma T2.1 for singletons; (M13) like (M10). ∎

---

## T5. Ramsey's theorem and the calm exponents

For numbers r ≥ 1, q, Q let Ram(r, q, Q) be the statement: for every set c of strictly increasing sequences of length r with entries in {1,…,Q}, there is a strictly increasing g : {1,…,q} → {1,…,Q} such that either every strictly increasing sequence of length r with entries in the range of g belongs to c, or none does. Sequences are coded by numbers, so Ram is a stratified condition.

Define ρ by recursion: ρ(1, q) = 2q, and ρ(r+1, q) = 2^(ρ(r, q)^(r+1)).

**Lemma T5.1 (Ramsey). [textbook]** For all r ≥ 1 and all q: Ram(r, q, ρ(r, q)).

*Proof.* Induction on r, which is legitimate because the condition is stratified. r = 1 is the pigeonhole principle. For the step let N = ρ(r, q), M = 2^(N^(r+1)), and let c be a set of increasing (r+1)-sequences from {1,…,M}. Choose a₁ < a₂ < … < a_N and sets S₀ ⊇ S₁ ⊇ … with S₀ = {1,…,M}, a_{m+1} = min S_m, and S_{m+1} ⊆ S_m ∖ {a_{m+1}} a largest set on which, for every r-subset B of {a₁,…,a_{m+1}} containing a_{m+1}, membership of B ∪ {x} in c does not depend on x. There are at most N^(r−1) such B, so |S_{m+1}| ≥ (|S_m| − 1)/2^(N^(r−1)) ≥ |S_m|/2^(N^(r−1)+1) as long as |S_m| ≥ 2, and N·(N^(r−1) + 1) ≤ N^(r+1); so the construction runs for N steps. For an r-subset B of {a₁,…,a_N}, membership of B ∪ {a_j} in c is the same for all j above B. Apply Ram(r, q, N) to that colouring of r-subsets. The construction is a recursion on m ≤ N for a set function and the estimates are inductions on m. ∎

**Lemma T5.2 (calm exponents). [proved]** Let 𝖱 be the class of r such that r = 0, or ρ(r, q) is calm for every calm q. Then 𝖱 is a cut and 𝖱 ⊆ 𝖲.

*Proof.* ρ is increasing in r and r ≤ ρ(r, 1), so 𝖱 is closed downwards and 𝖱 ⊆ 𝖲, because 𝖲 is closed downwards. 1 ∈ 𝖱 because 𝖲 is closed under +. If r ∈ 𝖱 and q is calm, then N = ρ(r, q) and r + 1 are calm, so N^(r+1) ≤ 2^(N·(r+1)) and ρ(r+1, q) are calm by Lemma 2.2. ∎

---

## T6. Good states and the dichotomy

A **state** is a finite sequence σ of zeros and ones, coded by a number; lh(σ) is its length. It assigns the value σ(i) to the atom αᵢ for i < lh(σ).

For a number q, a state σ is **q-good** if there are a flat model 𝔗 and a strictly increasing sequence e = (e₁ < … < e_q) of levels of 𝔗 such that for every i < lh(σ) and every placement v from span(αᵢ) into {e₁,…,e_q}:

𝔗 ⊨ᵛ αᵢ ⇔ σ(i) = 1.

A state is **good** if it is q-good for every calm q. "q-good" is a formula of U with σ and q free; it need not be stratified, and no induction is applied to it.

Three remarks. If σ is q-good and q′ ≤ q, then σ is q′-good (restrict e). An initial segment of a q-good state is q-good. And by (2), in a pair (𝔗, e) witnessing q-goodness, 𝔗 ⊨ᵛⱼ αᵢ ⇔ σ(i) = 1 for every shift j and every placement v into {e₁,…,e_q} whose domain includes j + span(αᵢ).

**Lemma T6.1. [proved from (F)]** The empty state is good.

*Proof.* For calm q ≥ 1 take a flat model of height q and e = (1,…,q); for q = 0 take any flat model. ∎

**Lemma T6.2 (dichotomy). [proved]** Let σ be good, k = lh(σ), and suppose w(α_k) ∈ 𝖱. Then σ⌢1 is good or σ⌢0 is good.

*Proof.* Let r = w(α_k). Fix a calm q. Then Q = ρ(r, q) is calm, so σ is Q-good: take 𝔗 and e′ = (e′₁ < … < e′_Q). The placements of span(α_k) into {e′₁,…,e′_Q} correspond to the increasing r-sequences from {1,…,Q}. Let c be the set of those at which α_k is true in 𝔗; it is a set. By Lemma T5.1 there is an increasing g : {1,…,q} → {1,…,Q} on whose range c is constant, with value b ∈ {0, 1}. Put eᵢ = e′_{g(i)}. Every placement into {e₁,…,e_q} is a placement into {e′₁,…,e′_Q}, so (𝔗, e) witnesses that σ⌢b is q-good.

So for every calm q, σ⌢1 is q-good or σ⌢0 is q-good. Let A₁ be the class of calm q for which σ⌢1 is q-good, and A₀ likewise. Both are closed downwards and A₁ ∪ A₀ = 𝖲. If q₁ ∈ 𝖲 ∖ A₁ and q₀ ∈ 𝖲 ∖ A₀, then max(q₀, q₁) is calm and lies in A₁ or A₀, hence q₁ ∈ A₁ or q₀ ∈ A₀. So A₁ = 𝖲 or A₀ = 𝖲. This step uses no induction. ∎

---

## T7. Decision sequences and the cuts

A state σ is **correct** if

- every initial segment of σ, including σ, is good; and
- for every i < lh(σ): σ(i) = 1 if and only if (σ↾i)⌢1 is good.

Let 𝖱′ = {k : 8k + 8 ∈ 𝖱}; it is a cut, because 𝖱 is closed under successor. Let

J = {k ∈ 𝖱′ : there is a correct state of length k}.

**Lemma T7.1. [proved]** (a) If σ, σ′ are correct and lh(σ) ≤ lh(σ′), then σ is an initial segment of σ′. (b) J is a cut.

*Proof.* (a) Initial segments of correct states are correct. If σ is not an initial segment of σ′, let i be the least number with σ(i) ≠ σ′(i); the set of such i is given by a stratified condition. Then σ↾i = σ′↾i, and correctness makes both σ(i) and σ′(i) equal to 1 exactly when (σ↾i)⌢1 is good.

(b) 0 ∈ J by Lemma T6.1. J is closed downwards. Let k ∈ J with correct σ. By (1), w(α_k) ≤ 8k + 8 ∈ 𝖱. Put σ′ = σ⌢1 if σ⌢1 is good and σ′ = σ⌢0 otherwise; in the second case σ⌢0 is good by Lemma T6.2. Then σ′ is correct, and k + 1 ∈ 𝖱′. ∎

Let I be a cut with I ⊆ J that is closed under + and × (Solovay's shortening, **[textbook]**: I₁ = {n : ∀m ∈ J (m + n ∈ J)}, I = {n : ∀m ∈ I₁ (m·n ∈ I₁)}; the same computation is Lean for the cut 𝖢₂ of Lemma 2.3: `K_add`, `K_mul`, `K_down`, `K_sub` in the namespace `Shortening` of `NFUCut.lean`). If t, t′ ∈ I then the codes of t ∈ t′ and t = t′, and the code of f(t₁,…,tₙ) for tᵢ ∈ I, are values of polynomials at numbers in I, so they are in I.

---

## T8. The interpretation

- δ(t): t is a closed term and t ∈ I.
- ε(t, t′): there is a correct state σ of length i + 1 with σ(i) = 1, where i is the code of t ∈ t′.
- η(t, t′): the same with the code of t = t′.

These are formulas of the language of NFU without parameters: "calm", "flat model", Val, "q-good", "correct", 𝖱, J and I are all defined outright. By the last paragraph of T7, δ is closed under the eighteen term constructors. By Lemma T7.1, for t, t′ in δ and any correct σ whose length exceeds the code i of an atom between them, ε or η holds if and only if σ(i) = 1.

**Lemma T8.1 (the decisions satisfy N). [proved]** Let α¹,…,αⁿ be atoms between terms in δ (n standard), let j₁,…,jₙ be standard integers, and let B be a Boolean combination of n propositional variables. Suppose that for every flat model 𝔗 and every placement v whose domain includes all jₘ + span(αᵐ), B holds of the truth values 𝔗 ⊨ᵛ_{jₘ} αᵐ. Then B holds of the truth values that ε and η give to α¹,…,αⁿ.

*Proof.* Let k ∈ J exceed the codes of the αᵐ and let σ be the correct state of length k. The widths w(αᵐ) are at most 8k + 8, hence calm, so there is a calm q such that an interval [A, B′] of q integers includes all jₘ + span(αᵐ). σ is q-good: take 𝔗 and e, and let v(A + n) = e_{n+1}. By the third remark of T6, 𝔗 ⊨ᵛ_{jₘ} αᵐ if and only if σ gives αᵐ the value 1. Apply the hypothesis to 𝔗 and v. ∎

**Theorem. [proved from (A), (B), (F)]** U proves the relativisation to δ of every axiom of N, with ∈ as ε and = as η. Hence U proves the relativisation of every sentence of NF₀, and U interprets NF.

*Proof.* Each instance of an axiom of N at terms in δ is a Boolean combination of at most five atoms between terms in δ, and by Lemma T4.1 it holds in every flat model at every sufficiently long placement when the atoms are read at the listed shifts. Lemma T8.1 gives the instance for ε and η. Lemma T1.1 gives NF₀. ∎

---

## T9. Where (F) comes from, and what has to be formalised

**(F) from the earlier parts.** Let h ≥ 1 be calm. (Status as of 14:46 UTC on 15 November, after Phase 0.)

1. Lemma 3.2 **[Lean]** gives, for suitable calm m, the structure 𝔏 with a definable linear order <* in which every set of 𝔏 with a member has a least member, and whose numbers are isomorphic to ℕ by a set map.
2. **[Lean]** 𝔏 is a host in the sense of `Host.lean` (`NFUCut.Model.host`), and it contains a ladder of closed levels: the levels at the stages ν₁ < … < ν_m of Lemma 3.2, each the least stage that is not small over the one before. Transitivity and closure under subsets come from `next_absorb`; the bounding of functions is a new hull argument (`next_coll_at`: the proof of Collection at a stage, with the formula evaluated at a later stage); the initial segments of <* are covered because <* compares ranks first (`cover_lim`).
3. **[Lean]** In every host with such a ladder there is a tower (`Host.tower_of_ladder`), and for every tower the typed statements hold for all descending chains of levels: `ext_ax`, `sing_ex`, `up_ex`, `inter_ex`, `compl_ex`, `singletonImage_ex`, `insertion2_ex`, `insertion3_ex`, `vCross_ex`, `typeLower_ex`, `converse_ex`, `cardinalOne_ex`, `subset_ex`. Items 1–3 together are the theorem `NFUCut.Model.exists_host_tower`: if 3(d₀ + 3) + 2 is calm, there are a host, a tower in it of height d₀ + 1, and a map `num` from the numbers of U onto the numbers of the host that takes 0 to ∅, i + 1 to the successor, and < to ∈. Its axioms are `propext`, `Classical.choice`, `Quot.sound`.
4. **[open: small]** Reading off. C is the set of pairs (a, x) with 1 ≤ a ≤ h and x an object of level a of the tower; λ(a, x) = a; (b, z) E (a, x) if b < a and z is a member of x at the level b; ≺ orders by level and then by <*. (F1)–(F12) are item 3. (F0) holds because each selection set is first-order definable in 𝔏 with parameters, so it is a set of 𝔏 and has a <*-least member. The empty object is in every level.

**What is left for (F), therefore:** item 4, in whichever form the choice below fixes. If T3 and T4 are carried out inside the host, item 4 is not a separate step: a flat model is a tower, and (F0) is the least-element principle of the host.

**A choice for the formalisation.** T3, T4 and the first paragraph of the proof of Lemma T6.2 are arguments about one flat model. They can be carried out inside the host, where a flat model is a tower, by ordinary Lean reasoning with the definability automation of `Host.lean`, instead of inside U with one explicit formula per induction. "σ is q-good" is then "for some m, 𝔏 satisfies: some tower and some increasing sequence of q of its levels witness σ". What remains at the level of U is T5.2, the second paragraph of T6.2, T7 and T8, which use no induction on unstratified conditions, plus the transfer of σ, q and ρ(r, q) between ℕ and the numbers of 𝔏. I think this is the shorter route, but it is a plan and I have not tested it.

**Codes or set functions.** States, the sequences e and the functions g of Lemma T5.1 can be taken to be set functions on initial segments of ℕ instead of codes; nothing in T5–T8 changes, since the only inductions there are on stratified conditions with these as parameters. Codes are needed only where the object is a component of a member of a set defined by recursion, which is the placement v in Val. If T3 is carried out inside the host, that recursion is an ordinary recursion in 𝔏 and no coding by numbers is needed at all.

**Points I consider delicate.**

- The type assignment in Lemma T3.1. Codes, levels, placements and elements of C must all receive one type. This is why placements and sequences are coded by numbers and why C consists of objects of one sort. It is routine, and §3.3 did the same for term evaluation, but it has to be done.
- Lemma T5.1 with r a variable. It is a theorem of PA, so it holds in ℕ by (A); the Lean arithmetic of U has what the proof uses (recursion for set functions, 2ˣ, induction for stratified conditions), but the lemma itself is not formalised.
- The bound (1). It depends on the coding of terms; with a different coding the constant 8 changes and nothing else does.
- (Resolved.) The bounding of functions by the levels went through as a variant of the existing Collection proof; the fallback R2 of the plan was not needed.

**What is no longer needed.** `Crabbe.lean` and `MainLemma.lean` (the external form of §§5–6), Lemma 6.1 in the form with a fixed exponent, Lemma 7.1 (interpretation existence, cited) and Lemma 7.2 (cut elimination with bounds, cited). They remain correct; they are not on the path to the theorem.
