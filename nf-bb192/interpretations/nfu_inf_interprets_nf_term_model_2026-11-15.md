# NFU + Infinity interprets NF: the term model on a cut

15 November 2026, second version. It replaces `nfu_inf_interprets_nf_phase2_2026-11-15.md`, which described a design that was changed during the formalisation (T6–T8 there are superseded; the changes are listed in T12). Every numbered statement below is a Lean theorem; its name is given in `code`. The prose proofs are summaries of the Lean proofs. "The main document" is `nfu_inf_interprets_nf_proof_2026-11-13.md`; "§n" refers to it.

Files, in order of dependence: `Host.lean` (8,453 lines), `HostTerm.lean` (4,392), `NFUTerm.lean` (3,622), `NFUInterpretsNF.lean` (1,799). They sit on top of `ConNF.NF.NFUConstr` (§§2–3 of the main document) and `ConNF.NF.Hailperin`.

---

## T0. The theorem

**Theorem** (`NFUCut.nfu_inf_interprets_nf`). There are formulas δ, ε, η of the language of NFU (∈, =, "is a set") such that for every model M of NFU + Infinity there are a structure (W, mem) and a map π from {x ∈ M : M ⊨ δ(x)} onto W with

- (W, mem) satisfies extensionality and every instance of stratified comprehension (`ConNF.NF.IsNF`);
- π(x) = π(y) if and only if M ⊨ η(x, y);
- mem(π(x), π(y)) if and only if M ⊨ ε(x, y).

The formulas are `nfDelta`, `nfEps`, `nfEta`. They contain no parameters and do not depend on M. Lean reports the axioms `propext`, `Classical.choice`, `Quot.sound`, and no `sorry`.

So the structure that δ, ε, η define in M, with equality read as η, is isomorphic to a model of NF. Since this holds in every model with the same three formulas, the translation of every axiom of NF under (δ, ε, η) holds in every model of NFU + Infinity.

**How to read the statement.**

1. A model of NFU (`NFUCut.Model`) is a type with relations ∈ and "is a set" such that only sets have members, sets with the same members are equal, and every stratified formula with parameters defines a set. Infinity (`Model.Infinity`) says that the universe belongs to no natural number. This is the setting of §2.4.
2. "M ⊨ δ(x)" is `Sat M.mem M.isSet δ (fun _ => x)`: the formula evaluated with x as the value of every variable. "M ⊨ ε(x, y)" is evaluation with y as the value of the variable 103 and x as the value of every other variable. So the conditions are those defined, without parameters, by the formulas obtained from δ, ε, η by identifying all free variables other than 103. The formulas are built so that δ has only the free variable 100, and ε, η only 100 and 103, but Lean does not state this, and the statement does not need it.
3. Equality of NF is interpreted by η, which is a congruence for ε. The domain consists of natural numbers of M.
4. The theorem is about all models. That U = NFU + Infinity *proves* the translated axioms follows by the completeness theorem. Since the evening of 15 November that step is in Lean too (`SetTheoryU.interpretsNF`; see `nf_syntactic_interpretation_2026-11-15.md`).
5. No model of NFU + Infinity is exhibited in Lean. The theorem does not say that NF is consistent; it says that NF is interpretable in U. (Late on 15 November a model of NFU + Infinity was built in Lean: `JensenNFU.exists_model`, §11 of `nf_syntactic_interpretation_2026-11-15.md`.)

**The proof in one paragraph.** The elements of the interpretation are closed terms in a signature with eighteen function symbols, coded by natural numbers of U. A *truth assignment* is a set of numbers, read as the set of codes of true atomic sentences t ∈ t′ and t = t′. The axioms N are universal axioms in this signature whose models, divided by =, are models of NF (T1). The whole definition of the interpretation is arithmetical: a finite assignment is *good* if for every q in a certain cut it extends to an assignment that satisfies all instances of N with atoms below q; the leftmost good assignments of each length cohere; the terms in a cut I, with the truth values given by these assignments, form the model (T8, T9). The one substantial fact is that for every q in the cut there is an assignment satisfying N below q (T7). It is proved by evaluating terms in a model of tangled type theory of nonstandard height, built inside a structure that satisfies Separation and Collection, and making the truth values of the atoms below q independent of the levels by Ramsey's theorem (T2–T6).

---

## T1. The signature and the axioms N

Eighteen function symbols, with tags 0–17:

| tag | symbol | reads | tag | symbol | reads |
|---|---|---|---|---|---|
| 0 | sing(x) | {x} | 9 | CV(x) | converse |
| 1 | up(x, y) | {x, y} | 10 | C1 | the set of all singletons |
| 2 | IN(x, y) | x ∩ y | 11 | SB | the inclusion relation |
| 3 | CO(x) | complement | 12 | D(x, y) | a point where x and y differ |
| 4 | SI(x) | singleton image | 13 | P1(p) | first component of p |
| 5 | I2(x) | insertion two | 14 | P2(p) | second component of p |
| 6 | I3(x) | insertion three | 15 | EL(p) | the element of the singleton p |
| 7 | VC(x) | V × x | 16 | WT(p, x) | a counterexample for p ∈ TL(x) |
| 8 | TL(x) | type lowering | 17 | WS(p, q) | a counterexample for p ⊆ q |

op(x, y) abbreviates up(sing(x), up(x, y)).

**Codes.** With ⟨x, y⟩ = (x + y)² + x, the term f(x, y) has the code ⟨f, ⟨x, y⟩⟩ + 1 (`tm`). All symbols are treated as binary; a symbol of smaller arity ignores the extra arguments, which are written as 0. Every number is a term: a number that is not of the form ⟨f, ⟨x, y⟩⟩ + 1 with f < 18 is a *null term*. This removes the predicate "is a term" from the construction. The atom t ∈ t′ has the code 2⟨t, t′⟩ (`aIn`) and t = t′ has the code 2⟨t, t′⟩ + 1 (`aEq`). Arguments have smaller codes than the term, and terms have codes at most that of an atom they occur in (`le_npair_left`, `le_aIn_*`, `le_aEq_*`).

**The axioms N.** For all values of the variables:

- (E1) x = x. (E2) x = y ∧ x = z → y = z. (E3) x = x′ ∧ y = y′ ∧ x ∈ y → x′ ∈ y′. (E4) x = x′ → sing(x) = sing(x′); x = x′ ∧ y = y′ → up(x, y) = up(x′, y′).
- (M1) (D(x,y) ∈ x ↔ D(x,y) ∈ y) → x = y.
- (M2) y ∈ sing(x) ↔ y = x. (M3) z ∈ up(x,y) ↔ z = x ∨ z = y. (M4) z ∈ IN(x,y) ↔ z ∈ x ∧ z ∈ y. (M5) z ∈ CO(x) ↔ ¬ z ∈ x.
- (M6) op(sing z, sing w) ∈ SI(x) ↔ op(z, w) ∈ x.
- (M7) op(sing sing p, op(s, r)) ∈ I2(x) ↔ op(p, r) ∈ x. (M8) the same with I3 and op(p, s).
- (M9) p ∈ VC(x) → p = op(P1 p, P2 p) ∧ P2 p ∈ x; and p = op(s, r) ∧ r ∈ x → p ∈ VC(x).
- (M10) p ∈ TL(x) → op(s, sing p) ∈ x; and op(WT(p,x), sing p) ∈ x → p ∈ TL(x).
- (M11) op(p, s) ∈ CV(x) ↔ op(s, p) ∈ x.
- (M12) p ∈ C1 → p = sing(EL p); and p = sing s → p ∈ C1.
- (M13) op(p, s) ∈ SB ∧ r ∈ p → r ∈ s; and (WS(p,s) ∈ p → WS(p,s) ∈ s) → op(p, s) ∈ SB.

These are the axioms of the Lean structure `NFModel` with the inner existential quantifiers replaced by the symbols 12–17. Written as conditions on a truth assignment they are 22 clauses.

**Definition** (`NSat τ q`). τ satisfies N below q: each of the 22 clauses holds for all terms for which every atom of the instance has a code < q, with τ(i) as the truth value of the atom with code i.

`NSat` is monotone in q (`NSat.mono`) and depends only on τ below q (`NSat.congr`).

---

## T2. Flat models inside a host

A **host** (`Host`, in `Host.lean`) is a structure (W, ∈, <*) that satisfies extensionality, pairing, union, infinity, Separation and Collection for every first-order formula, and in which <* is a linear order with x ∈ y → x <* y such that every nonempty definable class has a <*-least element. Its numbers are the members of its ω. Lean predicates on W built from ∈, <*, =, connectives, quantifiers and definable relations are shown to be definable by the tactic `hdef`; after that Separation, Collection, induction and the least-element principle are applied to them directly.

A **flat model** in a host H (`FlatM`) consists of a number d of H and two definable relations: Ob(x, a), "x is an object of level a", and El(z, x, ⟨a, b⟩), "z of level b is a member of x of level a". Levels are the numbers 1, …, d. Its axioms (`FlatM.Ax`): every level has an object; for all levels b < a, objects of level a with the same members of level b are equal; and for every descending chain of levels of the required length, the typed forms of the twelve existence statements of `NFModel` (singleton, pair, intersection, complement, the set of singletons, V × x, converse, inclusion, singleton image, the two insertions, type lowering). Singletons, pairs and Kuratowski pairs across levels are unique and injective (`sg_unique`, `sg_inj`, `op_unique`, `op_inj`).

This is a model of tangled type theory presented with one sort and a level relation. Where flat models come from is T11.

---

## T3. Evaluation of terms

Fix a host H with arithmetic (T7) and a flat model in it. A **placement** is an increasing sequence of levels: a function v of H whose domain is a number L of H, strictly increasing, with levels as values (`Plc`). A term is evaluated at a position k < L; its value is an object of level v(k). The arguments of a symbol are evaluated at positions k + s with the following offsets s, and the selection condition θ_f (`T0`–`T17`, `Th`) mentions levels at positions between k − 5 and k + 3:

| f | offsets of the arguments | f | offsets |
|---|---|---|---|
| sing, up | −1 (, −1) | CV | 0 |
| IN, CO | 0 (, 0) | D, WS | +1, +1 |
| SI | −1 | P1, P2 | +2 |
| I2, I3, VC | −2 | EL | +1 |
| TL | +3 | WT | −1, +3 |

The conditions θ_f(y; c₁, c₂), for an object y of level a = v(k) and the values c₁, c₂ of the arguments, are as follows. Write aⱼ = v(k − j) and uⱼ = v(k + j). For objects of lower levels, {x}_b and {x, y}_b are the singleton and the pair at level b, and ⟨x, y⟩_{b,c} = {{x}_c, {x, y}_c}_b. Membership is always between the levels of the two objects.

| f | θ_f(y; c₁, c₂) |
|---|---|
| sing | y = {c₁}_a |
| up | y = {c₁, c₂}_a |
| IN | for all z of level a₁: z ∈ y ⇔ z ∈ c₁ ∧ z ∈ c₂ |
| CO | for all z of level a₁: z ∈ y ⇔ ¬ z ∈ c₁ |
| SI | for all z, w of level a₄: ⟨{z}_{a₃}, {w}_{a₃}⟩_{a₁,a₂} ∈ y ⇔ ⟨z, w⟩_{a₂,a₃} ∈ c₁ |
| I2 | for all p, q, r of level a₅: ⟨{{p}_{a₄}}_{a₃}, ⟨q, r⟩_{a₃,a₄}⟩_{a₁,a₂} ∈ y ⇔ ⟨p, r⟩_{a₃,a₄} ∈ c₁ |
| I3 | the same with ⟨p, q⟩_{a₃,a₄} on the right |
| VC | for all p of level a₁: p ∈ y ⇔ p = ⟨q, r⟩_{a₁,a₂} for some q, r of level a₃ with r ∈ c₁ |
| TL | for all p of level a₁: p ∈ y ⇔ for all q of level a: ⟨q, {p}_a⟩_{u₂,u₁} ∈ c₁ |
| CV | for all p, q of level a₃: ⟨p, q⟩_{a₁,a₂} ∈ y ⇔ ⟨q, p⟩_{a₁,a₂} ∈ c₁ |
| C1 | for all p of level a₁: p ∈ y ⇔ p = {q}_{a₁} for some q of level a₂ |
| SB | for all p, q of level a₃: ⟨p, q⟩_{a₁,a₂} ∈ y ⇔ every r of level a₄ in p is in q |
| D | ¬ (y ∈ c₁ ⇔ y ∈ c₂) |
| P1 | c₁ = ⟨y, r⟩_{u₂,u₁} for some r of level a |
| P2 | c₁ = ⟨q, y⟩_{u₂,u₁} for some q of level a |
| EL | c₁ = {y}_{u₁} |
| WT | ¬ ⟨y, {c₁}_a⟩_{u₂,u₁} ∈ c₂ |
| WS | y ∈ c₁ ∧ ¬ y ∈ c₂ |

For the symbols 0–11 this is the matrix of the corresponding axiom of a flat model, so some y satisfies it.

**Definition** (`Val`). The value of the term n at the position k of v is the <*-least object y of level v(k) with θ_f(y; values of the arguments), if n = f(n₁, n₂), the argument positions are positions of v, and there is such a y; otherwise it is the <*-least object of level v(k). Formally Val(n, k, v, c) says that (n, k, c) belongs to some set D of H all of whose members satisfy this clause relative to D (`SelfSup`). So Val is definable in H, and no recursion theorem is needed.

**Lemma T3.1** (`val_tot`, `val_fun`, `val_ob`, `val0_spec`–`val17_spec`). For a placement v, every number n and every position k of v, there is exactly one c with Val(n, k, v, c); it is an object of level v(k); and if the reach of the symbol fits into v, it satisfies the clause above. For the symbols 0–11 the first case of the clause applies (`vs0`–`vs11`).

*Proof.* Induction on n in H, for all k at once: the arguments have smaller codes. Existence joins certificates for the arguments; uniqueness compares two certificates. ∎

The value as a function is `vl`. An atom is evaluated at a position (`Tin`, `Teq`; in relational form `TinR`, `TeqR`, `Tr`): t ∈ t′ is true at k if vl(t, k, v) is a member of vl(t′, k + 1, v) between the levels v(k + 1) and v(k); t = t′ is true at k if vl(t, k, v) = vl(t′, k, v).

---

## T4. The axioms N at shifted positions

**Lemma T4.1** (`n_e1`, `n_e2`, `n_e3`, `n_e4a`, `n_e4b`, `n_m1`, …, `n_m13b`). In a flat model, for every placement v long enough around the positions used, each clause of N holds when its atoms are evaluated at the following positions relative to a base position:

| axiom | positions |
|---|---|
| (E1), (E2), (M2)–(M5), (M11), (M12) | all atoms at 0 |
| (E3) | x = x′ at 0, y = y′ at 1, the membership atoms at 0 |
| (E4) | premises at −1, conclusion at 0 |
| (M1) | D ∈ x and D ∈ y at 0, x = y at 1 |
| (M6) | … ∈ SI(x) at 0, op(z, w) ∈ x at −1 |
| (M7), (M8) | … ∈ I2(x) at 0, op(p, r) ∈ x at −2 |
| (M9) | p ∈ VC(x) and p = op(…) at 0, P2 p ∈ x and r ∈ x at −2 |
| (M10) | p ∈ TL(x) at 0, the other atoms at +3 |
| (M13) | op(p, s) ∈ SB at 0, the other atoms at −3 |

*Proof.* The positions are chosen so that each term is evaluated at one position throughout the clause. Each clause is then the specification of Lemma T3.1 for the symbol concerned, with the injectivity of singletons and pairs. For (M1): if the values X, Y of x, y at position 1 differ, extensionality gives an object of the level below in exactly one of them, so the value of D(x, y) is such an object and the premise fails. For the second halves of (M10), (M13): if the selected "counterexample" is not one, there is none. ∎

---

## T5. Locality

**Lemma T5.1** (`loc`, `tr_loc`). Let v, w be placements such that v(m + j) = w(j) for all j < W. If t is the code of a term and 5t + 5 ≤ j, j + 5t + 5 < W, then the value of t at the position m + j of v equals its value at the position j of w. If i is the code of an atom and 5i + 6 ≤ j, j + 5i + 6 < W, then the atom is true at m + j in v if and only if it is true at j in w.

*Proof.* Induction on the code in H, through a general statement for two placements related by a correspondence of positions that respects successors, predecessors and levels (`Bis`, `loc_step`, `pick_congr`). One symbol reaches at most 5 positions, and the arguments have smaller codes. ∎

So the truth value of the atom i at a position depends only on the 2(5i + 6) + 1 levels around it. The radius is uniform in the code; the spans lo(t), hi(t) of the first version are not used.

---

## T6. Ramsey's theorem inside the host

Let Card(B, r) say that B is the set of values of an increasing sequence of length r. For numbers r, q, Q of H, **Ram(r, q, Q)** (`Ram`): for every set c and every increasing sequence F of length Q there is an increasing sequence g of length q, a subsequence of F, such that all sets B of values of g with Card(B, r) agree about membership in c.

A host **has arithmetic** (`Host.Arith`) relative to an ordered semiring N with a function E, when a map num from N onto the numbers of H takes 0 to ∅, successor to successor and < to ∈, and the graphs of num(a), num(b) ↦ num(a + b), num(a·b) and num(a) ↦ num(E a) are definable in H. In the application N is the set of natural numbers of U and E is 2ˣ.

Let **rstep(x) = 2·E(E(x + 1)·(x + 1))** (`rstep`).

**Lemma T6.1** (`ram_zero`, `ram_step`). Ram(0, q, q). If Ram(r, q, Q₀) and rstep(Q₀) ≤ l, then Ram(r + 1, q, l).

*Proof.* The step is the usual one: from a sequence of length l extract a sequence of length Q₀ + 1 that is pre-homogeneous, meaning that membership of B ∪ {x} in c does not depend on x above B (`exists_prehom`, from `refine_lemma` and `halve`); then apply Ram(r, q, Q₀) to the induced colouring of r-sets. ∎

For an increasing sequence e, a number i and a radius R, let **AllT(e, i, R)** say: the atom i is true at the position p of w, for every increasing subsequence w of e, of any length L, and every p with R ≤ p and p + R < L. **AllF** is the same with "false".

**Lemma T6.2** (`decide_atom`). If 5i + 6 ≤ R, e′ is increasing of length Q, and Ram(2R + 1, q, Q) holds, then e′ has an increasing subsequence e of length q with AllT(e, i, R) or AllF(e, i, R).

*Proof.* Colour a set B of 2R + 1 values of e′ by the truth value of the atom i at the middle position R of the increasing enumeration of B. Take g homogeneous. For a subsequence w of g and a position p as above, the window of w around p is such a set B, and by Lemma T5.1 the truth value at p in w is the colour of B. ∎

---

## T7. Existence of truth assignments

**Lemma T7.1** (`nsat_of_dec`). Let e be an increasing sequence of levels of a flat model, of length l ≥ 2R + 6, such that every i < q has AllT(e, i, R) or AllF(e, i, R). Then τ(i) :⇔ AllT(e, i, R) satisfies N below q.

*Proof.* Evaluate an instance at the placement e with base positions between R and R + 5. For each atom i of the instance, the truth value at its position is τ(i), because the position is at distance at least R from both ends. Lemma T4.1 gives the clause. ∎

**Lemma T7.2** (`Host.sound_core`). Let H have arithmetic, with a flat model of height num(D), and let Tw be a function on N with rstep(Tw n) ≤ Tw(n + 1), such that induction over N holds for definable relations of H along Tw (the hypothesis G of the Lean statement). If 5q + 6 ≤ R, 2R + 6 ≤ Tw(m) and Tw(m + (2R + 1)·q) ≤ D, there is an increasing sequence e of levels of length Tw(m) such that i ↦ AllT(e, i, R) satisfies N below q.

*Proof.* By induction on j, Ram(j, Tw(a), Tw(a + j)) for all a (Lemma T6.1). By induction on k ≤ q: every increasing sequence of levels of length Tw(m + (2R + 1)·k) has a subsequence of length Tw(m) on which every atom below k is decided at radius R. The step applies Lemma T6.2 to the atom k with Ram(2R + 1, Tw(m + (2R + 1)·k), Tw(m + (2R + 1)·(k + 1))); decided atoms stay decided on subsequences (`AllT.sub`). Start from the sequence of all levels and finish with Lemma T7.1. ∎

**The side of U.** Let tw(0) = 0, tw(b + 1) = rstep(tw(b)), a set function on the numbers of U (`tw`, by the recursion theorem `exists_prec`). Let 𝖲 be the calm numbers (Lemma 2.2), and

𝖪ₜ = the cut obtained from {n : tw(n) ∈ 𝖲} by shortening twice (`InKt`): K₁ = {n : ∀m (tw(m) ∈ 𝖲 → tw(m + n) ∈ 𝖲)}, 𝖪ₜ = {n : ∀m ∈ K₁, m·n ∈ K₁}.

𝖪ₜ is closed downwards and under + and ×, contains every standard number, and tw(n) is calm for n ∈ 𝖪ₜ (`kt_down`, `kt_add`, `kt_mul`, `kt_cast`, `kt_tw`; the shortening lemmas are those of Lemma 2.3).

**Theorem T7.3 (soundness)** (`Model.sound`). For every q ∈ 𝖪ₜ there is a set τ of numbers of U that satisfies N below q.

*Proof.* Put R = 5q + 6, m = 2R + 6, n₀ = m + (2R + 1)·q. Then n₀ ∈ 𝖪ₜ, so d₀ = tw(n₀) is calm, and so is 3(d₀ + 3) + 2. By T11 there are a host H with arithmetic and a flat model in it of height d₀ + 1. Lemma T7.2 applies with Tw = tw and D = d₀ + 1; its induction hypothesis G is Lemma T7.4 below. The set {i < q : AllT(e, num i, num R)} is a set of H by Separation, and the set of numbers of U that num maps into a given set of H is a set of U (`isPred_mem`). ∎

**Lemma T7.4 (mixed induction)** (`mixed_ind`). Let H be the host of T11, Q a definable relation of H and g a set function on the numbers of U. If Q(num 0, num g(0)) and Q(num b, num g(b)) → Q(num(b + 1), num g(b + 1)) for all b, then Q(num b, num g(b)) for all b.

*Proof.* For each k the graph of g up to k, transported by num, is a set of H (`exists_inner_graph`; T11, item 1). With it as a parameter the statement for b ≤ k is a definable property of num(b), and induction in H applies. No new instance of comprehension in U is used. ∎

The same lemma gives the arithmetic of the host: +, × and 2ˣ are defined in H by recursion, and they agree with those of U through num (`rec_transfer`, `add_transfer`, `mul_transfer`, `exp_transfer`, `arith`).

---

## T8. Good states and the cut of the terms

From here on everything is arithmetic of U with sets of numbers as parameters. A **state** is a number k with a set S of numbers; only the members of S below k matter. Agree(k, S, S′) means that S and S′ have the same members below k.

**Definitions** (`Sat1`, `Good`, `T1`, `Correct`, `InJ`, `InI`).

- Sat1(k, S, q): some τ agrees with S below k and satisfies N below q.
- (k, S) is **good**: Sat1(k, S, q) for every q ∈ 𝖪ₜ.
- T1(k, S): some S′ agreeing with S below k has k ∈ S′ and (k + 1, S′) good.
- (k, S) is **correct**: (i, S) is good for every i ≤ k, and for every i < k: i ∈ S ⇔ T1(i, S).
- J = {k ∈ 𝖪ₜ : some (k, S) is correct}.
- **I** = the cut obtained from J by shortening twice: I₁ = {n : ∀m ∈ J, m + n ∈ J}, I = {n : ∀m ∈ I₁, m·n ∈ I₁}.

**Lemma T8.1 (dichotomy)** (`dichotomy`). If (k, S) is good, then T1(k, S), or some S′ agreeing with S below k has k ∉ S′ and (k + 1, S′) good.

*Proof.* Otherwise (k + 1, S ∪ {k}) fails Sat1 at some q₁ ∈ 𝖪ₜ and (k + 1, S ∖ {k}) fails it at some q₀ ∈ 𝖪ₜ. Take τ for (k, S) at q₀ + q₁ ∈ 𝖪ₜ. If k ∈ τ then τ witnesses Sat1(k + 1, S ∪ {k}, q₁), otherwise Sat1(k + 1, S ∖ {k}, q₀). ∎

No Ramsey argument and no induction is used here. Ramsey's theorem occurs only in T7.

**Lemma T8.2** (`correct_zero`, `correct_succ`, `correct_unique`, `inJ_hyp`). (0, ∅) is correct. A correct state of length k has a correct extension of length k + 1. Two correct states agree below the smaller length. J is closed downwards and under successor.

*Proof.* The first is Theorem T7.3: with k = 0, goodness says that for every q ∈ 𝖪ₜ some τ satisfies N below q. The second is the dichotomy: extend by 1 if T1 holds, by 0 otherwise. The third is induction on i ≤ k for "the two states agree below i", which is a set condition because S, S′ are sets (`isPred_agree`); at each step both values equal the truth value of T1(i, ·), which depends only on the state below i (`t1_congr`). ∎

**Lemma T8.3** (`i_down`, `i_add`, `i_mul`, `i_cast`, `i_sub`, `i_tm`, `i_aIn`, `i_aEq`). I is closed downwards and under + and ×, contains the standard numbers, and I ⊆ J. Hence I is closed under the eighteen term constructors, and atoms between terms in I have codes in I.

---

## T9. The term model

**Definitions** (`Eps`, `Eta`). ε(t, t′): some correct state of length i + 1 contains i, where i is the code of t ∈ t′. η(t, t′): the same for the code of t = t′.

**Lemma T9.1** (`exists_model_state`). For every finite list l of numbers in I there are k and S such that S satisfies N below k, every member of l is below k, and for every atom of l between terms t, t′: its code belongs to S if and only if ε(t, t′) (respectively η(t, t′)).

*Proof.* Take k ∈ I above the list. Then k ∈ J ⊆ 𝖪ₜ: there is a correct (k, S), and (k, S) is good, so some τ agrees with S below k and satisfies N below k. By Lemma T8.2 the correct states of length i + 1 agree with S, hence with τ, at i (`val_iff`). ∎

**Theorem T9.2** (`ax_e1`, …, `ax_m13b`; `termModel`; `termModel_isNF`). Every clause of N holds for ε and η at terms in I. Hence η is an equivalence relation on I and a congruence for ε, sing and up, and the quotient of I by η, with ε, is an `NFModel`. It satisfies extensionality and every instance of stratified comprehension.

*Proof.* An instance of a clause has at most four atoms, all between terms in I. Apply Lemma T9.1 to the list of these atoms and read the clause off `NSat`. The fields of `NFModel` are the clauses, with the witnesses given by the term constructors. The last sentence is Hailperin's theorem (`NFModel.isNF`). ∎

In Lean: `Tm` is the type of numbers in I, `NV` its quotient by η, `nmem` the relation induced by ε.

---

## T10. The formulas

What remains is to show that I, ε and η are defined by formulas of the language of NFU without parameters. This is done in three steps.

**Step 1: two-sorted arithmetic** (`BTm`, `BFml`, `bholds`). Terms are built from number variables, 0, 1, numerals, + and ×. Formulas are built from s = t, s ≤ t, t ∈ X (X a set variable), "t ∈ 𝖪ₜ", ¬, ∧, ∀ over numbers and ∀ over sets; set variables range over all objects of the model. `NSat`, Agree, Sat1, good, T1, correct, J, I, ε, η are written as such formulas (`nsatF`, `agreeF`, `sat1F`, `goodF`, `t1F`, `correctF`, `inJF`, `inIF`, `delta2`, `eps2`, `eta2`), and each is proved equivalent to the Lean predicate (`bholds_nsatF`, …, `bholds_delta2`, `bholds_eps2`, `bholds_eta2`). The 22 clauses of `nsatF` are generated by a script from the same list as the fields of `NSat`.

**Step 2: translation into the language of NFU with parameters** (`trB`, `sat_trB`). The parameters are 0, ℕ, 1 and the graphs of +, × and tw, as values of the variables 1–6. A number variable i becomes the variable 3i + 100 relativised to ℕ, a set variable X becomes 3X + 101, and terms are compiled into existential quantifiers over the graphs with the fresh variables 3j + 102. "t ∈ 𝖪ₜ" is written out from the definition of the cut, with "calm" as the formula "n ∈ ℕ and some member of n is strongly cantorian" (`fInSn`, `fKt`). `sat_trB`: if the parameters have their intended values and the environment represents the number and set variables, then the translation holds if and only if the formula of step 1 does.

**Step 3: the parameters are defined** (`isZ`, `isNat`, `isOne`, `fAddSpec`, `fMulSpec`, `fExpSpec`, `fTwSpec`; `parF`, `closeP`). 0 is the singleton of the empty set; ℕ is the set of objects that belong to every set containing 0 and closed under successor; 1 is the successor of 0. A set A is the graph of + if and only if it is a total functional relation on ℕ × ℕ with A(a, 0) = a and A(a, b + 1) = A(a, b) + 1 (`addSpec_iff`), and likewise for ×, 2ˣ and tw from the earlier graphs (`mulSpec_iff`, `expSpec_iff`, `twSpec_iff`). Uniqueness is by induction in U, which is available because the candidate graph is a set. The final formulas put the conjunction of these conditions in front and quantify the seven objects existentially:

- `nfDelta` = ∃ parameters (they are as specified ∧ x₁₀₀ ∈ ℕ ∧ tr(δ₂));
- `nfEps`, `nfEta` = ∃ parameters (… ∧ x₁₀₀ ∈ ℕ ∧ x₁₀₃ ∈ ℕ ∧ tr(ε₂)), respectively tr(η₂).

**Lemma T10.1** (`sat_parF`, `exists_par`, `sat_nfDelta`, `sat_nfEps`, `sat_nfEta`). The parameters exist, and they are determined by the specification. So `nfDelta` holds of x if and only if x is a number in I; `nfEps` holds of x, y if and only if both are numbers and ε(x, y); likewise `nfEta`.

The theorem of T0 follows with W = `NV`, mem = `nmem`, and π the quotient map.

*Size.* As two-sorted arithmetical formulas, δ₂ has 6,660 atoms, connectives and quantifiers and ε₂, η₂ have 1,662 each, not counting the terms. The terms are polynomials in which the pairing function is nested several times, and each of their operations becomes a quantifier with a graph formula, so the formulas of NFU are far larger. I tried to evaluate them and ran out of memory at 7 GB, so I do not know their size. The proof never writes them out: every lemma about them is by recursion on their construction.

---

## T11. Where the flat models come from

This part was finished earlier on 15 November (Phase 1 in `Host.lean`, Phase 0 in `NFUTerm.lean`). It replaces the Transfer Lemma of §4.3.

1. **The host.** For a calm number 3(d₀ + 3) + 2, Lemma 3.2 (`lemma_3_2`, §3.3) gives the structure 𝔏 of names: a level of the constructible hierarchy over a ladder, with a definable order <*, Separation and Collection. It is a host (`Model.host`), and the numbers of U are mapped onto its numbers by a map num that takes 0 to ∅, successor to successor and < to ∈ (`numIso`). For every set function g on the numbers of U and every k, the set of pairs (num i, num g(i)) with i ≤ k is a set of the host (`exists_inner_graph`).
2. **Closed levels.** The levels of 𝔏 at the stages ν₁ < … < ν_{d₀+2} of Lemma 3.2, each the least stage that is not small over the one before, form a sequence in 𝔏 of transitive sets, each a member of the next, each containing ω and every subset of each of its members (`next_absorb`), satisfying Collection for definable relations from a member into it (`next_coll_at`), and covering the initial segments of <* below its members (`cover_lim`).
3. **The tower.** In a host with such a sequence Λ(1), …, Λ(d + 1), the overlapping construction of a model of tangled type theory is carried out with the height d a number of the host (`Host.tower_of_ladder`, `Host.Tower`). This is the construction of your exposition (`nf_consistency_exposition.tex`): atoms and labels with prescribed adjacency, with position given by <*; paths, tokens and supports; the stages defined level by level by Separation. The typed statements hold for every descending chain of levels: `ext_ax`, `sing_ex`, `up_ex`, `inter_ex`, `compl_ex`, `cardinalOne_ex`, `vCross_ex`, `converse_ex`, `subset_ex`, `singletonImage_ex`, `insertion2_ex`, `insertion3_ex`, `typeLower_ex`.
4. **The flat model.** A tower gives a flat model of the same height (`Tower.flat`, `flat_ax`).

Items 1–3 together are `Model.exists_host_tower` (through `l32x_calm` and `exists_tower_of`).

Because the construction is formalised for an abstract host with the height as an element of the host, it applies at nonstandard heights. That is what the Transfer Lemma asserted and what could not be read off the con-nf formalisation.

---

## T12. What is checked, what is not, and what changed

**Checked.** All four files compile with Lean 4.35.0 and Mathlib, with no `sorry`; every declaration is checked by Lean's kernel on compilation. The files as delivered were rebuilt in an empty directory at 17:05 UTC on 15 November (291 s, 23 s, 18 s, 27 s). `#print axioms NFUCut.nfu_inf_interprets_nf` gives `propext`, `Classical.choice`, `Quot.sound`. A traversal of the constants that the theorem depends on finds 8,144 of them: from Lean core and Mathlib, from the seven NFU files of §2.4, from `ConNF.NF.Hailperin`, 22 from `ConNF.NF.Model` (the definition of `NFModel`), and from the four files above. None comes from the Holmes–Wilshaw formalisation, from `Crabbe.lean`, `MainLemma.lean` or `Tangle.lean`. (Since 16 November the definition of `NFModel` is in `ConNF/NF/NFModel.lean`, `Hailperin.lean` imports only that, and the four files build without con-nf: §12 of `nf_syntactic_interpretation_2026-11-15.md`.) So the theorem does not depend on the Transfer Lemma, on Crabbé's conversion, on the Main Lemma or on cut elimination.

**Not checked by Lean.**

1. (Resolved on 15 November, evening: `SetTheoryU.interpretsNF`, in `NFInterpretations.lean`.) The passage from "the translations hold in every model" to "U proves the translations" (completeness theorem).
2. That `Model` with `Infinity` is NFU + Infinity and that `IsNF` is NF. This is a matter of reading four definitions: `NFUCut.Fml`, `NFUCut.Model`, `Model.Infinity`, `ConNF.NF.IsNF`.
3. The free variables of the three formulas (T0, item 2). This no longer matters for the statement about derivations: there the domain and membership formulas are translated with every name sent to a bound variable, so they are closed by their type (`nfDomain`, `nfMem` in `NFInterpretations.lean`).
4. The files were compiled directly with `lean`, against a build of the con-nf repository that contains the `ConNF.NF.*` files. They are not yet part of the lake project, and the result has not been replayed with an external checker.
5. (Added at 17:50 UTC.) The converse, that NF interprets NFU + Infinity, has since been formalised: `nf_interprets_nfu_inf` in `NFSpecker.lean`, with Specker's theorem that NF proves Infinity. See `nf_infinity_not_choice_2026-11-15.md`.

**What changed from the first version of this note.**

- *Good states* were defined through flat models and placements (old T6), so the defining formulas mentioned hosts. Now a state is good if it extends, for every q in the cut, to a truth assignment satisfying N below q. The definitions are arithmetical and flat models occur only in the proof of soundness (T7.3).
- *The dichotomy* (old Lemma T6.2) used Ramsey's theorem at every step and needed the cut 𝖱 of calm exponents (old Lemma T5.2). Both are gone: the dichotomy is now Lemma T8.1, and Ramsey's theorem is used only in the proof of soundness, inside the host, with the exponent 2R + 1 and the bound tw.
- *Ramsey's theorem* is proved for sets of r values with the step function rstep, not for tuples with ρ.
- *Flat models* have no order ≺ of their own; "least" refers to <* of the host. Placements are sequences of the host indexed by its numbers, and spans are replaced by the uniform radius 5i + 6.
- *Terms*: all symbols binary, every number a term (null terms). There is no predicate "is a closed term".
- *States* are sets of numbers with a length, not codes of sequences.
