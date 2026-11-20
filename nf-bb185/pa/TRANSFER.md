# The PA transfer from 192 states to 185

Let $H_{192}$ assert that the original nine-row, 192-state **pure NF countdown** machine halts from a blank tape. Let $H_{185}$ assert the same for the eight-row, 185-state table in this directory's parent. All machine sizes count working states. Both halting sentences use finite two-ray traces. The new table has SHA-256 `5504746071e10a0555754b55efc2da348ebfb1f8e8ab5bc7af474eaad81f60fe`. The axiom of counting plays no role.

The machine-to-machine claim is

$$
                          \mathrm{PA}\vdash H_{192}\longrightarrow H_{185}.
$$

Here is a proof using the published 192-state arithmetic reduction. There is also a direct proof of $\mathrm{PA}\vdash\neg H_{185}\to\mathrm{Con}(\mathrm{PA})$. Its verification status is recorded in the [README](README.md). The direct proof has no dependency on correctness of an earlier machine.

## How to locate the Lean argument

The formal proof works inside an arbitrary model of PA with carrier in Lean's universe `Type`. Its natural numbers and proof lengths may be nonstandard. A halt in that model yields a nine-row proof by `NineReverse.h192_implies_proof_of_scope`. Under the assumption of no eight-row refutation, `Comparison.old_rows_of_no_refutation` constructs an old row algebra whose equality and operations are definable on representatives in the ambient arithmetic. `Old.model_excludes_old_proof` evaluates the ambient model’s own derivations in this algebra. It excludes the nine-row proof just obtained. Hence there is an eight-row refutation, and `refutation_reaches_register_halt` followed by `Symbolic.tape_of_coverage` produces an internal blank-tape trace of the literal 185-state machine. Arithmetic completeness gives the object-theory implication.

The proof below also explains the connection in terms of first-order proof translations and names the finite theories involved. The Lean verification uses the definable-algebra argument above.

## 1. What must transfer

Let $U_9$ and $U_8$ be the finite universal theories corresponding to the nine-row and eight-row machines, respectively, in a language with a binary relation $E$, application, a letter and a binary witness function. Use the actual nonlogical rows and the negation of the goal $G=E(jj,j)$. The implication-only propositional row governs numerical proof search. Here $j$ names the single raw letter in each language. Its interpreted role changes with the rows. The goal code in both machines is 3. Write $T_0$ for the old normalized algebra theory. Its finite language has ordinary equality, application, the unary constant-function constructor $K$, the stratified abstractor $B$, and a fixed-point tester $q$. Its distinct test outputs are $K(B)$ on success and $B$ on failure. Write $D_8(3)$ for the existence of a finite numerical proof of 3 from the actual eight rows.

The first two implications below are inputs from the NF192 arithmetic paper. The next sections prove the remaining three.

$$
 H_{192} \ \Rightarrow\ \neg\mathrm{Con}(U_9)
     \ \Rightarrow\ \neg\mathrm{Con}(T_0)
     \ \Rightarrow\ \neg\mathrm{Con}(U_8)
     \ \Rightarrow\ D_8(3)
     \ \Rightarrow\ H_{185} .
$$

In the first implication a halt occurs with 3 in the cache. The invariant for the cache then yields an internally coded numerical proof of 3. Sections 2 and 3 of the NF192 paper give the simulation and the conversion from a numerical proof to a first-order refutation. For the second implication section 4 proves $\mathrm{Con}(T_0)\to\mathrm{Con}(U_9)$ already in PRA. The off-diagonal witness in that proof picks a point separating two unequal functions in a coded countable normalized algebra. The normalized laws imply $qq=K(B)$, $(qq)q=B$, and $qq\ne q$, so the interpretations of the old machine's ground constants have their required values. These two inputs concern the pure countdown release. [NF192 arithmetic paper and source supplements](https://github.com/wlad-svennik/notes/releases/tag/nf192-pa)

## 2. The finite interpretation that changes the calculus

In a $U_8$ structure put $Kx=h(x,x)$ and $B=jj$. The constant-function row and the Euclidean row give reflexivity of $E$ by applying the Euclidean row with the same instance $E((Kx)z,x)$ as both premises. The Euclidean row then gives symmetry and transitivity. Both argument positions of application respect $E$. To see that $K$ respects $E$, compare the two putative constants at the single witness $h(Kx,Ky)$ and use extensionality. Thus application and $K$ descend to the quotient by $E$. The extensionality witness stays in the raw language. On the quotient the $K$ and $B$ equations hold and application is extensional. The goal axiom gives $B\ne j$.

Put $d(x,y)=(j(Kx))y$. Reading the literal tester row with symmetry of $E$ gives
$$
     (d(x,y)=B\ \to\ d(x,x)=B)\ \to\ x=y .
$$
For $x\ne y$, classical logic gives both $d(x,y)=B$ and $d(x,x)\ne B$. For every $x$ there exists a distinct $y$, since $B\ne j$. Consequently
$$
    x\ne y\Rightarrow d(x,y)=B,\qquad d(x,x)\ne B.
$$
Here the old and new letters and their Boolean outputs need care. The new row allows the diagonal value to vary with $x$. To get two *fixed* outputs use
$$
                         Qfx=d(B,d(fx,x)).
$$
If $fx=x$, the inner value differs from $B$, so the outer value is $B$. If $fx\ne x$, the inner value is $B$, so the outer value is $d(B,B)\ne B$. The closed combinatory term for $Q$ and its displayed application law are `NF196.Weak.norm` and `norm_law` in the eight-row release. In particular the definition of the test is usable inside a first-order interpretation.

Use this algebra on the quotient for FunctionNF. Its truth and falsity constants are $B,d(B,B)$, its application is the quotient application, and its equality selector is $(Q(Kx))y$. The finite syntax operations `kpush`, `abs`, and `tr` in `ArbitraryBooleanFNF.lean` verify the stratified abstraction axioms for these fixed first-order operations. The published `FNF.fnInterpretsNF` supplies fixed formulas for the interpreted NF domain, equality and membership. Inside that interpretation use the fixed graphs of `DirectNFToNormalized.lean` from the 192-state release. In particular its two tester graphs use independent return parameters in stratified comprehension before substituting $K(B_0)$ and $B_0$, where $B_0$ is the abstractor in the interpreted normalized algebra. There is no need to identify $B_0$ with the new machine's $B$.

This composition gives fixed formulas interpreting the **finite** theory $T_0$ in $U_8$. The distinction between a construction by fixed formulas and the mere existence of some equiconsistent theory matters here. To spell out the proof-code consequence, take the interpretation's domain, equivalence, operation graphs and any parameter package. The nonemptiness, congruence, totality and uniqueness modulo equivalence, existence of suitable parameters, and validity of each translated $T_0$ axiom are finitely many ordinary first-order obligations. The preceding constructions verify them in every $U_8$ structure. First-order completeness outside PA supplies a *fixed finite tuple* of $U_8$ derivations of the obligations. With parameters, first choose an admissible tuple existentially and carry its defining condition throughout the interpretation.

Now translate an arbitrary $T_0$ refutation line by line, inserting those fixed proof strings and using the operation graphs for term values. Discharge the parameter package by its existence theorem. This is a primitive recursive operation on proof codes. PA proves its correctness by induction on the coded derivation, including variable renaming and the quantifier rules. The finitely many closed seed checks are true computations on numerals and PA proves them. This yields
$$
                    \mathrm{PA}\vdash
                    \neg\mathrm{Con}(T_0)\to\neg\mathrm{Con}(U_8).
$$
This argument needs no uniform soundness principle for NF, and no countable choice of separate proof strings indexed by the NF comprehension scheme. The theory whose proof is being translated has finitely many axioms. The use of first-order completeness here need not itself be internalized in PA.

## 3. From a first-order refutation to an eight-row numerical proof

Work in PA. From an equality-free first-order $U_8$ refutation extract a finite propositionally inconsistent family of ground instances of its universal axioms and the ground assumption $\neg G$, by effective Herbrand reduction. One implementation puts the universal closures on the left and $G$ on the right of a sequent, applies pure first-order cut elimination, replaces the remaining free parameters by the constant $j$, and collects the witnesses of the existential rules on the one-sided presentation. First-order logic here has no induction rule. The ordinary rank-by-rank cut elimination for pure predicate logic is provably total in PA. Section 3 of the NF192 paper gives the corresponding reduction for exactly this quantifier pattern. Changing the finite list of universal matrices preserves the argument.

If the extracted row instances are $C_1,\ldots,C_m$, the implication chain $C_1\to\cdots\to C_m\to G$ is a propositional tautology. A finite truth table, Hilbert deduction and the fixed proofs of $K$, $S$ and Peirce from restricted row 0 compile it to the machine's implication calculus. The side conditions on row 0 use $u\le a$ and each input is bounded by its encoded implication. Use the *literal* seven nonlogical constructors for the $C_i$ and apply modus ponens $m$ times. Nonlogical row indices with unused arguments may be specialized to zero, with the unused bound parameter $u=0$. The input language is equality-free, so no hidden rule of equality replacement for the witness function is inserted. The numerical implication has the collision $\mathrm{imp}(0,0)=0$. Every ground first-order atom encodes to an odd positive number, and each implication of positive encodings is positive. The collision does not arise in this ground encoding. The abstract Hilbert proof templates are valid for arbitrary numerical inputs, including zero.

This gives the claimed $D_8(3)$. Equivalently take a ranked proof pool, giving each leaf rank zero and each detachment a rank strictly greater than both parents. In every PA model the pool predicate contains the rows and is closed under detachment, by `NF185PA.Pool.leaf` and `mp`. Induction on an internally coded list of proof lines therefore puts its final formula in the pool.

## 4. From a proof witness to the literal halt

The eight-row compiler and the scanner work on the ambient PA model's own numbers. A derivation in the pool yields a sequence of commands observing cache 3. The compiler accounts for the fact that the last axiom in an eight-row AX batch is discarded in its final fall-through. It obtains that axiom from a nonfinal batch when necessary. The scanner reaches the encoded command prefix from any entering search candidate and payload unless it has already observed the goal.

The arithmetic register program has 2,959 instructions. Its AX body at address 40 returns at 2837; it emits the rows in the literal order, retains both updated parameters and branches back via 39. The remaining rank can be nonstandard. Induction on that rank composes the batches. The MP address is 2838. The actual comparison, falling through into the cache operation, implements the required detachment and pop. The cache test starts at 2939, with the sole halting instruction at 2942. From the signed bookkeeping origin at 40, 98 actual register steps reach the margin at 118. An absorbing terminal configuration and the commutation of iterates transfer eventual termination from that origin to the margin.

The literal binary table reaches the margin from blank in 59,905 steps. Symbolic frame contracts cover its 7,762 applicable register branches, including the two signed cases at the halting gate. The repeat-window induction permits any register and padding lengths in the PA model. Induction on the internally coded source execution lifts its terminal address to an internally coded blank-tape trace. This proves $D_8(3)\to H_{185}$ in PA. Composing sections 1–4 gives the stated machine-to-machine implication. It says that halting transfers; the proof codes, traces and running times may all change.

Finally the contrapositive and the old PA theorem $\neg H_{192}\to\mathrm{Con}(\mathrm{PA})$ give $\mathrm{PA}\vdash\neg H_{185}\to\mathrm{Con}(\mathrm{PA})$. The independent direct proof instead builds a definable eight-row countermodel from failure of the proof search and interprets PA proof checking in that countermodel. Each route gives the usual second-incompleteness consequence under consistency of PA. Assuming consistency of NF also supplies actual nonhalting of the published table, which rules out each PA-provable numerical upper bound on the running-time Busy Beaver function at 185.
