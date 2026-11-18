# The countdown machine and New Foundations

Let $M$ be the 192-state, two-symbol machine in `machine/NF_192_countdown.tm`. Its start state is `k:64`, the tape initially contains only zeroes, and its two directions are unbounded. Entering `halt` ends the run. The formal target is
$$
  M\text{ halts on the blank tape}\quad\Longleftrightarrow\quad
  \mathrm{NF}\text{ is inconsistent}.
$$
The NF on the right is the first-order theory of extensionality and stratified comprehension in the supplied archive. Consistency concerns derivations in that object theory. Lean supplies the metatheory.

## The change of truth values

Write application by juxtaposition, associating to the left, and let $Kx$ denote the constant function with value $x$. Here $(Kf)x=f$ and $Bfgx=f(Kx)(gx)$. This contender's tester gives $KB$ when $fx=x$ and $B$ otherwise. The two outputs differ. The archived CombNF expects its tester to return its constant $B$ on success and a distinct constant $R$ on failure.

The calculation that connects them is
$$
 B(Kf)(Kx)=K(fx).
$$
Apply each side to an arbitrary argument and use the two $B,K$ laws. Since $K$ is injective, the expression on the left equals $Kx$ exactly when $fx=x$. Now define the archived tester by the closed combinator whose action is
$$
 Q' f x = q\bigl(B(Kf)\bigr)(Kx)B .
$$
On success the last application gives $(KB)B=B$. On failure it gives $BB$. Interpret $R$ by $BB$. To see that $B\ne BB$, apply both to $K(Ku),Kv,B$. The first gives $u$ and the second $v$. Equality would collapse every two elements, contrary to $KB\ne B$. The closed expression and its reduction are in `NormalizedBasis.lean`. Thus each model of the machine algebra gives a model of the actual CombNF signature. The archived interpretations take CombNF through FunctionNF and NFU with Infinity to NF.

For the other direction start in an NF model with the archive's interpreted application and its $K,B$. For fixed parameters $t,b,f$, form the graph taking $x$ to $t$ if $fx=x$, and to $b$ otherwise. Assign $x,t,b$ and the output to one level and $f$ to the next level. Stratified comprehension and graph abstraction give a function $g_f$. Extensionality makes it unique. A second stratified graph sends $f$ to $g_f$. Choosing the fixed parameters $t=KB$ and $b=B$ gives exactly the tester of this contender. The construction uses parameters at the same level. Choosing $KB$ and $B$ afterwards respects stratification. The archive's nontriviality and the $B,K$ laws imply $KB\ne B$. This constructs the algebra in NF. First-order completeness then gives the equivalence between consistency of NF and existence of a normalized algebra in the proof's metatheory.

## The theory the register program actually enumerates

Write $C(a,b)=(a+b)(a+b+1)/2+b$. The code of implication is $2C(a,b)$ and the code of equality is $2C(a,b)+1$. In term position the latter code represents application. The code $2C(a,b)+2$ represents the witness $h(a,b)$, with $K(a)=h(a,a)$. The numerals for $q,s=qq,B=sq$ are $0,1,3$. In formula position the numeral $3$ says $s=q$. The exceptional equation $0\mathbin{\to}0=0$ on codes receives a separate case in the recursive evaluator.

Nine constructors of `Numerical.Deriv` introduce the axiom families. Its tenth constructor is modus ponens. The restricted implicational row recovers classical implication. If formula $3$ has no derivation, a maximal theory avoiding $3$ supplies a Boolean valuation. Its true equality atoms form an equivalence relation respected by application. The constant, congruence, Euclidean, tester and witnessing rows make the quotient of the natural numbers an extensional normalized algebra.

Conversely, in any normalized algebra, let $h(a,a)=Ka$ and, for unequal $a,b$, choose a point where their actions differ. Extensionality supplies such a point. No $x$ can satisfy $qx=x$. Indeed, evaluating that equality at $B$ gives $q x B=xB$. If $xB=B$, the left side is $KB\ne B$. If $xB\ne B$, the left side is $B$. Hence $qq\ne q$, so formula $3$ is false. Extensionality also gives $qq=KB$, since $q$ fixes no argument, and consequently $(qq)q=B$. With these interpretations every numerical axiom is true and modus ponens preserves truth. The term decoder is total on the naturals. This establishes
$$
  \text{formula }3\text{ has a derivation}\quad\Longleftrightarrow\quad
  \mathrm{NF}\text{ is inconsistent}.
$$

In the emitter's order, the following are the nine formulas. Write $G$ for $s=q$. Application associates to the left and implication associates to the right. The order condition in the first row compares numerical codes.

| Family | Formula |
| --- | --- |
| Restricted implication | $((c → u) → a) → ((a → c) → (b → c))$, for $u ≤ a$ |
| Positive test | $(a b=b) → (s=q a b)$ |
| Argument congruence | $(c=b) → (a c=a b)$ |
| Constant function | $(K b)a=b$ |
| Function congruence | $(a=c) → (c b=a b)$ |
| Abstraction | $B c a b=c(K b)(a b)$ |
| Euclidean equality law | $(a=b) → ((a=c) → (c=b))$ |
| Negative test | $((a b=b) → G) → (B=q a b)$ |
| Extensionality witness | $(b \,h(a,b)=a\,h(a,b)) → (a=b)$ |

## From a derivation to the binary table

The proof stack stores only derivable formulae. The register machine emits exactly the nine rows, performs modus ponens, and checks the goal. Conversely every finite derivation can be encoded as a finite sequence of commands. The counter eventually supplies such a sequence from any sound refill boundary. The proof checks the entire 2,928-instruction axiom emitter inside the selected 3,089-instruction program, including its repeated batches.

On the blank binary tape the first axiom entry is reached at step 16,813. At step 33,911 the table is at source ordinal 91 with a 42-cell margin. Register 0 then has logical value $-1$. The signed source proof follows the three initial axiom batches. They preserve that register until the first increment of register 0 changes it to zero. The ordinary natural-register search applies from then on.

For each of the 956 jump sites a finite decoder computation, combined with an induction on the length of the tape scan when needed, takes one canonical register frame to the next. For each of the 2,133 arithmetic sites the decoder prepares the gap, selects the register, increments or tests and decrements its unary field, then restores the file and the next address. The inductions allow arbitrarily large registers and arbitrarily long scans. The exceptional address shift on the zero exit of ordinal 3,087 is included. A zero decrement at ordinal 2,999 enters the sole halting transition.

Each completed source instruction takes a positive number of binary steps. After $n$ source instructions at least $n$ binary steps have elapsed. If the binary machine had halted between two inspected frames, its absorbing halt would still be visible at the next inspected frame. This yields both directions of the simulation, including reflection of a halt at an arbitrary binary time. Composing it with the numerical result gives the stated equivalence.
