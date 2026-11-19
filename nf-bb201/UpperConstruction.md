# Why the 201-state machine runs forever

Let $A$ be NF with Rosser’s Axiom of Counting. The paper construction below gives an applicative chart from a model of $A$. The checked theorem `C201.binary_iff_counting_chart` then gives nonhalting for the released binary table. The two relevant integers are **three old evaluations to construct the splice** and **one new evaluation to recover the abstraction operator**.

## Allocate the labels

Work inside a model of $A$. Write $V$ for its universe. A full chart assigns a label in $V$ to each internally represented total self-map of $V$. Use an old bijection $e_0$ between $V$ and the set of such graphs, with type-level ordered pairs. A set $x$ can be represented injectively by its two-valued characteristic graph, the graph objects inject back into $V$, and Cantor–Bernstein gives the bijection. Write $x\cdot_0 y$ for evaluation in this chart and $K_0(x)$ for the old label of the constant row with value $x$.

Take a fixed-point-free two-valued old row $f$ and any old label $g$. Define

$$
 F(x)=K_0^3\bigl(((x\cdot_0 f)\cdot_0 g)\cdot_0 f\bigr).
$$

Each evaluation lowers the type of the varying label by one, and each constant constructor raises it by one. This makes the graph of $F$ homogeneous. Fixed parameters appearing at different types may be entered as separately quantified parameters and specialized to the same value after comprehension. Its image is $K_0^3[V]$, since a triple constant with value $y$ gives $K_0^3(y)$. Let $a_0$ be its old label. Choose the old labels $a_{n+1}$ for distinct one-point perturbations of the identity, for example by varying the image of a single input over an injectively indexed sequence. Counting makes the native natural-number field strongly Cantorian, so these indexed families and the required shifts of their indices have set graphs.

Simultaneously transpose every $a_{n+1}$ with $K_0(a_n)$ in the old coding bijection. The former labels represent distinct nonconstant perturbations, the latter distinct constants. The $F$ label belongs to neither list because its range omits all nonconstant labels and is infinite. The new coding, with application written by juxtaposition, satisfies $K(a_n)=a_{n+1}$. It still represents $F$ at $a_0$, and preserves the row at $f$.

## Insert the Counting operation

Take the abstraction operator $B$ of the new full chart, so $Bxyz=(x(Kz))(yz)$. Its row is nonconstant and fixes every double constant. It differs from identity at $Kx$ for every nonconstant row $x$. The equality $B(Kx)=Kx$ would give $x(yz)=xz$ for all $y,z$, forcing $x$ constant. Thus $B$ occupies no changed label whose new row is a constant or a finite perturbation of identity. It also differs from $a_0$. A genuine auxiliary fixed-point tester $q_*$ has $Bq_*=q_*$, while $F(q_*)$ is an old constant label. Here $q_*$ is an old nonconstant label because its row has infinite image and infinite complement, excluding either kind of changed row. For any such tester the probes at $Kx$ give all singleton predicates, and its image omits the infinitely many constant rows with values outside its two answer values.

Set $v=KB$. Adjoin the finite prefix to the allocated labels to form the chain

$$
 v,\ Kv,\ K^2v,\ K^3v,\ a_0,\ a_1,\ldots .
$$

The entries are distinct by injectivity of $K$, the nonconstancy of $a_0,B$, and $B\notin\{a_n\}$. Define $J$ to advance along this chain and return $v$ everywhere else. The countably indexed chain, finite prefix and default give a represented total function. Its image is countably infinite, while $V$ is uncountable, by Cantor’s theorem on the strongly Cantorian natural-number field. Its complement is infinite, since the chain is countable. Thus its row is neither constant nor a finite perturbation of the identity. It differs from $a_0$ because its image contains the old nonconstant label $a_0$. The remaining chain labels represent constants, so $J$ itself is outside the chain.

Form the genuine tester $q$ in the new full chart by requiring $(qu)x=KJ$ when $ux=x$ and $(qu)x=J$ otherwise. These values are distinct since $J$ is nonconstant. Both $f$ and $q$ are outside the chain. The row of $f$ has just two values, unlike $F$. For $q$, evaluation at $Kx$ gives a nonconstant singleton-test row, whereas $F$ always returns an old constant label. The old and new rows at $q$ and $J$ agree by their range and complement sizes. The row at $KJ$ also agrees in the two charts. Indeed, $J$ is outside the allocated $a_n$, so its old constant label does not occur among the transpositions. Likewise the old and new iterated constant constructors agree through $K^3v$, since $v,Kv,K^2v$ are outside the allocated family.

Now $Jq=v$, so $(Jq)q=B$. The one exceptional readback in the chain is the step from $K^3v$ to $a_0$. Since $f$ has no fixed point, $qf=KJ$, $(KJ)g=J$, and $Jf=v$. These are precisely the three old evaluations in $F(q)$. Consequently $a_0q=K^3v$. Every other successor in the chain is a constant with value its predecessor. Hence $(Ja)q=a$ for every $a\in\operatorname{ran}J$, which gives the machine’s scalar axiom $(J(Jx))q=Jx$. Finally $q$ has no fixed points by applying any alleged $qx=x$ to $J$ and splitting on $xJ=J$. Thus $qq=KJ$, and $(qq)q=J$. These are the terms used by the actual machine.

Ordinary first-order completeness supplies a countable Henkin model from consistency of $A$. If a Skolem separator for unequal rows is needed for the numerical syntax, choose their least distinguishing argument in that countable presentation. The least element is taken in the external enumeration of that domain. The conclusion is the metatheoretic implication $\operatorname{Con}(A)\Rightarrow \neg H_{201}$.

## Discharging the upper premise in ZF

Theorem 21.1 of the v15 research manuscript gives the written consistency comparison between $A$ and $C_{\beth}$. The latter adds to Zermelo set theory with Choice one axiom for each standard $n$. Its witness has domain $\beth_n+1$, starts at $\omega$, takes cardinal power sets at successors and suprema at nonzero limits. In particular its last value is $\beth_{\beth_n}$. In the constructible universe $L$, choose a limit ordinal above all the requisite cardinals and sequence witnesses. For instance $\lambda=\beth_{\beth_\omega+\omega}+\omega$, calculated in $L$, suffices. The transitive rank $V^L_\lambda$ satisfies Zermelo set theory with Choice. It contains all the displayed sequences, their graphs, and the power sets and cardinal comparisons used to verify each. ZF therefore proves $\operatorname{Con}(C_{\beth})$ and, using the cited comparison, $\operatorname{Con}(A)$. This step uses the manuscript’s written comparison. The checked upper-tail lemmas cited below start with the chart data supplied by the construction.

## Files in `Counting201_inputs.zip`

- `theory/readback_201.md` specifies the preferred machine’s axiom and chart. Its reference to the earlier three-read construction resolves to `theory/native_zero/qzero/theorems.md` inside the archive.
- `theory/lean201/C201UpperTail.lean` proves `NF201.Upper.Tail.toChart` from the displayed tail data and `NF201.Upper.three_read_bridge` from the matching old and new rows.
- `lean/physical-201-native.zip` contains `C201Counting.lean` and its literal-machine dependencies.
- Inside `lean/NFU-model-interpretations.zip`, `ChartFamilies.lean`, `module-overlays/ChartSplice.lean` and `module-overlays/ChartSwaps.lean` formalize relabellings and indexed families under the chart hypotheses stated in those files.
