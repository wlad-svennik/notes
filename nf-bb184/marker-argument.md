# Variable-marker tester for pure NF

Write application by juxtaposition and put $D(x,y)=(J(Kx))y$. The tester axiom is

$$((D(x,y)=x)\to (D(x,x)=x))\to y=x.$$

On any carrier with at least two elements this says precisely that $D(x,y)=x$ for $x\ne y$, and $D(x,x)\ne x$. To see the second assertion, choose any $y\ne x$ and use the same instance. For the first assertion use the classical truth table for implication.

## From a marker chart to pure NF consistency

`VariableSyntax.lean` abstracts an injective pair $p(x,y)$ with the type shift required by the stratified combinatory basis. Its action is $p(x,y)f=K^2(f(Kx)y)$. Applying two equal pairs to the identity and the constant identity separates their two components.

Let $d(z)=zJJJ$ and $Fz=p(dz,dz)$. For each pair $x,y$, form $H_{xy}z=D(Fz,p(x,y))$. If $x\ne y$, pair injectivity gives $Fz\ne p(x,y)$ for every $z$. The off-diagonal law and extensionality then give $H_{xy}=F$. When $x=y$, evaluate both functions at $z=K^3x$. At this point $Fz=p(x,x)$, so the diagonal law gives $H_{xx}\ne F$.

It follows that $D(F,H_{xy})$ takes the fixed value $D(F,F)$ off the diagonal and the fixed value $F$ on the diagonal. Those two values differ. Four applications to fixed arguments, chosen successively by extensionality, preserve that inequality and compensate for the four-level type shift of the construction. This supplies a weak tester and therefore a model of pure NF by `NF196.Weak.consistent`. `VariableDetector.lean` implements these term abstractions and the conversion.

## From pure NF consistency to a marker chart

In an NF model, choose distinct objects and a stratified fixed-point-free switch $t(x)$, equal to the second choice when $x$ equals the first, and equal to the first choice otherwise. On a function $f$ take the function whose value at $x$ is $f(x)$ if $f(x)\ne x$ and $t(x)$ if $f(x)=x$. For $f=Ka$ it returns $a$ when $a\ne x$ and a value different from $a$ when $a=x$. The standard constant-function selector incorporates this operation in $J$ and ensures $JJ=B$ and $B\ne J$. This construction appears in `DataMarker.lean` and `VariableMarkerNF.lean`.

## Numerical source interface

`Moving186Logic.lean` defines the numeric rows and the derivability relation. `MovingRows.lean` structures the quotient chart and evaluates ground terms in a chart. `Moving186NF.lean` connects these components in the theorem `Moving186.deriv_goal_iff_nf_refutation`. The numerical theorem is independent of the state count of a literal table which implements its rows.
