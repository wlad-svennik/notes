# A Geometric Algebra type formalism for doing computations in hyperbolic geometry

Jan Trecht and I have developed a simple formalism for doing computations in 2D hyperbolic geometry. The ideas are inspired by Isaak Yaglom's two books *Complex Numbers in Geometry* and *A Non-Euclidean Geometry and Its Physical Basis*. I summarise it here. The formalism essentially constructs a bijection between $2 \times 2$ real matrices and hyperbolic cycles. The hyperbolic congruences which act on these cycles are also represented by the same matrices. The main current application is to visualise $2 \times 2$ real matrices as hyperbolic cycles, perhaps in order to plot the dynamics of iterative matrix algorithms like the QR algorithm.

## Positive and negative matrices

The matrices we consider are all $2 \times 2$ real. A matrix is called positive if its determinant is positive, and is called negative if its determinant is negative.

## Hyperbolic cycles

In Euclidean geometry, there are the following types of cycles:

- Point
- Line
- Circle

In hyperbolic geometry, by contrast, there are five kinds of cycles:

1. Point
2. Line
3. Circle
4. Horocycle
5. Hypercycle

In the Poincare half-plane model of hyperbolic geometry, all five cycles are represented by a pair of conjugate (in the sense of complex conjugation) Euclidean circles. By contrast, in the Poincare disk model, the two cycles are related by the inversion $z \mapsto 1/\overline z$.

In the Poincare models, the five cases are characterised respectively by:

1. A hyperbolic point is a pair of conjugate Euclidean points
2. A hyperbolic line is a pair of conjugate Euclidean circles which are the same as each other. Equivalently, they are both orthogonal to the boundary of the hyperbolic plane.
3. A circle is a pair of conjugate Euclidean circles which never meet the boundary of the hyperbolic plane.
4. A horocycles is a pair of conjugate Euclidean circles which are tangent to the hyperbolic plane.
5. A hypercycles is a pair of conjugate Euclidean circles which both meet the hyperbolic plane at two distinct points.

## Oriented cycles and positive matrices

An *oriented cycle* is defined to be a cycle with an orientation attached to it. This orientation is discrete and binary, and is either clockwise or anticlockwise. A point is considered unoriented. (As an aside, in circumstances other than the present one, it may be useful to allow points to be oriented while considering lines instead to be unoriented).

The space of oriented hyperbolic cycles can be parametrised by $2 \times 2$ positive matrices. They are in one-to-one correspondence. This correspondence connects the algebraic structure of $2 \times 2$ matrices with the geometric structure of oriented hyperbolic cycles.

The bijection works as follows: Define a *spear* to be an oriented hyperbolic line. Every spear can be given as $pq$ where $p$ and $q$ are points on the boundary of hyperbolic space. Since spears are oriented, we have that $pq \neq qp$. A spear is tangent to an oriented cycle if they are tangent as unoriented figures, and their orientations are the same at the point of contract. Denote the set of spears tangent to an oriented cycle $C$ by $T(C)$. Given a matrix $M$, denote by $G(M)$ (the "graph of $M$") the set of spears $\{p(Mp) \mid p \in \mathbb{RP}^1\}$.

**Proposition**: *Given a positive matrix $M$, there exists a unique oriented cycle $C$ such that $G(M) = T(C)$. Conversely, given an oriented cycle $C$, there exists a unique positive matrix $M$ such that $G(M) = T(C)$.*

We can therefore abuse notation and treat oriented cycles and positive matrices as the same thing. Matrix-vector multiplication $Mv$ then happens by finding the spear from $v \in \mathbb{RP}^1$ that is tangent to the oriented cycle $M$, and finding its intersection with the hyperbolic plane. The point of intersection is $Mv$. Matrix-matrix multiplication $MK$ happens simply by collecting the spears $v(MKv)$. Matrix inversion is the same thing as reversing the orientation of the cycle (as can easily be checked).

The five different cycles correspond to the five possible Jordan normal forms of a positive matrix. Respectively, we have that:

1. A point has JNF $\operatorname{diag}(i\lambda,-i\lambda)$.
2. A line has JNF $\operatorname{diag}(\lambda,0)$.
3. A circle has JNF $\operatorname{diag}(z, \overline z)$.
4. A horocycle has JNF $\begin{pmatrix}\lambda & 1\\ 0 & \lambda \end{pmatrix}$.
5. A hypercycle has JNF $\operatorname{diag}(\lambda, \mu)$.

where $\lambda$ and $\mu$ are positive reals.

Let $M$ denote an oriented cycle, and $P$ denote a hyperbolic congruence. Note that these are both the same type of object, a $2 \times 2$ real matrix! Applying the congruence $P$ to the cycle $M$ is simply $PMP^{-1}$. $P$ and $M$ are only relevant up to scalar factor, so we can also do $PM\operatorname{adj}(P)$, where we use the matrix adjugate.

## Negative matrices and pencils of equal inclination

The value of $G(M)$ for a negative matrix is no longer equal to $T(C)$ for a hyperbolic cycle. Instead, denote by $E(L,\theta)$ the set of spears which meet the spear $L$ at angle $\theta$. We have that:

**Proposition**: *If $M$ is an negative matrix, then there exists a unique spear $L$ and unique angle $\theta$ such that $G(M) = E(L,\theta)$. Conversely, if $L$ is a spear and $\theta$ is an angle, there exists a unique negative matrix $M$ such that $G(M) = E(L,\theta)$.*

## The larger group of hyperbolic Laguerre transformations

We can use matrices over the double numbers $\mathbb R \oplus \mathbb R$ instead of the real numbers $\mathbb R$. [TBD]

## Explicit connections to Clifford algebras

As a Clifford algebra, we are using $\operatorname{Cl}_{1,1}(\mathbb R) \cong \operatorname{Cl}_{2,0}(\mathbb R)$. For hyperbolic Laguerre geometry, the Clifford algebra $\operatorname{Cl}_{2,1}(\mathbb R)$ gets used. Connections to exterior products and multivectors are TBD.

## Connections to existing approaches to doing hyperbolic geometry computationally

[TBD]