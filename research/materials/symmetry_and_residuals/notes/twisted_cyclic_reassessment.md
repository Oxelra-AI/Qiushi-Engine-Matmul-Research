# twisted order-3 cyclic reassessment

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research purpose

The cyclic structured line is useful only if its symmetry model is mathematically exact. After analysis, the review pointed out that this investigation had treated only the untwisted cyclic rotation class. I tested the possible order-3 cyclic-type sandwich twists represented over characteristic zero by
\[
P=I,\qquad P=\operatorname{diag}(1,1,\zeta),\qquad P=\operatorname{diag}(1,\zeta,\zeta^2),
\]
with \(g=\operatorname{Ad}(P)\). The fixed locus of the natural twisted rotation is
\[
(X, gX, g^2X),
\]
and the associated cubic is
\[
C_P(X)=\operatorname{tr}(X\,gX\,g^2X).
\]

## First computation and correction

[twisted_cyclic_invariants.py](../code/twisted_cyclic_invariants.py) correctly built the cubic \(C_P\), its alternating exterior part, trace-quadratic coefficient, and Koszul--Young flattening. It produced stable modular values over \(p=65521,1000003\):

- \(\operatorname{KY}(C_P)=950\) in all three classes, with pure-cube calibration 70.
- The quadratic coefficient in the expansion along the tested scalar line had rank 8.
- The full \(\Lambda^3(\mathfrak{gl}_3)\) exterior target had \(GL_9\)-orbit dimension 64, larger than the affine \(\sigma_3(G(3,9))\) upper dimension 57.

However, its first interpretation of the invariant dimension was wrong. The numbers 245 and 243 came from inserting \(\operatorname{tr}(g)\) on \(M_3\) into the Burnside formula for an action on \(M_3^{\otimes 3}\). That is not the trace of the order-3 twisted rotation on the tensor product.

review verified the correction and gave the exact conjugating map. For
\[
\rho_P(X,Y,Z)=(g^2Y,g^2Z,g^2X),
\]
which fixes \((X,gX,g^2X)\), the map
\[
Q(X,Y,Z)=(X,gY,g^2Z)
\]
satisfies
\[
Q^{-1}\rho_PQ(X,Y,Z)=(Y,Z,X).
\]
Thus the actual order-3 twisted cyclic actions are linearly conjugate to the pure cyclic rotation. Their invariant tensor space has dimension 249, not 245 or 243.

## Action-level self-check

I wrote [twisted_cyclic_action_selfcheck.py](../code/twisted_cyclic_action_selfcheck.py) and ran it over \(p=65521\) and \(p=1000003\). The output is [twisted_cyclic_action_selfcheck.json](../results/twisted_cyclic/twisted_cyclic_action_selfcheck.json).

For all three representatives and both primes, the script verifies the following algebraic identities on the full coordinate basis (not by random sampling):

1. \(\rho_P^3=1\).
2. \(\rho_P\) preserves \(T(X,Y,Z)=\operatorname{tr}(XYZ)\).
3. \(Q^{-1}\rho_PQ\) is ordinary factor rotation.
4. The fixed-locus basis generators have the form \((X,gX,g^2X)\).
5. The coefficient action on the 729 coordinate tensors has orbit histogram
   \[
   1:9,\qquad 3:240,
   \]
   hence fixed-space dimension \(9+240=249\).
6. The fixed-locus trilinear form satisfies the coefficient identity
   \[
   \operatorname{tr}(X\,gY\,g^2Z)=\operatorname{tr}((XP)(YP)(ZP)),
   \]
   hence the diagonal cubic satisfies \(C_P(X)=\operatorname{tr}((XP)^3)\).
7. The full exterior target has radical \(KP^{-1}\): the contraction \(\iota_{P^{-1}}\omega_P\) is zero.
8. On the adapted eight-dimensional space
   \[
   \mathfrak h_P=\{X:\operatorname{tr}(XP)=0\}=\mathfrak{sl}_3P^{-1},
   \]
   the projected trivector has \(GL_8\)-stabilizer dimension 8, orbit dimension 56, and is outside \(\sigma_3(G(3,8))\) by the same dimension comparison as the pure cyclic Cartan form.
9. The adapted trace-grading quadratic coefficient in
   \[
   X=M+sP^{-1},\qquad M\in\mathfrak h_P,
   \]
   has rank 8.

## Mathematical interpretation

The apparent twisted order-3 cyclic classes do not produce a new weaker rank-22 skeleton. In the correct order-3 model they are adapted-coordinate versions of the pure cyclic rotation. The old cyclic theorem should therefore be worded as applying to cyclic-type order-3 actions after the coordinate adaptation above, not as a statement tied only to the literal \(P=I\) coordinates.

The existing pure cyclic mechanisms transfer as follows:

- Fixed terms are cubes only after the conjugation by \(Q\) (or equivalently after using the adapted coordinates). In original coordinates a fixed term looks like \(x\otimes gx\otimes g^2x\), whose exterior part need not vanish. Therefore any theorem must state the adapted-coordinate model explicitly.
- The exterior \(m\ge 4\) result transfers: on \(\mathfrak h_P\) the alternating target is in the open \(GL_8\)-orbit and not in \(\sigma_3(G(3,8))\).
- The trace-grading quadratic rank-8 result transfers on \(KP^{-1}\oplus\mathfrak h_P\). As before, it gives \(f\ge 8\) only after the mixed-trace equations force the free orbit representatives to vanish on \(P^{-1}\).
- The residual Waring problem is not changed by these order-3 twists. The hard `(10,4)` question remains the residual rank over the rank-four exterior fiber and internal frames; the `m>=5` branches remain governed by full mixed-trace equations and conciseness.

## Source support for the bivector-preserver idea

A knowledge request retrieved Ghorpade--Patil--Pillai, `\cite{ghorpade2009decomposable}`, which proves a structure theorem for decomposable subspaces of exterior powers. The useful specialization for \(\Lambda^2 V\) is that a linear subspace all of whose nonzero elements are decomposable is of close type I, \(v\wedge W\), or close type II, \(\Lambda^2 W\) with \(\dim W=3\), with the corresponding dimension ranges. This is relevant to the future analysis commutator-map route, but it is a theorem about decomposable subspaces, not by itself a full linear-preserver theorem for a map \(\Lambda^2V\to\Lambda^2V\). Lau--Lim 2024, `\cite{lau2024adjacency}`, records a modern adjacency-preserver theorem and cites the linear-preserver literature. The exact preserver statement needed for the commutator route still has to be formulated and matched to the actual map.

## Consequence for route choice

The twisted order-3 exploration did not open a new construction class. It instead repaired the cyclic formulation: all order-3 cyclic-type actions are conjugate to the ordinary cyclic action in adapted coordinates, so effort should not branch into separate twisted searches. The next high-value work is to turn this corrected formulation into a clean theorem note and then attack one of the remaining real cyclic obstacles:

- for `(10,4)`, use a sourced decomposable-subspace/preserver route for the analysis commutator map or another exact finite-distance analysis of the residual rank condition;
- for `m>=5`, build the frame-free conciseness relaxation based on the first catalecticant and the condition \(\operatorname{tr}(X^2Y)\in\sum_j\operatorname{Sym}^2(P_j)\), using the verified rank-23 cyclic controls only as calibration;
- keep the unrestricted independent-UV rank-one-span incidence separate, since no cyclic result covers arbitrary rank-22 decompositions.
