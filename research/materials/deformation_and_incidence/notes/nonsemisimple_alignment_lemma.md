# nonsemisimple termwise-alignment lemma

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

This note records the algebraic point needed to separate the nontransverse gauge stratum from the transverse symmetry quotient.

## Setting

Work over an algebraically closed field of characteristic zero, or over a sufficiently large characteristic not colliding with the Jordan decompositions being used.  A noncentral stabilizer Lie element is a triple
\[
(P,Q,R)\in\mathfrak{gl}_3^3
\]
acting on the three matrix-factor spaces by
\[
D_U(X)=P^T X-XQ^T,
\quad
D_V(Y)=Q^T Y-YR^T,
\quad
D_W(Z)=ZR-PZ.
\]
For a decomposition
\[
T_{333}=\sum_i u_i\otimes v_i\otimes w_i,
\]
being termwise aligned with this Lie element means that for each term there are scalars \(a_i,b_i,c_i\) with \(a_i+b_i+c_i=0\) and
\[
D_Uu_i=a_i u_i,
\quad D_Vv_i=b_i v_i,
\quad D_Ww_i=c_i w_i.
\]
Because the three tensor flattenings of \(T_{333}\) have rank 9, every exact decomposition spans each factor space:
\[
\langle u_i\rangle=\langle v_i\rangle=\langle w_i\rangle=M_3.
\]
Thus termwise alignment forces each of \(D_U,D_V,D_W\) to have a basis of eigenvectors, hence to be semisimple as a linear operator on the corresponding 9-dimensional space.

## Lemma

If \(D_U=L_{P^T}-R_{Q^T}\), \(D_V=L_{Q^T}-R_{R^T}\), and \(D_W=R_R-L_P\) are semisimple on \(M_3\), then the nilpotent parts of \(P,Q,R\) all vanish.  Hence any full-span termwise-aligned nontransverse stratum may be studied in the semisimple eigenvalue-weight model.

## Proof sketch

Use the additive Jordan decomposition
\[
P=P_s+P_n,
\quad Q=Q_s+Q_n,
\quad R=R_s+R_n,
\]
where semisimple and nilpotent parts commute for each matrix.  The nilpotent part of
\[
L_{P^T}-R_{Q^T}
\]
is
\[
N_U=L_{P_n^T}-R_{Q_n^T}.
\]
Indeed, left and right multiplication commute, and the Jordan decomposition of a commuting sum is obtained by summing semisimple parts and nilpotent parts.

If \(D_U\) is semisimple, then its nilpotent part is zero:
\[
L_{P_n^T}=R_{Q_n^T}.
\]
Applying both sides to all matrix units gives
\[
P_n^T X=XQ_n^T\quad\text{for every }X\in M_3.
\]
Setting \(X=I\) gives \(P_n^T=Q_n^T\).  Then the equality says this common matrix commutes with every \(X\), so it is scalar.  A scalar nilpotent matrix is zero.  Hence
\[
P_n=Q_n=0.
\]
Similarly, semisimplicity of \(D_V\) gives \(Q_n=R_n=0\), and semisimplicity of \(D_W\) gives \(R_n=P_n=0\).  The first two already force all three nilpotent parts to vanish.

Therefore the nonsemisimple cases cannot support a full-span termwise-aligned decomposition.  The surviving nontransverse layer is semisimple and is governed by repeated difference eigenvalues.

## Consequence for the route

The nontransverse stratum splits into finite-style semisimple weight patterns:
\[
A_\alpha=\operatorname{span}\{E_{ab}:p_a-q_b=\alpha\},
\quad
B_\beta=\operatorname{span}\{E_{bc}:q_b-r_c=\beta\},
\quad
C_\gamma=\operatorname{span}\{E_{ac}:r_c-p_a=\gamma\}.
\]
The generic distinct-difference case has 27 one-dimensional blocks and therefore needs 27 aligned coordinate summands.  Repeated-difference flats are the only semisimple aligned cases not removed by that immediate count; analysis's pilot enumeration shows that simple block flattening bounds remove many of them but leave hard patterns with lower-bound sums 18, 21, and 22.  Those remaining flats need exact enumeration and sharper block-rank arguments.
