# route update: one global independent-UV incidence

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical reduction now in force

The analysis refinement lemma, checked by review, shows that for any field \(K\):

\[
R_K(T_{333})\le 22
\quad\Longrightarrow\quad
\exists\; T_{333}=\sum_{i=1}^{22}u_i\otimes v_i\otimes w_i
\text{ with } X=[u_i\otimes v_i]_{i=1}^{22}\text{ of rank }22.
\]

The proof is in [independent_uv_refinement_and_blaser_status.md](../notes/independent_uv_refinement_and_blaser_status.md); review verification is at `independent-verification-record`.  The previous “lower-UV-rank branch” is therefore not a separate global branch for ordinary rank.  If a shorter algorithm exists, it can be split into a 22-term full-\(X\)-rank witness.  This does **not** imply every witness is transverse or smooth; split shorter algorithms may sit in singular subloci of the full-\(X\)-rank incidence.  But excluding all full-\(X\)-rank 22-term witnesses is enough for \(R_K(T_{333})\ge23\).

## Remaining characteristic-zero target

The remaining lower-bound target is the full-\(X\)-rank incidence:

- \(U,V,W\simeq K^9\), \(E=U\otimes V\);
- \(L=\operatorname{im}(T_{UV|W})\subset E\), \(\dim L=9\);
- find or exclude a 22-dimensional subspace \(S\subset E\) with
  1. \(L\subset S\),
  2. \(S\) has a basis \(x_i=u_i\otimes v_i\) of 22 rank-one matrices,
  3. the induced \(W\)-coefficients recover all 729 Brent identities.

Equivalently, with a quotient \(Q:E\to E/L\), for full-rank \(X\):
\[
L\subseteq\operatorname{im}X
\iff
\operatorname{rank}(QX)=13.
\]
The full \(X\)-rank open condition is essential; analysis found fake projected-kernel roots with \(\operatorname{rank}X=19\), \(\operatorname{rank}(QX)=13\), capturing only six of the nine directions in \(L\).

## Exact chart A: saturated projected-kernel graph

Pick 13 projected pivot columns \(P\) and 9 remaining columns \(R\).  Variables are 22 pairs \((u_i,v_i)\) and \(C\in K^{13\times9}\).  Equations:
\[
QX_R=QX_PC.
\]
Open conditions:

- a selected \(13\times13\) minor \(\delta(QX_P)\ne0\);
- a selected \(22\times22\) minor \(\Delta_X\ne0\), or a stronger intrinsic replacement below.

A cleaner saturation uses
\[
H(C)=\binom{-C}{I_9},\qquad QXH=0,
\]
so \(XH\in L\).  Express \(XH=\iota D\), \(D\in K^{9\times9}\).  If \(\delta(QX_P)\ne0\) and \(\det D\ne0\), then \(X\) is automatically full column rank and \(L\subseteq\operatorname{im}X\).  Algebraic proof: if \(Xa=0\), then \(a=Hb\); then \(0=XHb=\iota Db\), so \(b=0\), hence \(a=0\).  Thus a practical system can use inverse variables for \(\delta\) and \(D\) (e.g. \(DG=I_9\)) instead of enumerating all \(22\times22\) minors.

This chart is good for:

- modular root search under exact open conditions;
- F4/Gröbner experiments on fixed term-normalization charts;
- Nullstellensatz-style exclusion of a specified chart if feasible.

It must cover pivot choices, not just one QR-selected chart.

## Exact chart B: 13+9 completion through an invertible W-block

Select 9 terms whose \(w_i\) coefficients form an invertible \(9\times9\) block.  Since the \(w_i\) span \(W\), such a block exists in any exact decomposition.  After reordering terms write:
\[
T=X_PA+X_RB,
\qquad |P|=13,
\quad |R|=9,
\quad B\in GL_9.
\]
Set \(D=B^{-1}\) and \(C=AB^{-1}\).  Then
\[
X_R=T D-X_PC.
\]
Variables:

- thirteen free rank-one columns \(X_P=u_i\otimes v_i\);
- \(C\in K^{13\times9}\);
- \(D\in GL_9\) with inverse variable or determinant inverse;
- nine derived columns \(Y_j=(TD-X_PC)_j\), each constrained to be rank one in \(U\otimes V\).

This model is attractive because roots directly recover \(X_R\) and \(W\); it does not admit the analysis low-\(X\)-rank projected pseudo-root if \(D\) is invertible and the derived columns are rank one.  It may be encoded either by:

1. factor variables for the nine derived columns, \(Y_j=a_j\otimes b_j\), or
2. all \(2\times2\) minors of each \(9\times9\) reshaped derived column.

The next review should implement this chart over finite fields first, calibrate on random rank-22 tensors (positive controls), and test whether cn122 one-term deletions fail for the expected reason.  Then try small symmetry ansätze or modular search; absence of roots over sampled primes is not a characteristic-zero proof.

## Structural lower-bound ideas worth developing

### 1. Schur-product inverse theorem

Represent the 22 terms coordinatewise in \(K^{22}\):
\[
p_{ab}=((u_i)_{ab})_i,
\quad q_{bc}=((v_i)_{bc})_i.
\]
If \(H\subset K^{22}\) is the 9-dimensional \(w\)-coefficient space and \(K_0=H^\perp\), the Brent equations say cross products and diagonal differences land in \(K_0\), while the nine diagonal classes span the output quotient.  A possible theorem is that such a 13-dimensional annihilator \(K_0\) with full nondegeneracy must have a non-scalar diagonal stabilizer
\[
\{z\in K^{22}:z\circ K_0\subseteq K_0\}.
\]
If true, the remaining incidence collapses into the already treated termwise-aligned/nontransverse branch.  This is currently only a promising mechanism, not a theorem.  A computation should either find counterexamples to the inverse statement or produce elimination evidence after saturating nondegeneracy and scalar-stabilizer conditions.

### 2. Rank-spectrum/compound-minor constraints from \(L\simeq\{F\otimes I_3\}\)

Every nonzero element of \(L\) has matrix rank 3, 6, or 9.  A 22-rank-one basis containing \(L\) implies a diagonal-rank representation of the family \(F\otimes I_3\):
\[
F\otimes I_3=U_0\operatorname{diag}(h_1(F),\ldots,h_{22}(F))V_0^T.
\]
All \(7\times7\) minors must be divisible by \(\det F\), all \(8\times8\) minors by \((\det F)^2\), and the determinant by \((\det F)^3\).  The Plücker coordinates of the left/right rank-one bases are coupled.  This targets the special rank jump of the matrix-multiplication subspace and is more relevant than generic flattenings.

### 3. Finite moving frames and symmetry ansätze

Global chart work must use finite open covers: projective term normalizations, stabilizer frames built from invertible linear combinations of \(u_i,v_i\), and cyclic/companion-form conditions.  Local coordinate slices from Jacobian pilots do not prove global coverage.  A finite group ansatz such as \(C_3\) or transpose-permuting 22 terms is worth trying as a constructive/exclusion subproblem, but any negative result remains ansatz-specific.

## Bläser dependency status

The nontransverse aligned-stratum exclusion remains a valuable module.  It is complete modulo the small-format theorem
\[
R(M_{\langle3,3,2\rangle})\ge14.
\]
Current evidence:

- Landsberg line 37 explicitly cites Bläser's formula \(2nm-m+2n-2\).
- The DOI `10.1016/S0885-064X(02)00007-9` resolves to Elsevier.
- Wang/Yang's finite-field lower-bound paper records Bläser 2003 as an arbitrary-field small-format lower-bound source.
- analysis self-contained exterior/Koszul bounds reach only 11.

Further retrieval/proof reconstruction should be bounded.  The main attack should now concentrate on the single global independent-UV incidence, while keeping the nontransverse exclusion marked as relying on Bläser's theorem until primary proof text or a self-contained substitution proof is obtained.
