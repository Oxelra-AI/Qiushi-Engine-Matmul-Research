# independent-UV refinement and bounded Bläser source status

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The active characteristic-zero rank question had been separated into a full-UV-rank shortened atlas and possible lower-UV-rank strata.  The review note points out that this separation is unnecessary for ordinary tensor rank: any rank-at-most-22 decomposition of \(T_{\langle3,3,3\rangle}\) can be represented with exactly 22 terms whose \(u_i\otimes v_i\) columns are independent.  This note records the proof carefully, including field assumptions, and updates the route.

Throughout, let \(K\) be an arbitrary field and let \(U,V,W\simeq K^9\).  View a decomposition as
\[
T=\sum_{i=1}^s u_i\otimes v_i\otimes w_i
  =\sum_{i=1}^s x_i\otimes w_i,
\qquad x_i:=u_i\otimes v_i\in U\otimes V .
\]
For \(T=T_{\langle3,3,3\rangle}\), each of the three flattenings has rank 9, hence in every exact decomposition the sets \(\{u_i\}\), \(\{v_i\}\), \(\{w_i\}\) span the full corresponding 9-dimensional spaces.

## Lemma 1: minimal decompositions have independent \(UV\)-columns

Let
\[
T=\sum_{i=1}^s x_i\otimes w_i,
\quad x_i=u_i\otimes v_i,
\]
be a decomposition of minimal length among decompositions of \(T\).  Then \(x_1,\ldots,x_s\) are linearly independent in \(U\otimes V\).

**Proof.** Suppose \(\sum_i c_i x_i=0\) is a nontrivial relation and choose \(k\) with \(c_k\ne0\).  Then
\[
x_k=-\sum_{i\ne k}\frac{c_i}{c_k}x_i.
\]
Substitution gives
\[
\sum_i x_i\otimes w_i
=\sum_{i\ne k}x_i\otimes\left(w_i-\frac{c_i}{c_k}w_k\right).
\]
Thus the tensor has a decomposition with at most \(s-1\) terms, contradicting minimality.  This argument uses only division by the nonzero scalar \(c_k\), so it holds over every field.  If some new \(w_i\) is zero, the expression shortens further, strengthening the contradiction. \(\square\)

## Lemma 2: one splitting ARTIFACT raises \(UV\)-rank by one

Assume \(T=T_{\langle3,3,3\rangle}\) has a decomposition with \(s<22\) terms and independent \(UV\)-columns \(x_i=u_i\otimes v_i\).  Put
\[
S=\operatorname{span}\{x_1,
\ldots,x_s\}\subset U\otimes V.
\]
Then there is an index \(i\) and a vector \(a\in U\) such that \(a\otimes v_i\notin S\).  Replacing the \(i\)-th term by
\[
u_i\otimes v_i\otimes w_i
= (u_i-a)\otimes v_i\otimes w_i+a\otimes v_i\otimes w_i
\]
preserves the tensor, increases the number of terms from \(s\) to \(s+1\), and changes the \(UV\)-column span from \(S\) to \(S+K(a\otimes v_i)\), hence to dimension \(s+1\).  In particular, the new \(UV\)-columns are again independent.

**Proof.** Since the \(V\)-factor flattening of \(T_{333}\) has rank 9, the vectors \(v_i\) span \(V\).  If \(U\otimes v_i\subseteq S\) for every \(i\), then
\[
U\otimes V=U\otimes\operatorname{span}\{v_i\}
 \subseteq S,
\]
which is impossible because \(\dim S=s<22<81=\dim(U\otimes V)\).  Therefore some \(i\) has \(U\otimes v_i\not\subseteq S\), and we choose \(a\) with \(a\otimes v_i\notin S\).  Such an \(a\) exists over any field because \(\{a\in U:a\otimes v_i\in S\}\) is a proper linear subspace of \(U\).

The replacement identity is tautological.  Let \(y=a\otimes v_i\).  The new \(UV\)-columns span
\[
\operatorname{span}\{x_j:j\ne i\} + K(x_i-y)+Ky
 = S+Ky.
\]
Since \(y\notin S\), this has dimension \(s+1\).  The new expression has exactly \(s+1\) terms because \(a\ne0\), \(v_i\ne0\), \(w_i\ne0\), and \(u_i-a\ne0\): if \(u_i=a\), then \(a\otimes v_i=x_i\in S\), contrary to the choice of \(a\).  Thus the number of columns equals the span dimension, so they are independent.  The factor spans remain full: the original \(u_i\) is the sum of the two new \(U\)-factors, and the \(V,W\) factors are retained. \(\square\)

## Proposition: every rank-\(\le22\) algorithm has an independent 22-term \(UV\) presentation

If \(R_K(T_{\langle3,3,3\rangle})\le22\), then there exists a 22-term decomposition
\[
T_{333}=\sum_{i=1}^{22}u_i\otimes v_i\otimes w_i
\]
for which the 22 columns \(u_i\otimes v_i\in K^9\otimes K^9\) are linearly independent.

**Proof.** Start with any decomposition of length at most 22 and shorten it until its length is minimal for \(T_{333}\).  Lemma 1 gives independent \(UV\)-columns.  If the minimal length is already 22, stop.  If its length is \(s<22\), apply Lemma 2 repeatedly.  Each ARTIFACT preserves the tensor and full factor spans while raising both the term count and \(UV\)-column rank by one.  After \(22-s\) steps one obtains exactly 22 terms with \(UV\)-column rank 22. \(\square\)

## Consequence for the global route

The lower-\(UV\)-rank branch is not an independent global branch for ordinary rank.  A rank-21 or lower algorithm, if it exists, can be split into a rank-22 presentation inside the full-\(UV\)-rank open set.  Therefore:

1. To prove \(R_K(T_{333})\ge23\), it is enough to exclude the independent-\(UV\) 22-term incidence.
2. The shortened atlas with a nonzero \(22\times22\) minor of \(X=[u_i\otimes v_i]\) is globally relevant, not merely the transverse part of rank-exact-22 presentations.
3. The projected-kernel formulation must be saturated by full \(X\)-rank (or use left-inverse variables \(YX=I_{22}\)); once this is enforced, \(\operatorname{rank}(QX)\le13\) is equivalent to \(L=\operatorname{im}(T_{UV|W})\subseteq\operatorname{span}X\).
4. The previous phrase “lower-UV-rank strata” should be retired for the ordinary rank question.  Singular nonminimal 22-term presentations may exist, but they do not need separate exclusion: any rank-at-most-22 tensor rank witness also has a full-UV-rank 22-term witness.

This refinement holds over every field.  Characteristic zero is still needed for the stabilizer/Jordan/aligned-stratum analysis as currently written, and the Bläser block input must be used over a field where its theorem holds.

## Bounded Bläser source status

The nontransverse semisimple aligned-stratum exclusion remains dependent on
\[
R(M_{\langle3,3,2\rangle})\ge14.
\]
Current source state:

- The local Landsberg source `Knowledge/objects/papers/New-lower-bounds-for-the-rank-of-matrix-multiplication--fe4c79cff1ba--b50c936262b4/object.md` states at lines 33--37 that Bläser's previous bound is
  \[
  R(M_{\langle n,n,m\rangle})\ge 2nm-m+2n-2,
  \]
  which gives 14 at \((n,m)=(3,2)\).  Landsberg's paper itself works over \(\mathbb C\), sufficient for a characteristic-zero algebraic-geometric nontransverse exclusion after base extension, but it is still a secondary citation.

- Wang's finite-field lower-bound paper `Knowledge/objects/papers/Automated-Lower-Bounds-for-Small-Matrix-Multiplication-Complexity-over-F--d7e0d98ca98f--3c257f9fb1dd/object.md` records Bläser's 2003 small-format paper as an arbitrary-field source for a related rectangular family, and cites the same Journal of Complexity paper at lines 48--54 and 444--448.  This confirms that the 2003 paper is the correct primary reference, but the exact \(M_{\langle3,3,2\rangle}\) formula still rests locally on Landsberg's line 37.

- A focused `knowledge_request` for the primary DOI `10.1016/S0885-064X(02)00007-9` returned no usable primary object (`independent-verification-record`).

- analysis computed all exterior/Koszul flattenings for \(M_{\langle3,3,2\rangle}\); the best self-contained bound is only 11, so the gap to 14 is genuinely substitution-method content rather than a missing flattening calculation.

Practical status: for continuing the main research over characteristic zero, it is reasonable to use the Bläser input as a well-cited theorem with Landsberg's explicit formula, while marking the nontransverse exclusion as relying on that theorem until the primary paper or a self-contained substitution proof is obtained.  More effort to retrieve the primary source should be bounded; the route-changing mathematical refinement above is more important because it collapses the global incidence to independent \(UV\) columns.
