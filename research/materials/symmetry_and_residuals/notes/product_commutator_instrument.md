# product-form commutator instrument for cyclic `(10,4)`

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Protective correction inherited from analysis

The analysis Jennrich minor is a valid certificate for the **fixed BILR residual cubic**, not a universal exclusion of the pure-cyclic `(10,4)` branch.  A rank-4 exterior decomposition
\[
\sum_{j=1}^4 u_j\wedge v_j\wedge w_j=\omega
\]
does not determine the symmetric cubic \(\sum_j u_jv_jw_j\): each plane admits determinant-one changes of frame that preserve the wedge but change the symmetric product.  Thus BILR nonvanishing is not evidence against a special rank-22 point.  If a traceless `(10,4)` cyclic rank-22 algorithm exists, its residual must lie in the closed locus where the Hessian commutator has rank at most two for every pair \((X,Y)\).  That locus is also a candidate-finding locus, not something that can be discarded as nongeneric.

I patched the theorem ledger ([structured_theorems_ledger_.md](../../quotient_cores/notes/structured_theorems_ledger_.md)) and the analysis integer certificate conclusion ([jennrich_integer_certificate.json](../results/hessian_commutator/jennrich_integer_certificate.json)) to reflect this scope.  The old synthesis [jennrich_and_10_4_exclusion.md](jennrich_and_10_4_exclusion.md) now begins with a warning that its universal `(10,4)` conclusion is superseded.

## Closed product formula for the Hessian endomorphism

Use the trace pairing
\[
\ell_A(X)=\operatorname{tr}(AX).
\]
For a traceless free-orbit residual
\[
R(X)=\operatorname{tr}(X^3)-3\sum_{j=1}^4 \ell_{u_j}(X)\ell_{v_j}(X)\ell_{w_j}(X),
\]
with \(u_j,v_j,w_j\in\mathfrak{sl}_3\), define
\[
H_X=(1/6)\operatorname{Hess}_R(X)K^{-1},\qquad K(Y,Z)=\operatorname{tr}(YZ).
\]
Tracelessness gives \(H_I=\mathrm{Id}\), so the trace form is intrinsic to the residual at the identity.  Polarizing gives the exact product formula
\[
H_X(Y)=\frac{XY+YX}{2}
-\frac12\sum_j\Big((v_j(X)w_j(Y)+w_j(X)v_j(Y))u_j
+(u_j(X)w_j(Y)+w_j(X)u_j(Y))v_j
+(u_j(X)v_j(Y)+v_j(X)u_j(Y))w_j\Big).
\]
Inside a free plane, the correction is the hollow symmetric block
\[
-\frac12\begin{pmatrix}0&x_3&x_2\\x_3&0&x_1\\x_2&x_1&0\end{pmatrix}
\]
in the coordinates \(x=(u_j(X),v_j(X),w_j(X))\).  The leading term satisfies
\[
[H^0_X,H^0_Y]=\frac14\operatorname{ad}([X,Y])
\]
for the Jordan product \(H^0_X(Y)=(XY+YX)/2\).  In the integer-scaled code variable `H2=2H`, the leading commutator is exactly \(\operatorname{ad}([X,Y])\).

The script [product_commutator_bilr.py](../code/product_commutator_bilr.py) implements this formula directly, without expanding or differentiating a cubic polynomial.

## Exact BILR checks

Output: [bilr_product_commutator_invariants.json](../results/product_commutator/bilr_product_commutator_invariants.json).

Main exact checks:

- Stored BILR free representatives must be transposed into the trace-pairing convention: stored files use \(\ell_L(X)=\operatorname{tr}(L^T X)\), while this note uses \(\ell_A(X)=\operatorname{tr}(AX)\).  With transposition, the product formula matches the 11-cube residual Hessian on all tested directions with zero mismatches; without transposition there are 90 mismatched entries and max mismatch 20.
- For the fixed BILR residual, the commutator at the analysis directions has rank 4 over \(\mathbb Q\).  In the column convention and scaling `H2=2H`, the first nonzero \(3\times3\) minor at rows `(1,2,3)` and columns `(1,2,6)` has determinant `-12800`.  This differs from the analysis `27993600` determinant only because the earlier certificate used a different Hessian scaling/convention; the rank obstruction is the same.
- The cheap scalar rank-\(\le2\) identities for this same commutator give `tr(C^3)=0` but
  \[
  2\operatorname{tr}(C^4)-\operatorname{tr}(C^2)^2=-20480000\ne0,
  \]
  so the quartic trace identity alone certifies rank \(>2\) for this pair.
- The full BILR commutator image space
  \[
  L=\operatorname{span}\{[H_X,H_Y]:X,Y\in\mathfrak{gl}_3\}
  \]
  has `span_dim=4`, `common_image_dim=4`, `common_kernel_dim=5`; basis commutators have rank histogram `0:18, 2:18`, but random linear combinations have rank histogram `4:185, 2:15` over 200 trials.  Thus the space itself contains rank-4 operators even though each basis-pair commutator is only rank 0 or 2.
- For the calibration residual \(R=\operatorname{tr}(X^3)\) with no free corrections, the commutator space is the adjoint image: `span_dim=8`, `common_image_dim=8`, `common_kernel_dim=1`, random combinations always had rank 6.  This matches the regular-adjoint picture.

These checks strengthen the BILR residual Waring-rank-11 proof, but they do not prove anything about other frames except through the exact identities they motivate.

## Bounded-rank matrix-space literature check

The relevant classification input is real and useful but must be stated carefully.

- Atkinson's `Primitive spaces of matrices of bounded rank. II` assumes the field has more elements than the maximum rank and recalls the Atkinson--Lloyd reduction: every bounded-rank matrix space is equivalent to a compression part plus a primitive core; for rank at most 2, the primitive core is the space of \(3\times3\) skew-symmetric matrices.  The paper states this explicitly in Section 4 after Theorems A and B.  Citation key from the Knowledge request: `\cite{atkinson1983primitive}`.
- Huang--Landsberg's bounded-rank review/classification states that compression spaces are the block spaces with zero lower-right corner, and records that Atkinson--Lloyd classified rank 2, with the only primitive rank-2 space being the \(3\times3\) skew-symmetric example (Knowledge lines 29--40).  It also summarizes the compression/primitivity reduction (lines 288--295).  Citation key: `\cite{huang2023linear}`.
- Pazzis's classification of large bounded-rank subspaces gives image/kernel compression conclusions for large dimensions, but its large-dimension threshold is not enough for our small commutator spaces.  Citation key: `\cite{pazzis2010classification}`.

For rank \(\le2\), the complete alternatives include the compression types \(R(2,0),R(1,1),R(0,2)\) and the primitive skew \(3\times3\) model.  The simple data fields `common_image_dim<=2`, `common_kernel_dim>=7`, and `span_dim<=3` are useful summaries, but they do **not** implement the full \(R(1,1)\) compression alternative.  For actual exclusions one can either impose all \(3\times3\) minors of the linear space \(L\), or split by the full bounded-rank alternatives.

A separate literature check on \(\operatorname{tr}(X^3)\) found Chiantini--Hauenstein--Ikenmeyer--Landsberg--Ottaviani, `\cite{chiantini2017polynomials}`: for \(sM_{\langle3\rangle}=\operatorname{tr}(A^3)\) on \(\operatorname{Mat}_3\), Proposition 2.6 gives symmetric border rank at least 14 using a Koszul--Young flattening of rank 950, Theorem* 2.7 reports a numerical 18-summand decomposition, and Conjecture 2.8 predicts Waring rank 18.  This calibrates the no-free-orbit cubic as much harder than a ten-cube residual, but it does not solve the BILR residual or cyclic `(10,4)` problem.

## Internal frame probes over finite fields

Script: [internal_frame_scan.py](../../quotient_cores/code/internal_frame_scan.py).
Output: [internal_frame_scan_f31.json](../results/product_commutator/internal_frame_scan_f31.json).

This exact \(\mathbb F_{31}\) pilot changes determinant-one frames independently inside the four BILR exterior planes, preserving the exterior trivectors while changing the symmetric residual.

Results:

- Base BILR over \(\mathbb F_{31}\): `span_dim=4`, `common_image_dim=4`, `common_kernel_dim=5`, and random linear combinations reach rank 4; the fixed scalar filters fail.
- 300 random internal `SL3(F31)` frame choices: no sample passed either the bounded-rank behavior expected from a rank-\(\le2\) commutator space or the fixed scalar filters.  The commutator spaces typically enlarged dramatically: `span_dim=28` in 291 samples and `27` in 9 samples; `common_image_dim=8`, `common_kernel_dim=1`, and random combinations reached rank 8 in all 300 samples.
- Elementary one-parameter slices and diagonal two-parameter slices in one plane never showed upper-rank-2 behavior; in every scanned slice a rank-4 combination was seen.  Four elementary values did pass the five fixed scalar-pair identities, but still had rank-4 commutators and failed the full-space behavior.

The last point was checked exactly over \(\mathbb Q\) in [elementary_exception_exact.py](../../quotient_cores/code/elementary_exception_exact.py), output [elementary_scalar_exception_exact.json](../results/product_commutator/elementary_scalar_exception_exact.json).  For the unipotent frame
\[
\begin{pmatrix}1&0&0\\0&1&0\\1&0&1\end{pmatrix}
\]
applied to any one BILR plane, the five selected scalar identities all vanish over \(\mathbb Q\), yet the commutator space has `span_dim=5`, `common_image_dim=5`, `common_kernel_dim=4`, and random pairs exhibit rank-4 commutators.  This is a useful warning: finitely many trace identities can miss the rank-\(>2\) locus unless they are imposed as polynomial identities in all \((X,Y)\), or replaced by a full matrix-space classification argument.

## Current scientific meaning

The new product instrument changes the cyclic `(10,4)` problem from large cubic expansion into a small algebraic question about a linear space of \(9\times9\) commutators.  For any traceless `(10,4)` candidate, the residual must satisfy
\[
\operatorname{rank}[H_X,H_Y]\le2\quad\text{for all }X,Y.
\]
Equivalently, all elements of the linear space \(L=\operatorname{im}(\Lambda^2\mathfrak{gl}_3\to\operatorname{End}(\mathfrak{gl}_3))\) have rank at most two.  Bounded-rank matrix-space theory then forces strong compression or a small primitive skew model.  The BILR point is far from that locus; random internal frame changes move even farther away.  None of this excludes special frames, and those special frames are exactly where a rank-22 cyclic algorithm could live.

The next useful work is to turn this into an exact algebraic split:

1. Derive symbolic equations for the full upper-rank-2 condition on \(L\), preferably using the bounded-rank alternatives rather than all minors.
2. Include the full \(R(1,1)\) compression alternative: existence of a line \(E\subset\mathfrak{gl}_3\) and a hyperplane \(D\subset\mathfrak{gl}_3\) with \(C(D)\subset E\) for every \(C\in L\).  The simple common-image/common-kernel summaries do not cover this case.
3. If an alternative is feasible, solve the resulting smaller system for internal frames; any solution is a candidate residual and should then be tested for a ten-cube Waring decomposition and finally against all 729 Brent identities.
4. If all alternatives are empty under the exterior equation, then the traceless `(10,4)` cyclic branch closes without needing a component classification of rank-4 exterior decompositions.
