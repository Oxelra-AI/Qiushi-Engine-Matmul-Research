# canonical `Z4` Q-basis and tail-scaling correction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

This note records the corrected convention and the new structural finding needed before any characteristic-zero `Z4` block solve can be trusted. It is a research-facing proof/verification note, not a final publication-ready result.

The active structured problem is the single-free-orbit `Z4` residual family from earlier analysis. For an internal recombination matrix `M in SL3`, the residual cubic is
\[
C_M(X)=\operatorname{tr}(X^3)-3\sum_{k=0}^3
\ell_{g^kA_M}(X)\ell_{g^kB_M}(X)\ell_{g^kC_M}(X),
\]
where the displayed factors are stored in the old packed convention `ell_L(X)=tr(L^T X)`.

## One convention rule

Use exactly this rule for the `Z4` block instrument:

1. Convert a stored packed form `L` to a trace-pairing coefficient matrix
   \[
   A=L^T,
   \qquad \ell_L(M)=\operatorname{tr}(L^TM)=\operatorname{tr}(AM).
   \]
2. Choose `Q` diagonalizing the matrix that acts on form coefficients:
   \[
   Q^{-1}a_0^TQ=D=\operatorname{diag}(-1,i,-i),
   \qquad
   Q=\begin{pmatrix}1&1&1\\-1&i&-i\\1&-1&-1\end{pmatrix}.
   \]
3. Use the same basis on both coefficient and variable matrices:
   \[
   A''=Q^{-1}AQ,
   \qquad
   M''=Q^{-1}MQ.
   \]
   The basis change gives
   \[
   \operatorname{tr}(AM)=\operatorname{tr}(A''M'').
   \]
   Separately, the equivariant relation is
   \[
   \ell_{DA''D^{-1}}(M'')=\ell_{A''}(D^{-1}M''D),
   \]
   so the coefficient action is `A'' -> D A'' D^{-1}` and the precomposed variable action is `M'' -> D^{-1}M''D`. These are not meant as a simultaneous transformation preserving the trace pairing term-by-term.
4. If `n_ab=M''_{ab}` and `mu=(-1,i,-i)`, then the coordinate weight is `mu_b/mu_a`. In the coordinate order used in analysis,
   \[
   p=(n_{11},n_{22},n_{33}),\quad
   q=(n_{23},n_{32}),\quad
   z=(n_{21},n_{13}),\quad
   w=(n_{12},n_{31}).
   \]

No mixed `P/Q` basis should be used. The earlier `P` basis diagonalized `a0`, not `a0^T`, and caused the form-level size-four contributions to have artificial rank two.

## Self-tests that must pass

The canonical-basis target identity is
\[
\begin{aligned}
\operatorname{tr}(X^3)=&\ n_{11}^3+n_{22}^3+n_{33}^3
+3(n_{22}+n_{33})n_{23}n_{32}\\
&+3(n_{11}+n_{22})n_{12}n_{21}
+3(n_{11}+n_{33})n_{13}n_{31}\\
&+3n_{32}n_{21}n_{13}+3n_{23}n_{12}n_{31}.
\end{aligned}
\]
Thus the target `qz^2` and `qw^2` blocks are rank one, their binary quadrics are hyperbolic rather than squares, and their `q` directions are different.

The script [z4_qbasis_selftest.py](../code/z4_qbasis_selftest.py) implements these tests over the good split prime `65521`. Its output is [qbasis_selftest.json](../results/z4_qbasis/qbasis_selftest.json). The checked facts are:

- `Q^{-1}a0^TQ=diag(-1,i,-i)`.
- The short block formula for `tr(X^3)` agrees with the direct coordinate expansion.
- Target `qz^2` rank is `1`, active on the `n32` row, with block `[[0,0,0],[0,3,0]]`.
- Target `qw^2` rank is `1`, active on the `n23` row, with block `[[0,3,0],[0,0,0]]`.
- Both active binary quadrics have nonzero discriminant; they are not squares.
- Random pairing tests have zero mismatches.
- The BILR residual is exactly the sum of the eleven BILR cubes in this basis, with cube-orbit lengths `1,2,4,4` and supports `p`, `p+q`, general, general.

These tests fix the coordinate convention; they do not prove or disprove rank 22.

## Off-block extraction and the hidden tail scaling

For a size-four `Z4` cube orbit represented by
\[
\ell=p+q+z+w,
\]
the orbit contribution has the block form
\[
qz^2=12\,q\,z^2,
\qquad
qw^2=12\,q\,w^2,
\qquad
pzw=24\,p\,z\,w,
\]
and tail
\[
p^3+pq^2=4p^3+12p q^2.
\]
For two size-four orbits, the generic branch solves
\[
C_{qz^2}=12(q_1z_1^2+q_2z_2^2),\quad
C_{qw^2}=12(q_1w_1^2+q_2w_2^2),\quad
C_{pzw}=24(p_1z_1w_1+p_2z_2w_2).
\]

The important correction is that these off blocks determine each orbit only up to the rescaling
\[
z\mapsto t z,
\qquad
w\mapsto \varepsilon t w,
\qquad
q\mapsto t^{-2}q,
\qquad
p\mapsto \varepsilon t^{-2}p,
\qquad \varepsilon^2=1.
\]
The off blocks are unchanged, while the tail contribution is multiplied by
\[
h=\varepsilon t^{-6}.
\]
Thus a sign change of the `w` block must be accompanied by the corresponding sign on the `p` component; changing `w` alone is not a symmetry of the off blocks. Any tail test must include independent nonzero scalars `h1,h2` for the two recovered size-four orbits. Subtracting the unscaled recovered forms can falsely reject the BILR positive control and could falsely prove emptiness.

The symbolic script [z4_symbolic_orbit_formula.py](../code/z4_symbolic_orbit_formula.py) proves the length-four formula, the length-two formula, and the hidden scaling identity modulo `eps^2=1`, with output [symbolic_orbit_formula.json](../results/z4_qbasis/symbolic_orbit_formula.json). The script [z4_tail_positive_control.py](../code/z4_tail_positive_control.py) verifies this on the BILR residual. Its output [tail_positive_control_bilr_v2.json](../results/z4_qbasis/tail_positive_control_bilr_v2.json) records:

- all `32` order/sign generic variants match the off blocks;
- all `32` recover the known BILR `4+4+2+1` tail after solving the two tail scalars `h1,h2`;
- the `4+4+1+1` rank-22 necessary condition that the `pq^2` tail vanish after subtracting the two scaled size-four tails has no solution at the BILR residual.

A further fixed-residual check, [z4_bilr_tail442_groebner.py](../code/z4_bilr_tail442_groebner.py), tests the full `4+4+2` tail equations over `F_65521` for the BILR residual in the generic off-block variants. It imposes the length-two orbit constants
\[
(P+Q)^3+(P-Q)^3=2P^3+6PQ^2,
\]
with the same `P,Q` in both `p^3` and `pq^2` components. Output [bilr_tail442_groebner.json](../results/z4_qbasis/bilr_tail442_groebner.json) reports both affine charts `q0=1` and `q1=1` empty for all `32` generic variants. This agrees with analysis's stronger Koszul--Young proof that the fixed BILR residual needs 11 cubes. It is still a fixed-residual control, not a proof for the six-parameter residual family.

The sample scale solution is `h=[65457,65457]` modulo `65521`; other sign variants produce `64` and `65457`, matching the projective hidden-scale ratios to the actual BILR size-four orbits.

## Branch taxonomy for the next algebraic solve

Conciseness requires independent `z` parts and independent `w` parts for the two size-four orbits, but it does not force independent `q` parts. The `qz^2` and `qw^2` blocks must therefore be treated branchwise:

1. **Generic branch:** `q1,q2` independent. The rowspace of `C_{qz^2}` is a pencil meeting the Veronese conic in two square points; likewise for `C_{qw^2}`. Extraction is finite up to order, sign, and the two hidden tail scalars `h1,h2`.
2. **Proportional-q branch:** `q2` proportional to `q1`, both nonzero. The block has rank one and the binary quadric only needs to split as a sum of two squares; this leaves a one-parameter family and cannot be discarded by a generic conic extractor.
3. **Zero-q branch:** one of the two `q` parts is zero. The corresponding rank-one rowspace is a perfect square branch.

The same taxonomy applies independently to the `w` extraction, with shared `q` coupling. A proof or exact solver that assumes only the generic rank-two branch is incomplete.

## Current mathematical status

The Q-basis and hidden-tail correction are now reliable instruments for the `Z4` component, but they do not yet give a characteristic-zero rank-22 candidate or emptiness theorem. The next mathematical work is to write and solve the branch-aware algebraic systems over `Z[i]` or good split primes with exact reconstruction:

- generic branch equations with variables from the six-parameter internal `SL3/T` residual family and hidden tail scalars `h1,h2`;
- proportional-`q` and zero-`q` branches, because they can survive `qz^2/qw^2` rank-one tests;
- tail conditions for `4+4+1+1`: `pq^2` vanishes after scaled subtraction, then the `p^3` remainder is a sum of two p-cubes;
- tail conditions for `4+4+2`: the `pq^2` remainder is a single `p q^2` orbit and the `p^3` remainder is the matching `2p^3` (up to the correct orbit constants).

Any extracted candidate must be converted back to a full 22-term bilinear scheme and checked on all 729 Brent equations. A diagonal cubic/block identity alone is not a full bilinear verification: cyclic antisymmetric terms can vanish on the diagonal. Any nonexistence result must state its symmetry, field, and branch coverage precisely.
