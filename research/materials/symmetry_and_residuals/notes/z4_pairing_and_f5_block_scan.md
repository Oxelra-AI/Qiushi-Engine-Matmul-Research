# corrected `Z₄` pairing action and finite-field block solve

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Correct action for the residual cubic

For the BILR residual cubic
\[
C(M)=\sum_{i=1}^{11}\langle L_i,M\rangle^3,
\qquad \langle L,M\rangle=\operatorname{tr}(L^T M),
\]
the coefficient cube set is permuted by
\[
L\mapsto a_0La_0^{-1}.
\]
With the packed Euclidean pairing this is dual to the variable action
\[
M\mapsto a_0^T M a_0^{-T},
\]
since
\[
\operatorname{tr}((a_0La_0^{-1})^TM)
=\operatorname{tr}(L^Ta_0^TMa_0^{-T}).
\]
The analysis non-invariance was therefore caused by testing the wrong conjugation on variables.

[z4_pairing_pencil.py](../code/z4_pairing_pencil.py) performs a coefficientwise brute-force comparison over `F_65521`:

| variable action | residual coefficient differences | `tr(X^3)` differences | cube set permuted |
|---|---:|---:|---|
| `M -> a0 M a0^{-1}` | 55 | 0 | no |
| `M -> a0^{-1} M a0` | 55 | 0 | no |
| `M -> a0^T M a0^{-T}` | 0 | 0 | yes |
| `M -> a0^{-T} M a0^T` | 0 | 0 | yes |

The chosen action has `R^T` equal to the coefficient action `L -> a0 L a0^{-1}`. The old- and new-coordinate anchors both satisfy
\[
\operatorname{tr}(X^3)-3\sum_{k=0}^3 A_kB_kC_k-\sum_{i=1}^{11}L_i^3=0
\]
coefficientwise.

The incorrect analysis note was patched so later steps do not inherit the false non-invariance statement.

## Eigenblock positive control

For `rho(M)=a0^T M a0^{-T}`, the eigenspace dimensions over `F_65521` are
\[
3,2,2,2
\]
with weights `p,q,z,w` equal to `0,2,1,3 mod 4`. Cubic invariants split exactly as
\[
p^3(10)\oplus pq^2(9)\oplus pzw(12)\oplus qz^2(6)\oplus qw^2(6),
\]
with no other invariant monomials. The BILR residual has zero coefficients outside these five blocks, and invariant projection changes zero coefficients.

The `qz²` and `qw²` blocks both have rank `2`. Their row spaces meet the binary-square conic in exactly two projective points. These points match the two known size-four BILR cube orbits:

- orbit `[3,4,5,6]` matches square line `[1,-2,1]` in both `z` and `w`;
- orbit `[7,8,9,10]` matches the second `z` and `w` square lines, up to the recorded projective factors.

This validates the block coordinates, the `12` and `24` orbit-sum normalizations, and the pencil-conic extraction of the size-four orbit square lines. It is still only a positive control for the instrument, not a rank-22 algorithm and not a lower-bound theorem.

Canonical files:

- script: [z4_pairing_pencil.py](../code/z4_pairing_pencil.py)
- data: [pairing_pencil_positive_control.json](../results/z4_pairing_pencil/pairing_pencil_positive_control.json)

## Exact `F_5` scan of the single-free-`Z₄` residual model

Using the corrected action, I scanned the internal `SL₃` residual family over `F_5` modulo the right diagonal recombination torus. The group count is
\[
|SL_3(F_5)|=372000,
\qquad |T|=16,
\qquad |SL_3(F_5)/T|=23250,
\]
and the scan enumerated all `23250` representatives.

The first generic scan (`z4_f5_sl3_quotient_scan.py`) used the pencil-conic rowspace path and found no rank-10 residual matches for the two concise `Z₄`-stable patterns `4+4+2` and `4+4+1+1`. Because that path assumes recoverable rank-two block structure and can drop branches when a linear solve has too many solutions, it was superseded by the robust scan.

The robust scan (`z4_f5_robust_rank10_scan.py`) precomputes all finite-field blocks for
\[
q_1,q_2,z_1,z_2,w_1,w_2\in F_5^2,
\]
solves every `pzw` linear system, and tests the two tail types:

- one length-two orbit in `p\oplus q` for `4+4+2`;
- two fixed `p`-space cubes for `4+4+1+1`.

It includes rank-deficient `qz²` and `qw²` branches. Result:

- representatives tested: `23250`;
- generic rank-two `qz/qw`: `17226`;
- rank-deficient `qz/qw`: `6024`;
- rank-10 hits: `0`.

The corresponding finite-field statement is:

> In the corrected single-free-`Z₄` residual model over `F_5`, for every `M in SL_3(F_5)` modulo right diagonal recombination, there is no `F_5`-rational `Z₄`-stable ten-cube residual decomposition of pattern `4+4+2` or `4+4+1+1`.

This finite computation does not exclude decompositions over extensions of `F_5`, does not by itself imply a characteristic-zero theorem, and does not address non-`Z₄`-stable decompositions or other exterior skeletons.

Canonical files:

- script: [z4_f5_robust_rank10_scan.py](../code/z4_f5_robust_rank10_scan.py)
- result: [f5_sl3_modT_robust_rank10_scan.json](../results/z4_block_scan/f5_sl3_modT_robust_rank10_scan.json)

## Conciseness over `F_5`

[z4_f5_conciseness_scan.py](../code/z4_f5_conciseness_scan.py) computed the first catalecticant rank for all `23250` residual representatives. Every representative has rank `9`. Therefore, within this finite-field model, every residual is concise in nine variables. A `Z₄`-stable ten-cube decomposition with fewer than two length-four cube orbits would span at most seven variables (`p\oplus q` plus one `z` line and one `w` line), so the only concise ten-cube orbit patterns are exactly
\[
4+4+2,
\qquad 4+4+1+1.
\]

File: [f5_sl3_modT_conciseness_scan.json](../results/z4_block_scan/f5_sl3_modT_conciseness_scan.json).

## Positive controls for the robust solver

[z4_block_solver_controls.py](../code/z4_block_solver_controls.py) verifies that the robust block solver can actually recover known instances:

- a synthetic `4+4+2` cubic: recovered, reconstruction difference `0`;
- a synthetic `4+4+1+1` cubic: recovered, reconstruction difference `0`;
- the BILR `4+4+2+1` residual over `F_5`: recovered, reconstruction difference `0`.

The control file also records SHA-256 hashes for the analysis scripts and data.

File: [f5_block_solver_positive_controls.json](../results/z4_block_scan/f5_block_solver_positive_controls.json).

## What remains mathematically unresolved

The characteristic-zero single-free-`Z₄` case is not closed. The finite `F_5` result shows the corrected block solver has real discriminating power, but characteristic-zero work still needs algebraic treatment over an algebraic closure: the conic intersections, `w` square conditions, `pzw` pairing, and `H_W` tail equations must be expressed as polynomial conditions in the six essential internal parameters. A successful solution would yield a rank-22 candidate to verify on all 729 Brent identities; an exact emptiness proof would give only a restricted characteristic-zero theorem for this single-free-orbit, `Z₄`-stable residual model.

The global rank problem is still open: no rank-22 decomposition has been found, and no unrestricted proof of rank-23 optimality exists.
