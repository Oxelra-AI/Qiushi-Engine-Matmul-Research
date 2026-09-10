# structural coset reduction toward a rank-20 exclusion

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

This note consolidates the current strongest lower-bound route for proving
\(R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\ge 21\).  It is not yet a final
proof because the dim-2 Wang occupation raises 479 and 484--491 still need a
proof-producing certificate or an independently replayable exact proof object.
The new content of this ARTIFACT is that, once those raises are accepted as
premises, the remaining high-rank A-factor structure collapses to a small
coset profile and that profile is now DRAT-certified impossible at the full
A-side Wang occupation level.

## Files produced in analysis

- [coset_structural_checks.py](../code/coset_structural_checks.py)
- [coset_structural_checks.json](../results/structural/coset_structural_checks.json)
- [saturated_flattening_checks.py](../code/saturated_flattening_checks.py)
- [saturated_flattening_checks.json](../results/structural/saturated_flattening_checks.json)
- [flattening_product_formula.py](../../quotient_cores/code/flattening_product_formula.py)
- [flattening_product_formula.json](../../quotient_cores/results/structural/flattening_product_formula.json)
- [coset_rankone_fullwang_compress.py](../code/coset_rankone_fullwang_compress.py)
- [coset_rankone_fullwang_compress.json](../results/coset_fullwang/coset_rankone_fullwang_compress.json)
- [certify_all_coset_H.py](../code/certify_all_coset_H.py)
- [all_coset_H_drat_manifest.json](../results/coset_fullwang_cert_all/all_coset_H_drat_manifest.json)
- [certify_original_dim2_raises.py](../../finite_certification/code/certify_original_dim2_raises.py)
- [dim2_direct_full_cnf.py](../../finite_certification/code/dim2_direct_full_cnf.py)
- [dim2_lp_feasibility.py](../../finite_certification/code/dim2_lp_feasibility.py)
- [dim2_lp_feasibility.json](../../finite_certification/results/dim2_raise_certs/dim2_lp_feasibility.json)

The last three dim-2 certification scripts are exploratory.  They did not yet
produce a certificate for the dim-2 raises.

## Premises currently needed

1. The standard split flattening \(\Phi_A(T)\) is a 27-by-27 permutation matrix.
   This was verified in analysis and re-used here.
2. In any length-20 decomposition,
   \[
   \sum_t \operatorname{rank}(A_t)\ge 27,
   \qquad \sum_t(\operatorname{rank}(A_t)-1)\ge 7.
   \]
3. Every one-dimensional A-line has quotient lower bound at least 19.  analysis
   recorded that all 49 rank-one, 294 rank-two, and 168 rank-three nonzero
   A-directions have line lower bound 19.
4. The original Wang LUT dim-2 occupation raises 479 and 484--491 from old lower
   bound 18 to 19 are valid.  analysis independently reproduced these as CP-SAT
   `INFEASIBLE` with 29,210 rows each, but analysis did not yet turn them into
   checked certificates.  This is the main remaining proof burden.
5. The Wang row table used for full A-side support constraints is a faithful
   table for length 20 over the full A-slot; the analysis DRAT certificates prove
   unsatisfiability only relative to the compressed rows derived from that table.

## Short high-rank coset argument

Assume the dim-2 raises are valid.  In a length-20 decomposition, repeated
high-rank A-directions are impossible: quotient by their one-dimensional line
leaves at most 18 terms, contradicting the line lower bound 19.  For two
distinct high-rank factors \(a,b\), quotienting by \(\langle a,b\rangle\) also
leaves at most 18 terms.  Therefore \(\langle a,b\rangle\) must be a dim-2 orbit
whose lower bound remains below 19.  Among dim-2 orbits with at least two
high-rank nonzero elements, analysis leaves only orbits 481, 482, 483.

The finite orbit-pattern check in
`coset_structural_checks.json` shows:

- orbit 481 has rank pattern \((1,2,2)\),
- orbit 482 has rank pattern \((1,3,3)\),
- orbit 483 has rank pattern \((1,2,3)\),
- hence every allowed pair of distinct high-rank factors satisfies
  \(\operatorname{rank}(a+b)=1\).

There is an important nuance: rank-one difference is not equivalent to being
allowed.  Orbit 479 also has rank pattern \((1,2,2)\), but is among the raised
and excluded orbits.  The reduction uses only the one-way implication
`allowed => rank(a+b)=1`.

Fix one high-rank factor \(p\).  For every other high-rank factor \(a\), put
\(r_a=a+p\).  Each \(r_a\) is rank one.  For two such differences,
\(r_a+r_b=(a+p)+(b+p)=a+b\), also rank one.  Over \(\mathbb F_2\), nonzero
rank-one matrices have unique form \(uv^T\) with nonzero \(u,v\in\mathbb F_2^3\).
The finite check confirms the elementary lemma: for two distinct rank-one
matrices \(uv^T\) and \(xy^T\), the sum has rank one iff either \(u=x\) or
\(v=y\).  Moreover every pairwise-compatible triple of rank-one matrices shares
one side globally.  The proof is short: if two members share column direction
\(u\) but have different row directions \(v_1\ne v_2\), then a third member with
another column direction would have to share row direction with both, impossible;
the transposed argument handles the other case.

Thus all high-rank A-factors lie in one affine rank-one coset
\[
  p+u\otimes (\mathbb F_2^3)^*
\]
or, after transposition, in
\[
  p+(\mathbb F_2^3)\otimes v^T.
\]
This is now a proof-readable argument, not a clique enumeration.

## Consequences inside the coset

Normalize to the column-type coset.  analysis and analysis finite checks use the
canonical lower-block rank-two representative
\(p=E_{22}+E_{33}\) with varying first row.  The coset has eight points forming
\(AG(3,2)\).  The finite arithmetic in
`coset_structural_checks.json` and `coset_plane_verify.json`
confirms:

- every five-point subset of \(AG(3,2)\) contains an affine plane;
- every four-point affine plane of high-rank coset points spans a dim-3
  subspace with Wang lower bound 17;
- such a plane cannot occur in a length-20 decomposition because quotienting by
  its four A-factors leaves at most 16 terms, contradicting lower bound 17.

Therefore there are at most four high-rank A-factors.  Since split flattening
requires excess at least seven, there must be exactly four high-rank A-factors,
and the excess profile must be
\[
  (\operatorname{rank}-1)\text{-sum}=7.
\]
This forces one rank-two and three rank-three high-rank factors, with all other
sixteen A-factors of rank one.  Lower-block rank-one cosets have no rank-three
points and are impossible.  In a lower-block rank-two coset, the four rank-three
points themselves form one affine plane, so all four rank-three points cannot be
selected.  The remaining profile is exactly one rank-two plus three rank-three
points, with the chosen four not forming an affine plane.  analysis records the
16 normalized cases.

## Full A-side Wang exclusion of the remaining normalized H cases

I independently compressed the complete full-Wang length-20 row table against
each of the 16 normalized high-rank sets \(H\).  Unlike the peer script, this
allowed all 49 rank-one A-directions as Boolean variables and used only the
constraints
\[
  \sum_{x\in R\cap \mathcal R_1} z_x \le c(R)-|R\cap H|,
  \qquad \sum_x z_x=16.
\]
For every one of the 16 cases, compression produced 230,667 unique nontrivial
constraints from 8,283,456 full rows and CP-SAT found infeasibility.  Then I
extracted small active cores and certified all 16 resulting CNFs with CaDiCaL
DRAT proofs replayed by `drat-trim`.

Manifest:
[all_coset_H_drat_manifest.json](../results/coset_fullwang_cert_all/all_coset_H_drat_manifest.json).

All 16 cases are `verified: true`.  Active core sizes range from 1,417 to 2,000
constraints; CNFs have roughly 28k--43k variables.  This is a strong proof asset:
conditional on the structural reduction and row provenance, there is no A-side
Wang-admissible rank-20 support with the surviving coset profile.

## Saturated split-flattening compatibility

The structural reduction also implies the A-rank sum is saturated:
\[
  16\cdot 1+1\cdot 2+3\cdot 3=27=\operatorname{rank}\Phi_A(T).
\]
For any saturated decomposition, if \(P=\Phi_A(T)\) and
\(F_t=\Phi_A(A_t\otimes B_t\otimes C_t)\), then
\(G_t=P^{-1}F_t\) are complementary idempotent projections.  In the actual index
convention, analysis checked the product formula
\[
F(a,b,c)P^{-1}F(a',b',c')=F(a(B'C^T)a', b, c')
\]
on all 729 elementary pairs and 5000 random dense pairs.  Therefore a saturated
decomposition satisfies the termwise identities
\[
A_t(B_s C_t^T)A_s=0 \quad (t\ne s),\qquad
A_t(B_t C_t^T)A_t=A_t,
\]
provided \(B_t,C_t\ne0\).  The schoolbook 27-term decomposition is a positive
control: it saturates and all projection identities pass.  Verified rank-23
controls do not saturate the A-split rank sum (rank sums 30--32), and they
accordingly fail these identities; this is expected and prevents misuse.

These identities were not needed for the A-side Wang exclusion above, but they
remain valuable if the dim-2 raise certification route stalls or if a future
route needs to couple the surviving A-profile directly to B/C factors.

## Failed or unfinished certification attempts for dim-2 raises

I attempted to turn the original-LUT dim-2 raises into certificates.

- `certify_original_dim2_raises.py` extracts active CP-SAT cores and
  encodes them into occurrence-slot CNFs.  For orbit 479, two pilots did not
  find an infeasible active core: one ended `UNKNOWN` with 1,992 active rows;
  a longer run ended `UNKNOWN` with 2,618 active rows.
- `dim2_lp_feasibility.py` showed the LP relaxations are feasible for
  every raised orbit 479 and 484--491, so no simple real Farkas certificate is
  available from the raw occupation system.
- `dim2_direct_full_cnf.py` encoded the full occurrence-slot CNF for
  orbit 479.  The generated CNF and partial DRAT are large
  (`orbit479_full.cnf` about 1.5 GB; `orbit479_full.drat` about 1.5 GB), and
  CaDiCaL timed out after 900s.  This is not evidence against the raise; it only
  says this direct encoding is not yet the right proof method.

Thus the dim-2 raises remain the exact unfinished proof support.  They are the
only large missing link in the current rank-21 lower-bound route if the Wang row
provenance and symmetry normalization are accepted.

## Current route status

A conditional proof chain is now clear:

1. line LBs exclude repeated high-rank A directions;
2. certified dim-2 raises would force every high-rank pair into orbits 481--483;
3. these allowed orbits force rank-one pairwise differences;
4. rank-one pairwise differences force one row/column affine coset;
5. affine-plane and split-flattening arguments force exactly the 16 normalized
   one-rank-two plus three-rank-three cases plus sixteen rank-one factors;
6. analysis DRAT certificates exclude all 16 cases at the full A-side Wang
   occupation level.

If analysis is given proof-producing support, this chain would prove no length-20
exact decomposition exists, hence \(R_{\mathbb F_2}(T_{333})\ge21\).  The next
highest-value work is therefore to certify or otherwise prove the original-LUT
dim-2 raises 479 and 484--491, not to run generic searches over quotient orbits
481--483.  If a hidden flaw is found in those raises or in the Wang row
provenance, this reduction must be repaired or abandoned accordingly.
