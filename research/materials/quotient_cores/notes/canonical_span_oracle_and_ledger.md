# canonical rank-one-span formulation and exact F₂ oracle

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The active target remains the exact tensor rank of \(T_{\langle3,3,3\rangle}\): construct a rank-\(\le 22\) algorithm or prove rank 23 optimal over a specified field/algebraic setting.  This ARTIFACT corrected the interpretation of analysis and converted the validated 13+9 chart into a cleaner invariant finite-field object.

## Correct canonical formulation

Let
\[
E = K^9\otimes K^9 \simeq M_9(K),
\]
and let \(L\subset E\) be the 9-dimensional UV-slice space of \(T_{333}\) in the UV--W flattening:
\[
T_{333}^{UV|W}:K^{9*}\to E,
\qquad L=\operatorname{im}(T_{333}^{UV|W}).
\]
Then, over any field \(K\),
\[
R_K(T_{333})\le r
\]
if and only if there exist \(r\) rank-one matrices \(x_i=u_i\otimes v_i\in E\) whose linear span contains \(L\).

Reason: a decomposition \(T=\sum_i x_i\otimes w_i\) expresses every UV slice as a \(w\)-weighted linear combination of the \(x_i\). Conversely, if \(L\subset \operatorname{span}(x_1,\ldots,x_r)\), expanding the nine basis slices of \(L\) in the \(x_i\) gives the corresponding \(W\)-factor coefficients and hence a bilinear algorithm.

By the analysis independent-UV refinement, the rank-\(\le22\) case may be represented by 22 independent \(x_i\). Equivalently, for \(r=22\) there should be a 22-dimensional subspace
\[
S\subset E,
\qquad L\subset S,
\]
which is spanned by its rank-one matrices.  Writing \(Q:E\to E/L\), this becomes the search for a 13-dimensional quotient subspace \(H\subset E/L\) such that the rank-one matrices with \(Qx\in H\) span all of \(Q^{-1}(H)\), i.e. have quotient rank 13 and total span rank 22.

This is exactly the invariant form of the analysis 13+9 completion chart: choose 13 rank-one pivots independent modulo \(L\); the nine derived rank-one elements lie in \(L+\operatorname{span}(\text{pivots})\) and their \(L\)-projections must span \(L\).

## Retired analysis interpretations

Two analysis interpretations should not be used as evidence for rank \(\ge23\):

1. **F₂ slot-budget interpretation.** In
   \[
   X_R=T_{\text{flat}}D-X_PC,
   \]
   the matrix \(C\in K^{13\times9}\) is free column by column. A pivot rank-one matrix may be used in all nine derived columns, in none, or in any subset; using it for one column does not consume it for another. Therefore the observed D=I single-correction facts (28 reducers per slice, zero cross-slice intersection, damage to other slices, 6 completion partners) do not imply any 18/27-slot obstruction and should not guide lower-bound claims. They remain only raw local combinatorics of the standard W-basis.

2. **Generic cokernel fraction.** At a generic rank-22 point, the Brent Jacobian has rank 550, so the cokernel dimension is \(729-550=179\). A random unit target direction has expected cokernel norm fraction near \(\sqrt{179/729}\approx 0.496\). The measured \(\approx0.41\) for \(T_{333}\) at random rank-22 points is below this null expectation and is not an obstruction. It should not be refined at cn122 truncations.

## Exact F₂ span oracle

Script:

- [f2_span_oracle.py](../code/f2_span_oracle.py)

Output:

- [f2_span_oracle_results.json](../results/f2_span_oracle/f2_span_oracle_results.json)

Main exact facts over \(\mathbb F_2\):

- The projective rank-one locus in \(E=M_9(\mathbb F_2)\) has exactly
  \[
  (2^9-1)^2=261121
  \]
  points.
- The quotient map \(Q:E\to E/L\) is injective on this rank-one locus: all 261121 quotient images are distinct.
- No nonzero rank-one matrix lies in \(L\). This matches the structural description of \(L\): after permuting the \(v\)-index, \(L\simeq\{A\otimes I_3:A\in M_3\}\), so nonzero elements have rank \(3,6,9\).
- The rank-one quotient images span all 72 quotient dimensions, so the question is not ambient reachability but finding a 13-dimensional quotient subspace with an exceptionally large hidden \(L\)-span.

## Seed quotient-span tests

For each verified rank-23 seed (`cn122`, `serendipitous_8d34`, `naive_c88`) reduced over \(\mathbb F_2\):

- The 23 UV columns have rank 23.
- Their quotient images have rank 14.
- Their rank-one locus inside the 14-dimensional quotient span has:
  - 29 rank-one points,
  - quotient rank 14,
  - total span rank 23,
  - hidden \(L\)-intersection dimension 9.

This is a positive control: the oracle recovers the rank-23 algorithm as a 23-dimensional subspace containing \(L\) and spanned by rank-one matrices.

I then scanned all 13-dimensional hyperplanes of each seed quotient span, i.e. all \(2^{14}-1=16383\) candidate 22-dimensional subspaces containing \(L\) inside that seed's UV span.  Result for all three seeds:

- 0 hyperplanes satisfy the rank-22 condition.
- Best hyperplanes have total rank-one span rank 21 and hidden \(L\)-intersection dimension 8.
- For `cn122` and `serendipitous_8d34`, exactly 4 hyperplanes reach `(xspan_rank, l_intersection_dim)=(21,8)`; for `naive_c88`, exactly 4 also reach the same top pair.

This strictly strengthens one-term deletion checks: it excludes every 22-dimensional subspace between \(L\) and the rank-23 UV span of each known seed, not merely subspaces obtained by dropping an original term. It remains local to those seed spans and is not a global lower bound.

## Bounded near-seed construction search

Scripts and outputs:

- [f2_near_seed_search.py](../code/f2_near_seed_search.py)
- [f2_exact_star_neighborhood.py](../code/f2_exact_star_neighborhood.py)
- [near_seed_search.json](../results/f2_span_oracle/near_seed_search.json)
- [exact_star_neighborhood.json](../results/f2_span_oracle/exact_star_neighborhood.json)

Random and exact local searches were run in the quotient formulation:

1. 500 random 13-dimensional quotient subspaces generated by rank-one quotient points: 0 successes. These random subspaces are very sparse; best trials had only 16 rank-one members and total rank-one span 13, hidden \(L\)-dimension 0.

2. Near-seed random search: for each seed, 4000 one-swap trials from best seed hyperplanes and 4000 extensions of random 12D cores inside the seed span by an outside rank-one quotient point. Total successes: 0. Best one-swap remained at most `(xspan_rank, l_intersection_dim)=(21,8)`; random core extensions were weaker.

3. Exact star-neighborhood scan: for each seed, take the top two seed hyperplanes; for each selected hyperplane, take the 13 subspaces obtained by deleting one vector from that chosen hyperplane basis, and enumerate every candidate 13D subspace obtained by adding one rank-one quotient coset. This scanned 26 selected basis-deletion cores per seed exactly. Total successes after the corrected rerun: 0. Best candidates again reached only `(xspan_rank, l_intersection_dim)=(21,8)`.

Important repair: review found that the first version of `f2_exact_star_neighborhood.py` grouped cosets using a noncanonical residual from `gf2_reduce_with_coeff`, which can split one true coset into several groups. I patched the script with `canonical_mod_subspace`, which reduces through all available pivots, and reran the scan. The zero-success result quoted here refers only to the patched rerun in [exact_star_neighborhood.json](../results/f2_span_oracle/exact_star_neighborhood.json).

These searches did not find an \(\mathbb F_2\) rank-22 algorithm and give a sharper local picture of the known rank-23 neighborhoods. They do not constitute a proof that \(R_{\mathbb F_2}(T_{333})>22\), let alone a characteristic-zero result.

## Research consequence

The most valuable object now is the canonical rank-one-span problem: classify or construct 13-dimensional subspaces \(H\subset E/L\) whose rank-one preimage spans all of \(Q^{-1}(H)\).  This representation is field-explicit, directly comparable with Wang-style subspace occupation data, and avoids the misleading slice-correction accounting. It gives a fast exact oracle for any \(\mathbb F_2\) candidate and a clean algebraic endpoint for characteristic-zero work.

Recommended next computational direction: combine this oracle with symmetry and candidate generation in \(E/L\), not via fixed D=I slice reducers. For \(\mathbb F_2\), a candidate \(H\) is checked in milliseconds by enumerating the 261121 rank-one points once and testing membership in \(H\). For characteristic zero, the analogous geometric object is the family of \(22\)-dimensional linear spaces \(S\supset L\) whose intersection with the Segre \(\mathbb P^8\times\mathbb P^8\) spans \(S\).
