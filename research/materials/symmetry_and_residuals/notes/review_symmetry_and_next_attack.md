# review review: analysis termwise inner symmetry theorem and next De Groote-symmetry attack

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## 1. Status of the analysis torsion theorem

I reviewed [torsion_layer_repair.md](torsion_layer_repair.md), the review verifier integration `independent-verification-record`, and the analysis arrangement script/data enough to judge whether the repaired theorem can be used as a stable research component.

### Corrected theorem scope

The usable statement is exactly the narrow inner/sandwich, termwise-fixed statement:

> Over a characteristic-zero field, if an inner/sandwich De Groote symmetry of `T_<3,3,3>` is noncentral modulo the scalar center and has finite order modulo the center, then no exact rank decomposition of length `<=22` can have every rank-one Segre point fixed projectively by that symmetry.

The note correctly no longer claims coverage of:

- cyclic factor permutations;
- transpose-containing outer De Groote components;
- orbit-permuting decompositions whose relevant power is central;
- the transverse unsymmetric full-UV-rank incidence.

This restriction is not cosmetic. The proof uses a simultaneous eigenspace decomposition in the three fixed tensor factors, with sandwich weights
`p_a/q_b`, `q_b/r_c`, `r_c/p_a`. It is not automatically available for outer elements.

### Uniform torsion proof, not finite scan

The saved analysis note already contains the needed uniform proof of the torsion coarsening lemma. The essential argument is independent of a bound on the finite order `d`:

Choose standard residues `P_a,Q_b,R_c in {0,...,d-1}`. A multiplicative block is specified by

```text
(P_a-Q_b, Q_b-R_c) mod d.
```

Refine by the exact integer pair `(P_a-Q_b, Q_b-R_c)`. If two triples in the same multiplicative block share `a`, then

```text
P_a-Q_b == P_a-Q_b' mod d,
Q_b-R_c == Q_b'-R_c' mod d.
```

Because `Q_b,Q_b'` are standard residues, the first congruence gives `Q_b=Q_b'`; the second then gives `R_c=R_c'`. Hence the exact integer pairs agree. The same proof applies if the shared coordinate is `b` or `c`. Therefore different exact additive subblocks inside one multiplicative block are disjoint in the original `a`, `b`, and `c` index sets. Since the actual matrix-multiplication tensor factors use coordinates `(a,b)`, `(b,c)`, and `(c,a)`, this is a genuine direct sum in all three tensor factors.

The finite scripts [torsion_direct_sum_lemma_check.py](../code/torsion_direct_sum_lemma_check.py) and the d=2..12 JSON should be treated only as guards against coding/proof mistakes, not as the proof of the all-finite-order theorem. The note says this explicitly and is safe on this point.

### The small-component additivity ARTIFACT

The proof then needs: inside each multiplicative block, all but at most one exact subblock have at least one tensor factor of dimension at most 2. The analysis note gives a correct proof: if an exact subblock has all three actual factor dimensions >2, then either one original index-set size is 1 and the other two must be 3 (exhausting two coordinate sets), or all three original index-set sizes are at least 2 (so two disjoint such subblocks would require at least four indices in each of `{0,1,2}`). Thus at most one component is large. This allows an induction peeling off the small components.

This is the only place where tensor direct-sum additivity is used. It does not invoke the false general Strassen direct-sum conjecture; it invokes only the protected Ja'Ja'--Takche situation at each two-summand peeling ARTIFACT.

## 2. Source status for Ja'Ja'--Takche

The primary SIAM full text was not fetched. The new analysis retrieval found the DOI and Crossref record for Ja'Ja'--Takche, `10.1137/0215071`, but the SIAM full-text endpoint returned HTTP 403. The Crossref metadata includes the article's own abstract, which states:

> Let `S1` be a set of `r` `m x n` bilinear forms and `S2` be a different set of `s` `p x q` bilinear forms. If `2 in {r,m,n,s,p,q}`, the direct sum conjecture holds over any field.

This is primary-article metadata/abstract support for exactly the quantifier needed here: our tensor direct sums correspond to two disjoint bilinear systems, and a component with one tensor factor of dimension at most 2 matches one of `r,m,n,s,p,q` being 2 (or smaller, by embedding/conciseness). It also gives the field scope as `any field`, stronger than needed for characteristic zero.

However, because the theorem is load-bearing, the proof ledger should still distinguish:

- **verified now:** DOI, bibliographic identity, primary abstract statement, and independent secondary sources (`Rupniewski` excerpt and `Buczynski--Postinghel--Rupniewski`) agreeing that this is the Ja'Ja'--Takche protected additivity theorem;
- **not yet verified:** the exact theorem numbering/proof text and whether the full article has any auxiliary conventions not visible in the abstract.

For the present research, this is enough to keep the analysis theorem as a working mathematical component, but not enough for a final polished proof package without a direct copy of JT86 or an explicit self-contained proof of the ≤2-factor case.

## 3. analysis dependency

The analysis arrangement data records:

- total flats: 6425;
- one central-only flat and 6424 noncentral flats;
- 58 distinct noncentral support partition signatures;
- certified lower-bound histogram under the weak declared table: `23:36, 24:108, 25:27, 27:6253`;
- no noncentral pattern with bound `<=22`.

The script [semisimple_arrangement_blockrank.py](../../deformation_and_incidence/code/semisimple_arrangement_blockrank.py) enumerates the intersection lattice by exact rational row reduction of all pair-equality hyperplanes for the repeated-difference weights `(p_a-q_b, q_b-r_c)`. The analysis torsion theorem legitimately imports this as an existing exact computation. The analysis review did not rerun the 400s enumeration, so the theorem remains dependent on that saved exact enumeration and on the CHL-supported `(2,3,3)->14` input.

## 4. Research consequence

The termwise inner symmetry stratum is now a serious, correctly scoped exclusion in characteristic zero. It is not a proof of `R(T_333)=23`, and it does not exclude rank-22 algorithms outside the termwise inner fixed locus. Its value is that it removes a natural mechanism shared by many structured rank-23 constructions, and it sharply defines the remaining symmetry work.

The strongest next attack is not to extend more finite-field order-p sandwich families by hand. The highest-value unresolved symmetry family is the outer De Groote stratum: cyclic factor rotations and transpose-containing symmetries. This family is directly tied to Strassen/Smirnov/BILR-style invariant algorithms and is also a plausible construction space for rank 22.

## 5. Reorganized next attack: cyclic/outer De Groote symmetry

The next work should build a concrete cyclic-invariant algebraic search/checking instrument before attempting any final theorem. A suitable first construction route is the classical cyclic ansatz

```text
T = sum_i c_i l_{U_i}(A) l_{U_i}(B) l_{U_i}(C)
  + sum_j [ l_{U_j}(A) l_{V_j}(B) l_{W_j}(C)
          + l_{U_j}(B) l_{V_j}(C) l_{W_j}(A)
          + l_{U_j}(C) l_{V_j}(A) l_{W_j}(B) ],
```

where the first sum consists of factor-rotation fixed rank-one terms and the second sum consists of 3-orbits. For rank 22 the skeletons are `22 = f + 3m`, so `f ≡ 1 mod 3`. The practical skeletons are `f=1,4,7,10,13,16,19,22` with `m=(22-f)/3`, but high fixed counts should be checked against the dimension of the fixed rank-one span and against whether they can supply the non-cyclic-invariant parts if a twisted action is used. For pure cyclic invariance the target should be projected to the cyclic-invariant subspace first.

This route should be run in both directions:

1. **Construction search:** implement the cyclic ansatz over `C` and/or small finite fields, starting with rank 22 skeletons and using the existing amplitude/conditioning diagnostics to avoid mistaking noncompact border paths for exact algorithms. Every candidate must be expanded back to all 729 Brent equations and exactified before it matters.
2. **Exclusion analysis:** compute the fixed-rank-one locus, orbit equations, and skeleton feasibility for cyclic rotation and transpose-type involutions. For order `p` inner cases, a prime-order reduction may make the finite list smaller than the earlier composite count, but the outer cases should take priority because they are not covered by the analysis theorem and are where known symmetric constructions live.

The general transverse full-independent-UV rank-22 incidence remains untouched. Any outer-symmetric success or exclusion will be an important structured-family result, not a global rank-23 lower bound unless a separate argument proves every rank-22 decomposition must have such symmetry.

## 6. Basic exact checks for pure cyclic rotation

I wrote and ran [cyclic_outer_basic_checks.py](../code/cyclic_outer_basic_checks.py); the checked output is [cyclic_outer_basic_checks.json](../results/outer_symmetry/cyclic_outer_basic_checks.json).

The script verifies the following elementary but useful facts for the further research:

- The ambient tensor space has dimension 729.
- The pure factor rotation `rho(i,j,k)=(j,k,i)` has orbit histogram `1:9, 3:240`, so the cyclic-invariant linear subspace has dimension `249`.
- `T_<3,3,3>` is invariant under this cyclic factor rotation in the QMM support convention `(ab,bc,ca)`.
- `T_<3,3,3>` is not invariant under swapping the first two tensor factors; the script records explicit asymmetric support coordinates.
- A term projectively fixed by pure cyclic rotation has the form `u⊗u⊗u`; these span `Sym^3(K^9)` of dimension `165`. Hence an all-fixed pure-cyclic decomposition would lie in the fully symmetric subspace and cannot equal `T_<3,3,3>`.
- Rank-22 cyclic orbit skeletons are exactly `22=f+3m` with `(f,m)=(1,7),(4,6),(7,5),(10,4),(13,3),(16,2),(19,1),(22,0)`. The all-fixed `(22,0)` skeleton is impossible by the previous point; the mixed skeletons are the meaningful construction/exclusion targets.
- In the raw vector parameterization each rank-22 skeleton has `9 f + 27 m = 198` vector coefficients before gauge/scaling reductions, against 249 cyclic-invariant linear coordinates. Rank 23 has 207 raw vector coefficients and is known to contain structured algorithms, so parameter count alone is not a mathematical exclusion.

This check supports the handoff: build a cyclic-invariant rank-22 ansatz/search and matching exclusion analysis rather than continuing only inner termwise finite-order sweeps.
