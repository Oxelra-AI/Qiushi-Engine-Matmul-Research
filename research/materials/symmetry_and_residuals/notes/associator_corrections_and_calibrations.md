# associator corrections and reduced-pair calibrations

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Why this ARTIFACT changed direction

The analysis handoff proposed checking whether a fixed scalar Pfaffian polynomial has no zeros under internal `SL_3^4` frame changes, beginning with small finite-field scans and one-plane elimination. That route is not mathematically sound for excluding cyclic rank 22: on the actual `SL_3^4` frame variety a regular function without zeros would have to be a unit, so for this coordinate ring it cannot be a nonconstant polynomial; in localized charts this point would need separate checking. More importantly, a rank-22 point would be expected to lie on a special closed locus. Finite-field sampling or one-pair scalar nonvanishing cannot replace equations that hold for all pairs.

The corrected equations are:

- For each pair `(X,Y)`, let `C=[H_X,H_Y]` and `Omega=K C`, an ordinary skew form. Rank at most 2 is characterized exactly by the vanishing of all `4 x 4` Pfaffians of `Omega`. The scalar `Phi=2 tr(C^4)-tr(C^2)^2` remains useful only as a nonzero certificate that rank is at least 4; `Phi=0` is not equivalent to rank at most 2 for the indefinite trace form.
- In the `k=n+1` normal form forced by a ten-cube residual on `n=9` variables, there is a stronger common-pencil condition: for every fixed `X`,
  `Omega(X,Y) wedge Omega(X,Z)=0` in `Lambda^4(sl_3)` for all `Y,Z`. This follows because `Omega(X,Y)=-c G(X) wedge G(Y)`.

## Exact reduced-pair calibration on the BILR exterior component

Script: [reduced_pair_associator_calibration.py](../code/reduced_pair_associator_calibration.py)  
Data: [bilr_reduced_pair_calibration.json](../results/reduced_pair_associator/bilr_reduced_pair_calibration.json)

For each split `{i,j}|{k,l}`, I computed an integer basis of `(P_i+P_j)^perp cap sl_3` using the trace pairing convention `l_A(X)=tr(A X)` with stored BILR representatives transposed. In all six cases:

- `(P_i+P_j)^perp cap sl_3` is exactly two-dimensional (`constraint_row_rank=7`).
- The three forms of `P_i` and `P_j` vanish on both basis vectors, and the full product agrees with the product using only the remaining two plane corrections.
- `Omega=K[H_X,H_Y]` is exactly skew, the commutator annihilates the identity, and its image is traceless.
- The Jordan-only commutator has rank 4, but the full reduced commutator has rank 0 in all six splittings.

Thus the proposed cheap two-frame Pfaffian system is inactive at the BILR identity frame. This does not prove it is inactive everywhere, but it says the specific reduced-pair route should not be the next heavy elimination target for the BILR component.

## Exact common-pencil certificate for the fixed BILR residual

Script: [common_pencil_certificate.py](../../relaxations_and_cuts/code/common_pencil_certificate.py)  
Data: [bilr_common_pencil_certificate.json](../results/reduced_pair_associator/bilr_common_pencil_certificate.json)

For the fixed BILR residual, using the same `X,Y` as the analysis Pfaffian certificate and `Z=diag(1,-1,0)`, the common-pencil equation fails exactly:

- `rank Omega(X,Y)` on `sl_3` is 4.
- `rank Omega(X,Z)` on `sl_3` is 2.
- `Omega(X,Y) wedge Omega(X,Z)` has 9 nonzero `Lambda^4(sl_3)` coefficients; the first coefficient in the fixed `sl_3` basis is `-19440`, and the gcd of absolute nonzero coefficients is `19440`.

This gives another low-degree exact reading of the Strassen--Hessian obstruction for the fixed BILR residual. Because `Omega(X,Y)` already has rank 4, the mixed wedge is not an independent lower-bound mechanism; it records the stronger common-pencil structure that a ten-cube residual would have to satisfy. It is not a universal `(10,4)` exclusion; variable internal frames must satisfy the same common-pencil equations symbolically, and solutions would be candidate loci requiring further Waring/Brent verification.

## Ledger and old-note repairs

Patched:

- [associator_lemma_and_certificate.md](associator_lemma_and_certificate.md): renamed the theorem as Strassen-Hessian, replaced the false scalar equivalence by the exact `4 x 4` Pfaffian statement, fixed the `H_X=K^{-1}S_X` convention in the proof sketch, added the one-zero-weight caveat for `k=n+1`, removed the unconditional span-dimension proof, and recorded that the reduced-pair split vanishes at BILR.
- [jennrich_corrected_scope.md](jennrich_corrected_scope.md): removed the old implication that the BILR orbit or whole `(10,4)` branch is excluded.
- [jennrich_and_10_4_exclusion.md](jennrich_and_10_4_exclusion.md): replaced the overreaching historical content by a superseded-scope warning.
- [structured_theorems_ledger_.md](../../quotient_cores/notes/structured_theorems_ledger_.md): added analysis corrections, the common-pencil certificate, and exact evidence paths.
- [pfaffian_certificate.py](../code/pfaffian_certificate.py) and its JSON output: corrected the embedded theorem text so `Phi` is recorded as a one-directional certificate and the exact `4 x 4` Pfaffian equations are named.

## Relation to related analysis finite-field work

related analysis record reports a meaningful but still open improvement attempt for the `F_2` E11 distinct branch. They built an annihilator-weight representation of all 417199 E11-core Wang rows and explained the current 12-violation support through dual-line and dual-plane deficits; fixed-A completion for that inadmissible support is infeasible, but complete-Wang-admissible distinct support exclusion is not proved. Independent related analysis replay should wait until related analysis produces a replayable exclusion certificate for the distinct branch; if that happens, it may improve the global finite-field lower bound from Wang's `R_F2 >= 20` to `R_F2 >= 21`.

## Current meaning

The fixed BILR residual Waring rank 11 is supported by explicit 11 cubes, Koszul--Young flattening rank, and the Strassen/Hessian commutator equation system (nonzero rank-4/Phi certificate plus common-pencil reading). The earlier span-dimension argument is conditional on all weights being nonzero and should not be used as an unconditional proof. The pure-cyclic rank-22 problem remains open: `(10,4)` for variable exterior frames, other exterior components including degeneracies, and nontraceless `m>=5` all still need real work. The unrestricted independent-UV incidence remains the only line that covers arbitrary rank-22 algorithms.
