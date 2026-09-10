# repair of the dual-line pencil inference

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Correction

The analysis negative pencil classifications are not valid exclusions.  The stored
`analytical_pencil_results.json` marks many cases, including `[42,149,191]` and
`[55,141,186]`, by `random_2000`, not by an exhaustive algebraic test.  More
importantly, that search effectively looked for witnesses through rank-`c11`
factorizations, while the pencil condition is

```text
rank(Z) <= c11,  rank(M1+Z) <= c10,  rank(M2+Z) <= c01.
```

A lower-rank `Z` is allowed and can realize the flagship budgets.

## Explicit flagship witnesses checked in the original 9x9 inequalities

- line [42, 149, 191] colors [3, 3, 6, 7] budget [3, 6, 7]: witness ranks [3, 6, 6] <= [3, 6, 7], pass=True.
- line [55, 141, 186] colors [3, 3, 6, 7] budget [3, 6, 7]: witness ranks [3, 6, 6] <= [3, 6, 7], pass=True.

The witnesses are stored as row masks for `W` and `Z` in
[pencil_constructive_repair.json](../results/pencil_repair/pencil_constructive_repair.json) under
`detailed_line_analyses`.

## Structural envelope

For every all-rank-9 E11 dual line checked here, the normalized pencil satisfies
`M1^-1 M2 = H ⊗ I3` in the current ordering, or `diag(H,H,H)` after regrouping
coordinates.  The script verified 192 all-rank-9 lines and found
0 normalization failures.  For each 3x3 block, exact
enumeration of all 512 matrices gives the block-rank triples; in particular the
three constructive triples `(1,2,2)`, `(2,1,2)`, and `(2,2,1)` are realized by
rank-one update formulas.  Combining three blocks gives a block-diagonal
constructive feasible envelope.  On the analysis near-miss, this envelope
constructively realizes 192/192 all-rank-9 line
budgets.  The remaining budgets are not excluded by this calculation; they are
only outside this explicit block-diagonal envelope.

## Reclassification of analysis stored tests

Counts: `{'old_feasible_kept': 34, 'old_negative_corrected_to_constructively_feasible': 66}`.

No support-search cut should be generated from the 106 analysis reported
"infeasible" patterns.  Only future exclusions based on an exact full pencil
analysis or replayable proof may be used as necessary support consequences.

## Consequence for the main E11 distinct branch

The pencil formulation remains a useful local B/C compatibility question, but
analysis did not establish a new separating obstruction.  The central search must
continue using complete Wang rows, transported radius-three overlap cuts, and
validated compatibility tests, with pencil information admitted only when it is
constructive or rigorously proved.

## All-rank-9 support-budget boundary after the repair

The fast all-line block-envelope scan (`pencil_boundary_fast.json`) showed that the simple three-block diagonal construction is not a full description of every dual-line pencil: for all-rank-9 lines it misses only the three central minimal budgets `(4,5,5)`, `(5,4,5)`, and `(5,5,4)` (rank order `(rank(M1+Z), rank(M2+Z), rank(Z))`).  Those missing triples are not obstructions.  The follow-up construction in `allrank9_subspace_boundary.json` found explicit subspace witnesses for every one of the 192 all-rank-9 E11 lines.  For each line it records a 4-dimensional subspace `K` with `K ∩ A K = 0` for `A=M1^-1 M2`, an extra vector `e`, and three exact 9×9 matrices `W` giving:

```text
W(e)=e    -> ranks (4,5,5),
W(e)=Ae   -> ranks (5,4,5),
W(e)=0    -> ranks (5,5,4).
```

The direct rank checks in the original 9×9 inequalities pass for all 192 lines (`failure_count=0`, maximum random search trial for `K` was 5).  Combining these central witnesses with the block-diagonal envelope proves the all-rank-9 dual-line pencil condition gives no support-level color-budget restriction beyond the three individual contraction rank inequalities for length-19 budgets.  This is a constructive positive result about these pencils, not a tensor decomposition of the E11 core.

## Mixed- and low-rank lines

`pencil_boundary_fast.json` also found that the block-diagonal constructive envelope does not cover every budget allowed by individual contraction bounds for 5,567 of the 10,795 dual lines, mostly low- or mixed-rank types.  This is only a statement about the explicit block construction.  It does not prove true pencil infeasibility, because non-block-diagonal witnesses can exist, as the all-rank-9 central triples show.  Representative CP-SAT factorization on line `[1,2,3]` returned solver-INFEASIBLE for budgets `(1,2,2)`, `(2,1,2)`, and `(2,2,1)`, but without a replayable proof this is only computational evidence for that low-rank representative.  Any future use as a support consequence needs exact algebraic classification or checked proof objects.

## Independent audit and reader check

`pencil_repair_audit.json` recomputes the all-rank-9 records from raw E11 contractions, verifies the 192 saved `K, AK, e` records, reconstructs every saved `W`, and checks the three target rank triples.  It also reconstructs the flagship `Z` witnesses from row masks and compares the 100 analysis stored test colors with the near-miss support.  Result: `failure_count=0`, `warning_count=0`, 192 all-rank-9 records checked, two flagship `Z` witnesses checked, and all 100 analysis stored colors matched the near-miss.  The `106` number in analysis was a total count over all 192 all-rank-9 lines, while the stored `tests` list contains only 100 records; the reclassification counts `34+66=100` apply only to those stored records.

review independently checked the repair.  It agreed that the analysis negative inference is invalid, the two flagship witnesses are valid, and the all-rank-9 construction proves local pencil budgets add no support-level color-count restriction beyond individual contraction ranks for all-rank-9 lines.  It also caught a wording error in the construction explanation: the correct kernel inclusions are `AK ⊂ ker(I+W)` and `K ⊂ ker(A+W)`, not `(I+A)K` as a kernel.  The script docstring has been patched accordingly.

## Self-contained proof of the all-rank-9 central witnesses

Let `A=M1^-1 M2` on `V=F2^9`; all-rank-9 means `A` and `I+A` are invertible.  A four-dimensional `K` with `K∩AK=0` exists by a greedy argument.  Suppose `K_d∩AK_d=0` and put `S_d=K_d⊕AK_d`, `dim S_d=2d`.  For `d≤3`, choose

```text
v ∉ S_d ∪ A^{-1}S_d ∪ (I+A)^{-1}S_d.
```

The union has at most `3*2^(2d)≤192<512` vectors, so such `v` exists.  The three exclusions rule out the three nontrivial cases in an equation `k+αv=Aℓ+βAv`; hence `(K_d+<v>)∩A(K_d+<v>)=0`.  This builds `dim K=4`.  Choose `e∉K+AK`.

On the basis `K⊕AK⊕<e>`, define `W(k)=Ak` and `W(Ak)=Ak`.  Then:

- `AK⊂ker(I+W)`, and `(I+W)(K)=(I+A)K` has dimension 4.
- `K⊂ker(A+W)`, and `(A+W)(AK)=(I+A)AK` has dimension 4.
- `im(W)` contains `AK` and the optional value `W(e)`.

With `W(e)=e`, `W(e)=Ae`, or `W(e)=0`, direct dimension checks using `e∉K+AK` and invertibility of `A` and `I+A` give exactly `(rank(I+W),rank(A+W),rank(W))=(4,5,5)`, `(5,4,5)`, and `(5,5,4)`.  Multiplying back by `M1` gives `Z=M1W`, preserving the three ranks in the original pencil inequalities.

## Current practical value of low/mixed pencil tests

`candidate_block_envelope_scan.json` scanned four stored supports.  All four pass the individual contraction bounds on every dual line.  The simple block-envelope leaves only a few target lines for the older near-misses (`3` for the analysis base and `6` for the analysis variant, all rank type `(3,9,9)` and budget `(2,7,2)`), but many more for the analysis far supports (`40` and `48`, including rank types `(6,6,6)`, `(9,9,9)`, and mixed types).  These counts are not violations.

Exact rank-factor CP-SAT witness search on representative low/mixed outside-envelope cases produced no new support theorem:

- line `[9,87,94]`, budget `(2,7,2)`, status `UNKNOWN` after 90 s;
- line `[5,35,38]`, budgets `(3,3,4)`, `(3,4,4)`, `(4,4,3)`, all `UNKNOWN` after 90 s each;
- line `[4,178,182]`, budget `(2,4,2)`, solver `INFEASIBLE` after 90 s, but without a replayable proof.

Thus low/mixed pencil analysis may still be a real local question, but it is not yet an established global obstruction and should not drive support-search cuts until it has exact algebraic classification or checked proof objects.
