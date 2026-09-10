# restricted-core structure after continuation-route correction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Research context

The analysis gauge-invariant analysis changed the value of the rank-23 continuation line: the tracked one-dimensional paths from cn122/serendipitous are non-compact cancellation ends, not finite rank-22 candidates. The route is not mathematically exhausted, but raw continuation is no longer a good use of effort. The active finite-field restricted-core line is therefore the strongest current source of exact objects and transferable obstructions.

research_record corrected an earlier capacity ILP error: halfspace constraints were mistakenly encoded instead of multiplicity constraints. Any use of that old infeasibility result must be discarded. related analysis is now building the correct all-orbit multiplicity ILP. This ARTIFACT supplies exact rank-21 pool structure for that effort.

## Inputs inspected

- E11 core metadata: `data/restricted_cores/mask_001_E11_meta.json`
- E12+E21 core metadata: `data/restricted_cores/mask_010_E12_E21_meta.json`
- E13+E22+E31 core metadata: `data/restricted_cores/mask_084_E13_E22_E31_meta.json`
- E11 rank-21 flip pool: [mod2-rank21a.npy](../../exact_baselines/arrays/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy)
- E12+E21 rank-21 flip pool: [mod2-rank21a.npy](../../exact_baselines/arrays/e12e21_flip_workspace/data/schemes_modp/e12e21core/mod2-rank21a.npy)
- H3/E13+E22+E31 rank-21 flip pool generated in this ARTIFACT: [mod2-rank21a.npy](../../exact_baselines/arrays/e13e22e31_flip_workspace/data/schemes_modp/e13e22e31core/mod2-rank21a.npy)

Scripts:

- [core_rank21_structure.py](../code/core_rank21_structure.py)
- [core_rank21_wpattern.py](../code/core_rank21_wpattern.py)
- [prepare_restricted_core_flip_tensor.py](../code/prepare_restricted_core_flip_tensor.py)

## Exact results

### H3 / E13+E22+E31 upper-bound screen

Prepared the H3 core as a flip-cpd COO tensor under `data/e13e22e31_flip_workspace/` and ran:

```bash
./bin/search2 e13e22e31core --target-rank 19 --pool-size 500 --path-limit 2000000 --max-attempts 3000 --stop 5000 --threads 8 --plus --plus-lim 20000 --save --id a
```

Result: verified pools down to rank 21; no rank-20 candidate in 3001 attempts. This proves only an upper bound `R_F2(H3) <= 21`, not exactness, but it rules out the hoped-for shortcut `R_F2(H3) >= 22` for proving full `R_F2(T)=23` via a codimension-one restriction.

Together with analysis's E12+E21 flip run, all three related analysis cores E11, E12+E21, and E13+E22+E31 now have verified F2 rank <=21 schemes. Therefore none can yield a full-tensor lower bound 23 through the simple substitution lemma target `R(core) >=22`.

### Deletion-span structure in independent rank-21 pools

For a rank-21 CPD of a core, let `K` be the span of the 21 two-factor columns `u_i⊗v_i`, and let `L` be the 9-dimensional target C-slice space. Deleting two terms gives a 19-column span. If `dim((K+L)/K)=1`, the deletion is a rank-19 near miss: it misses exactly one C-slice mode.

The structural analyzer verified every pool row as an exact F2 CPD and then enumerated all one- and two-term deletions.

#### E11

Artifact: [e11_rank21_pool_structure.json](../results/e11_rank21_pool_structure.json)

- verified schemes: 519/519
- every one-term deletion has deficiency `(1,20,21)`
- two-term deletion distribution:
  - 815 pairs have deficiency `(1,19,20)`
  - 108175 pairs have deficiency `(2,19,21)`
- recurring missing modes include single C-slice coordinates and row/column blocks; top modes in the first pass were bits `[4]`, `[3]`, `[6]`, `[8]`, `[7]`, `[5]`.

Single-replacement closure test on 12 independent near-miss examples drawn from the top six modes checked `12 * 2,475,453 = 29,705,436` rank-one replacement possibilities and found no closure. This extends analysis's one-replacement negative evidence beyond the cn122-derived E11 scheme to independent flip-cpd rank-21 schemes. It is not a lower bound.

Artifact: [e11_rank21_pool_structure_repair80.json](../results/e11_rank21_pool_structure_repair80.json)

#### E12+E21

Artifact: [e12e21_rank21_pool_structure.json](../results/e12e21_rank21_pool_structure.json)

- verified schemes: 500/500
- every one-term deletion has deficiency `(1,20,21)`
- every two-term deletion has deficiency `(2,19,21)`
- no two-deletion deficiency-one near misses were present.

This core has rank <=21 but, in the sampled rank-21 pool, it lacks the repeated-channel near-miss structure seen in E11 and H3.

#### H3 / E13+E22+E31

Artifact: [e13e22e31_rank21_pool_structure.json](../results/e13e22e31_rank21_pool_structure.json)

- verified schemes: 554/554
- every one-term deletion has deficiency `(1,20,21)`
- two-term deletion distribution:
  - 626 pairs have deficiency `(1,19,20)`
  - 115714 pairs have deficiency `(2,19,21)`
- recurring modes again include many single C-slice coordinates and row/column blocks.

### Exact W-repetition law in sampled pools

Artifact: [restricted_core_rank21_wpatterns.json](../results/restricted_core_rank21_wpatterns.json)

For E11 and H3, the following equivalence held over all sampled rank-21 pool schemes:

> A two-term deletion is a deficiency-one rank-19 near miss iff the two deleted terms have identical W-factor masks.

Numerically exact counts:

- E11: `def1_same_w = 815`, `def1_diff_w = 0`, `same_w_not_def1 = 0`.
- H3: `def1_same_w = 626`, `def1_diff_w = 0`, `same_w_not_def1 = 0`.
- E12+E21: all 500 sampled rank-21 schemes have 21 distinct W masks, so there are no identical-W pairs and no deficiency-one two-deletions.

This is an exact observation about the sampled pools, not a theorem about all decompositions. It is nevertheless a useful structural signal: the closest rank-19 surfaces currently found arise by deleting two terms assigned to the same output-channel linear form, leaving exactly that C-slice mode missing. One-replacement closure fails on tested examples, so a rank-19 construction, if reachable near these rank-21 pools, likely needs coordinated replacement/recombination of at least two surviving two-factor columns, or a rank-21 seed family with a different W-multiplicity pattern.

## CryptoMiniSat status

The analysis CryptoMiniSat run on E11 rank-19 (`s4_t28_tool1`) returned exit code 0 but no `s SATISFIABLE` or `s UNSATISFIABLE` line; stdout ended in continuing solver statistics and `EXIT=0`. Treat it as a timed solver non-result, not as evidence for satisfiability or unsatisfiability.

Files:
- result: `tasks/s4_t28_tool1/result.json`
- stdout: `tasks/s4_t28_tool1/stdout.log`

## Strategic interpretation

1. The codimension-one restriction lower-bound shortcut using E11, E12+E21, or H3 cannot prove full F2 rank 23, because all three now have explicit rank <=21 upper bounds from flip-cpd. Lower-bound work should move to the full F2 rank-22 envelope or to stronger restrictions/quotients, not keep hoping for `R(core)>=22` for these cores.

2. E11 remains the shortest constructive route to a full rank-22 algorithm over F2: `R_F2(E11)<=19` would combine with the removed rank-3 slice to give `R_F2(T333)<=22`. Current evidence shows many rank-19 near misses but no single-replacement closure. This points to a targeted two-replacement or quotient-guided SAT search rather than another plain solver race.

3. The W-repetition law gives related analysis a compact obstruction candidate: in sampled rank-21 schemes, deleting an equal-W pair removes a single quotient direction of L, while deleting unequal W terms misses two directions. If Wang orbit constraints can formalize why all rank-19 candidates must pass through such repeated-channel mergers and then rule out the necessary multi-replacement patterns, it could strengthen the finite-field lower-bound route. At present that implication is only a hypothesis.

4. Geometry is still active only if formulated directly as an incidence problem `Brent + exact projective uv null relation + bounded amplitude/local chart`; raw one-dimensional continuation should not be continued.

## Repair of quotient-mode calculation and stronger two-replacement search

After writing the first quotient-guided two-replacement pilot, I found a real implementation bug in the quotient reduction routine used only for missing-mode extraction and quotient-guided repair searches. The reducer stopped when the current leading bit was not a base pivot; canonical row reduction must instead sweep all basis pivots in descending order. This bug did **not** affect direct rank/deficiency counts or the equal-W law, because those use independent Gaussian rank computations. It did affect the first missing-mode rankings and the first two-replacement pilot. The repaired scripts are:

- [core_rank21_structure.py](../code/core_rank21_structure.py)
- [e11_two_replacement_search.py](../code/e11_two_replacement_search.py)

Repaired structure files:

- E11: [e11_rank21_pool_structure_full_examples_v2.json](../results/e11_rank21_pool_structure_full_examples_v2.json)
- H3: [e13e22e31_rank21_pool_structure_v2.json](../results/e13e22e31_rank21_pool_structure_v2.json)

The rank/deficiency counts remained unchanged after repair:

- E11: 519 verified rank-21 schemes; all one-deletions `(1,20,21)`; two-deletions 815 `(1,19,20)` and 108175 `(2,19,21)`.
- H3: 554 verified rank-21 schemes; all one-deletions `(1,20,21)`; two-deletions 626 `(1,19,20)` and 115714 `(2,19,21)`.

The repaired E11 missing-mode distribution changed because the quotient residues are now canonical; the top modes are now `[6,7]`, `[4]`, `[3]`, `[6]`, `[5,8]`, `[3,4,5]`, `[3,4,5,6,7,8]`, `[3,6]`, `[3,4,6,7]`, `[7,8]`. This is the version to use going forward.

I then ran the repaired quotient-guided exact two-replacement search around **all 815** recorded E11 deficiency-one near misses:

```bash
python scripts/e11_two_replacement_search.py \
  --core data/restricted_cores/mask_001_E11_core.npy \
  --pool data/e11_flip_workspace/data/schemes_modp/e11core/mod2-rank21a.npy \
  --structure data/e11_rank21_pool_structure_full_examples_v2.json \
  --max-nearmisses 1000 \
  --json-out data/e11_two_replacement_search_all_nearmisses_v2.json
```

Result:

- 815 deficiency-one near misses scanned.
- For each, all `C(19,2)=171` choices of two additional surviving columns were removed, giving `815*171=139365` 17-column bases.
- For each 17-column base, all nonzero rank-one `8x9` columns were reduced modulo the base span and the exact small quotient condition `L_E11 <= span(base,x,y)` was tested.
- Target quotient dimensions after the extra two removals were: 137199 bases with quotient dimension 3 and 2166 bases with quotient dimension 2.
- No two arbitrary rank-one columns repaired any base to an exact rank-19 E11 CPD.

Artifact: [e11_two_replacement_search_all_nearmisses_v2.json](../results/e11_two_replacement_search_all_nearmisses_v2.json).

Interpretation: within the union of all rank-21 flip-pool near-miss surfaces sampled in this investigation, a rank-19 E11 decomposition cannot be reached by deleting an equal-W pair and then replacing any two further surviving two-factor columns by arbitrary rank-one columns. This is a much stronger local negative result than the earlier one-replacement search, but it is still not a global lower bound: an E11 rank-19 solution may lie in a different rank-21 neighborhood or not be naturally adjacent to these near misses.
