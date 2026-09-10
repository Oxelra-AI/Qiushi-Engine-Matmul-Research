# Explore: Wang root certificate, restricted-core reframing, and exact tangent correction

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

research: research_record. Active goal remains the exact tensor rank of `T_<3,3,3>`: either an exact rank <=22 algorithm or a rigorous lower-bound/rank-23 optimality result over a stated field or algebraic structure.

This note records what analysis actually changed. It is not a final result.

## 1. Wang F2 lower-bound certificate: what the 511 root proof does and does not say

Source code read through `qiushi-matmul source exec tensor-rank-lower-bound`:

- `search/rank_lower_bound_backtracking.h`
- `search/rank_lower_bound_computer.h`
- `search/rank_lower_bound_main.cc`
- `core/constraints.h`
- `core/rank_lower_bound_flatten.h`
- `core/rank_lower_bound_forced_product.h`
- `problems/matrix/problem.h`
- `problems/matrix/symmetry.h`
- `run.py` lines around the matrix `3,3,3` call

### Algorithmic interpretation

For a constrained A-side subspace `Phi <= (F2^9)^*`, Wang's substitution/backtracking proves statements of the form

\[
R(T|_\Phi) \ge |S| + L(\langle \Phi, S\rangle),
\]

where `S` is a set of additional A-side linear functionals. Equivalently, for any rank-`r` decomposition of a tensor with current constraints `Phi`, the number of summands whose A-factor lies in a further subspace/annihilator is limited by the lower bound of the further restricted tensor. The code encodes this by enumerating `minimal_constraints_`, checking all subsets of the current DFS path, and recording a proof ARTIFACT as soon as `popcount(mask)+1+value.rank` reaches the target.

For the unconstrained root orbit (`index 495`) in the published certificate:

```text
constrained_tensors {
  index: 495
  rank_lower_bound: 20
  rank_lower_bound_proof {
    backtracking_proof { proof_size: 511 }
  }
}
```

Over `F2^9` there are exactly 511 nonzero A-side linear functionals. The code's first root improvement from known lower bound 19 to target 20 is immediate once every codimension-one restriction orbit has certified lower bound 19. The certificate has exactly three one-dimensional restriction orbits, all with lower bound 19, represented by masks:

- `1` = `E11`
- `10` = `E12 + E21`
- `84` = `E13 + E22 + E31`

Therefore the 511-record root proof is best read as a complete projective sweep over all nonzero A-functionals, using the fact that each codimension-one restricted tensor has rank at least 19.

### What it does not encode

The stored root proof does **not** record a failed or complete attempt to improve the root from 20 to 21. `ProcessOrbit` would run a second `RankLowerBoundBacktracking::Search` after the 19->20 improvement, now with `known_rank_lower_bound = 20` and target 21. Since the final certificate remains 20, no successful 20->21 proof is stored. The code and certificate do not tell whether that later attempt exhausted its search tree or stopped because of finite budget / local weakness.

The repository `run.py` shows the published `matrix_q02_n333` generation was configured with finite search parameters:

```python
lb_args = {
    "backtracking_step_limit": 10_000_000,
    "forced_product_max_iterations_log2": 32,
}
search_matrix(2, 1, 3, 3, 3, lb_args, None, ub_args)
```

Thus absence of a 21 proof in the certificate is not evidence that Wang's single-factor occupation table is intrinsically unable to prove 21, unless a separate exhaustive root-level replay is performed. A quick attempt to run a root-only compiled replay from inside `source exec` failed with exit code 127 and produced empty output files (`root_probe_dim0_out.pb.txt`, `root_probe_dim0_out.btp`); this was a command/toolchain-path failure, not a mathematical result. Do not infer anything from it.

## 2. Restricted-core reframing: the three central 8x9x9 tensors

The strongest object exposed by Wang's certificate is not the full 9x9x9 tensor alone, but the three codimension-one A-side restricted tensors represented by the one-dimensional restriction orbits above. Each has certified rank lower bound 19 over `F2`, and improving any of them to lower bound 20 would immediately raise the full tensor lower bound to at least 21 by the 511-nonzero-functional root sweep.

Wang's `ApplyConstraintsToTensor` applies a constraint row to the A-mode. For a row with pivot coordinate `p` and free coordinates `i`, over `F2` it folds the pivot A-slice into every free coordinate with row coefficient 1, then zeros the pivot slice. Thus the restricted tensor is a 9x9x9 coordinate tensor with one zero A-coordinate; equivalently, after deleting the zero pivot coordinate it is an 8x9x9 tensor on the hyperplane `row(A)=0`.

Concrete representatives in row-major A-coordinate masks:

1. `E11` mask `1`:
   - constraint `a11=0`; pivot bit 0; zeroed/folded A-slice `a11` (no free additions).
2. `E12+E21` mask `10` (`0b000001010`):
   - pivot bit 3 (`a21`) because Wang uses highest-bit pivot; relation `a21 = a12` over F2; fold slice `a21` into slice `a12`, then zero `a21`.
3. `E13+E22+E31` mask `84` (`0b001010100`):
   - pivot bit 6 (`a31`); relation `a31 = a13 + a22`; fold slice `a31` into slices `a13` and `a22`, then zero `a31`.

These are the semantic cores to hand to search/proof work: try to prove `R_F2(core) >= 20`, or search for exact length-19/20 decompositions of these cores and understand their structure. If a length-19 exact decomposition is found for a representative, Wang's lower bound 19 would be tight for that core; if none exists under strong enough exact search/proof methods, a 20 lower bound may be reachable.

For a hypothetical rank-22 full algorithm over `F2`, applying the missing-slice/substitution identity around a codimension-one restriction gives a decomposition of one of these cores with length between roughly 19 and 21 plus a residual contribution from the summands whose A-factor is not in the hyperplane. The residual A-side complement is 1-dimensional, so after fixing the complement coordinate it contributes a `B⊗C` matrix of rank at most the number of escaped summands. This yields smaller semantic search surfaces than raw Challenge 4: length-19..21 decompositions of the three cores together with a low-rank residual 9x9 matrix/slice compatibility condition.

## 3. Single-factor occupation probes from the current Wang table

Scripts produced/used:

- [wang_occupation_search.py](../../quotient_cores/code/wang_occupation_search.py)
- [verify_occupation_candidate.py](../../quotient_cores/code/verify_occupation_candidate.py) (streaming verifier; too slow in Python for all dimensions as written)

`wang_occupation_search.py` uses exact `F2` subspace arithmetic and closes certificate representatives under `GL(3,2) x GL(3,2)` plus transpose according to `problems/matrix/symmetry.h`. It searches for a 20-point set of projective A-factors satisfying all currently loaded subspace caps

\[
|P \cap S| \le 20 - L(S).
\]

Pilot results:

- Dim <= 1: [occupation_dim1.json](../../quotient_cores/results/wang_occupation/occupation_dim1.json); 20-point escape exists.
- Dim <= 2 with transpose closure: [occupation_dim2_transpose.json](../../symmetry_and_residuals/results/wang_occupation/occupation_dim2_transpose.json); 43,947 unique low-dimensional subspaces generated from the 18 reps; 20-point escape exists, no violations within loaded constraints, 174 tight dimension-2 constraints.
- Dim <= 3 with transpose closure: [occupation_dim3_transpose_pilot.json](../../symmetry_and_residuals/results/wang_occupation/occupation_dim3_transpose_pilot.json); 831,982 unique subspaces generated from the 86 reps; 20-point escape exists, no violations within loaded constraints, 346 tight dimension-3 constraints.

These are **not** a proof that the full single-factor table cannot certify 21. They show only that constraints through dimension 3 do not already force a contradiction. A full-table Python streaming check against all dimensions timed out after 900 seconds with no output, so it is not evidence either way. The next useful exact computational action is either (a) use Wang's compiled `rank_lower_bound_main` root-only replay with a high/controlled ARTIFACT limit, if the build/toolchain path can be fixed, or (b) implement an optimized C++/bitset full occupation verifier/search that uses orbit caps without expanding all high-dimensional subspaces naively.

## 4. Exact tangent-space correction at rank-23 decompositions

Scripts produced/used:

- [exact_modular_tangent.py](../code/exact_modular_tangent.py)
- [find_correct_stabilizer_action.py](../../quotient_cores/code/find_correct_stabilizer_action.py)
- [exact_intrinsic_tangent.py](../code/exact_intrinsic_tangent.py)

The initial peer report from research_record claimed symmetry dimension 71 and complete second-order obstruction at three rank-23 decompositions. analysis independently found the same flaw research_record later reported: the guessed sandwich directions used in their first scripts are not all in the Jacobian kernel. Direct convention tests (`stabilizer_convention_probe.json`) showed nonzero `J D` image ranks for both primal/dual and output/trace guessed formulas.

The robust repair was to compute the Lie stabilizer intrinsically from the verified tensor itself by solving

\[
(X_A\otimes I\otimes I + I\otimes X_B\otimes I + I\otimes I\otimes X_C)T = 0
\]

over finite fields. Applying that stabilizer basis to the decomposition terms gives convention-free tangent directions.

Exact modular results saved in `data/cn122_tangent_exact_probe/`:

### cn122 ([scheme-47fa58e6cd.qmm](../../exact_baselines/results/cn122_3x3_r23_repro/scheme-47fa58e6cd.qmm))

`intrinsic_tangent_dims.json`, over primes 2,3,5,7,101:

- Jacobian rank = 527, kernel dimension = 94 for all tested primes.
- Intrinsic tensor Lie stabilizer dimension = 26 for all tested primes.
- Per-term rescaling span rank = 46 and all rescaling directions lie in `ker J`.
- Stabilizer parameter-direction span rank = 26 and all lie in `ker J`.
- Combined rescaling + intrinsic stabilizer span rank = 70.
- Residual tangent dimension = 24.

This corrects the earlier peer number 71/23 for cn122 to 70/24.

### serendipitous_8d34 and naive_c88 from research_record

Peer supplied hashes were independently checked:

- `data/fmm_r23_schemes/serendipitous_8d34.qmm`, sha256 `5e274f6a5d8f742baaa55ebf75f2c20fe23c7b75f364e911a0d787bb6eb3739e`.
- `data/fmm_r23_schemes/naive_c88.qmm`, sha256 `fd96e482fafbf2fb3abf4f98bc8889af08bb67e60aae4828da28b2292be21224`.

Using `exact_intrinsic_tangent.py` over `F_101`:

- `serendipitous_8d34`: Jacobian rank 531, kernel dimension 90, combined symmetry span 70, residual dimension 20. Saved at `serendipitous_intrinsic_tangent_p101.json`.
- `naive_c88`: Jacobian rank 528, kernel dimension 93, combined symmetry span 70, residual dimension 23. Saved at `naive_c88_intrinsic_tangent_p101.json`.

These agree with the peer's corrected qualitative direction that symmetry rank is 70, not 71, but give exact modular dimensions rather than float64 SVD dimensions. The corrected Kuranishi analysis states the earlier universal obstruction was false: coker equations collapse to 15 effective quadratics in residual variables, random starts find solutions, and the local deformation family is positive-dimensional. That revised result is plausible but has not yet been independently reproduced by research_record with exact or high-precision Kuranishi computations.

## 5. Immediate scientific consequences

1. The main lower-bound opportunity exposed by Wang is now sharply focused: prove any one of the three codimension-one restricted `8x9x9` cores has `F2` rank at least 20. This would lift the full `T_<3,3,3>` lower bound over `F2` from 20 to 21 through the already-certified root projective sweep.
2. The existing Wang root certificate alone is only a 19->20 lift; its absence of a 21 proof is not conclusive because generation used finite `10,000,000`-ARTIFACT backtracking. The full single-factor occupation problem remains open from this ARTIFACT's evidence.
3. The tangent/deformation route changed direction: rank-23 decompositions are not locally rigid by the peer's corrected Kuranishi result, and exact intrinsic first-order dimensions show larger residual spaces than the original report. This weakens any rank-23 optimality intuition based on local obstruction and makes it more interesting to search within rank-23 deformation families for routes to pairing-rank-defect or to a rank-22 limit.
4. A semantic search around the restricted cores is a better next surface than blind Challenge 4: it is smaller, directly tied to a possible finite-field lower-bound improvement, and can also reveal rank-22 upper-bound structure if core decompositions plus residual slices assemble unexpectedly.

## 6. Files created or changed in analysis

Scripts:

- [exact_modular_tangent.py](../code/exact_modular_tangent.py)
- [find_correct_stabilizer_action.py](../../quotient_cores/code/find_correct_stabilizer_action.py)
- [exact_intrinsic_tangent.py](../code/exact_intrinsic_tangent.py)
- [wang_occupation_search.py](../../quotient_cores/code/wang_occupation_search.py) (repaired RREF and transpose closure)
- [verify_occupation_candidate.py](../../quotient_cores/code/verify_occupation_candidate.py)

Data:

- [intrinsic_tangent_dims.json](../../exact_baselines/results/cn122_tangent_exact_probe/intrinsic_tangent_dims.json)
- [modular_tangent_dims_v2.json](../../exact_baselines/results/cn122_tangent_exact_probe/modular_tangent_dims_v2.json)
- [stabilizer_convention_probe.json](../../exact_baselines/results/cn122_tangent_exact_probe/stabilizer_convention_probe.json)
- [serendipitous_intrinsic_tangent_p101.json](../../exact_baselines/results/cn122_tangent_exact_probe/serendipitous_intrinsic_tangent_p101.json)
- [naive_c88_intrinsic_tangent_p101.json](../../exact_baselines/results/cn122_tangent_exact_probe/naive_c88_intrinsic_tangent_p101.json)
- [occupation_dim1.json](../../quotient_cores/results/wang_occupation/occupation_dim1.json)
- [occupation_dim2_transpose.json](../../symmetry_and_residuals/results/wang_occupation/occupation_dim2_transpose.json)
- [occupation_dim3_transpose_pilot.json](../../symmetry_and_residuals/results/wang_occupation/occupation_dim3_transpose_pilot.json)

Cautionary failed/empty files from an execution-path error:

- `data/wang_f2_lb20/root_probe_dim0_out.pb.txt` (empty)
- `data/wang_f2_lb20/root_probe_dim0_out.btp` (empty)

Do not use the empty root-probe outputs as evidence.
