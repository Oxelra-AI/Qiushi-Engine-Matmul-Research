# E11 quotient action and occupation-guided SAT surface

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

The active finite-field constructive route is still:

\[
R_{\mathbb F_2}(\mathrm{E11\ core}) \le 19
\quad\Longrightarrow\quad
R_{\mathbb F_2}(T_{333}) \le 22,
\]

using the exact +3 lift verified in analysis. analysis focused on making the A-side orbit compression mathematically correct and replacing generic MIP extension by an exact support-enumeration + fixed-A SAT surface.

## Correct E11 quotient action

The E11 A-factors live in the quotient by the killed line \(\langle E_{00}\rangle\), not in a fixed complement. For decomposition covectors the full isotropy acts by

\[
U\mapsto P^TUQ^{-T},\qquad V\mapsto Q^TVR^{-T},\qquad W\mapsto P^{-1}WR.
\]

This induces an action on \(A/\langle E_{00}\rangle\) iff

\[
P^T E_{00}Q^{-T}=E_{00},
\]

equivalently over \(\mathbb F_2\),

\[
\operatorname{row}_0(P)=e_0^T,\qquad \operatorname{col}_0(Q)=e_0.
\]

I wrote [e11_quotient_action_verify.py](../../quotient_cores/code/e11_quotient_action_verify.py) to rebuild this action from explicit generators, compare generator closure with direct enumeration, verify quotient well-definedness, verify preservation of the E11 core tensor for all pairs, and compute the point orbits.

Key output: [e11_quotient_action_verification.json](../../quotient_cores/results/e11_quotient_action/e11_quotient_action_verification.json).

Checked facts:

- \(|GL(3,2)|=168\).
- Correct \(P\)- and \(Q\)-subgroups each have 24 elements.
- Explicit generator closures equal direct enumerations.
- The direct product gives 576 distinct quotient permutations.
- The permutation closure from generators equals the explicit 576 pairs.
- Every permutation fixes zero and bijects the 255 nonzero quotient points.
- For each quotient class, representatives \(U\) and \(U+E_{00}\) have the same image class under every pair: no well-definedness failures.
- With \(R=I\), all 576 pairs preserve the E11 8x9x9 core tensor coordinatewise.
- Correct point-orbit sizes are
  \[
  3,3,9,36,36,36,36,96.
  \]
- The old complement-preserving action produces
  \[
  6,9,12,12,36,36,72,72,
  \]
  and must not be used for E11 quotient compression.
- The saved permutation array has shape `(576,256)`, dtype `uint16`, and raw sha256 `a33def2e4f331c3df373f99db20a1eb4d205ebfcb80a0ce6bbe76576957ef019`.

review independently confirmed this correction and added the block-form classification: writing

\[
P=\begin{pmatrix}1&0\\p&A\end{pmatrix},\quad
Q=\begin{pmatrix}1&q^T\\0&B\end{pmatrix},\quad
U=\begin{pmatrix}0&x^T\\y&Z\end{pmatrix},
\]

the quotient action gives

\[
Z'=A^TZB^{-T},\quad x'^T=(x^T+p^TZ)B^{-T},\quad y'=A^T(y+Zs),\ s=B^{-T}q.
\]

This yields the orbits: for \(Z=0\), sizes \(3,3,9\); for rank-1 \(Z\), four size-36 orbits distinguished by row/column membership of \(x,y\); for rank-2 \(Z\), one size-96 orbit.

## Code repair

`e11_orbit_search.py` was patched so its A-quotient action now uses the correct row/column conditions. Its corrected run at [e11_orbit_search_corrected_output.json](../../quotient_cores/results/e11_quotient_action/e11_orbit_search_corrected_output.json) reproduces the same A-orbit sizes. Any old files using sizes `6,9,12,12,36,36,72,72` remain exact only for the listed raw supports and have no quotient-orbit coverage meaning.

## Complete occupation model status

The complete E11 Wang occupation cache is in `data/e11_capacity_sat/e11_capacity_cache.pkl` with summary `e11_capacity_cache.summary.json`:

- 417,199 subspaces of \(\mathbb F_2^8\) (all dimensions 0--8).
- Derived from research_record's complete T-level Wang LUT of 8,283,458 subspaces with `coverage_ok=true`, `conflict_count=0`.
- At rank 19 the capacity distribution is: cap 0: 1, cap 1: 687, cap 2: 34,664, cap 3: 83,046, cap 4: 138,902, cap 5: 81,540, cap 6: 8,130, cap 7: 61,232, cap 8: 865, cap 10: 7,520, cap 13: 578, cap 16: 33, cap 19: 1.
- Singleton caps: 249 points cap 1, 6 points cap 2. The six cap-2 quotient points are `[1,2,3,4,32,36]` in the support-enumerator coordinates.

The full CP-SAT MIP from analysis ([result.json](../results/e11_complete_capacity/result.json)) reached `UNKNOWN` after 1800s. The LP relaxation is feasible, so the occupation system is not cut off by linear relaxation. This is not a proof of occupation feasibility or infeasibility.

The analysis lazy CP-SAT support run `main_lazy_incremental_sat_results.json` added complete-Wang violated cuts for five candidates and then hit `UNKNOWN` after 60s at 13,991 cuts. No complete occupation-feasible support reached fixed-A SAT in that run.

## Incremental SAT-oriented support enumeration

I built [e11_occupation_sat_enumerator.py](../../quotient_cores/code/e11_occupation_sat_enumerator.py). It represents A occupation directly with Boolean occurrence variables: one `y_p` for each point and a second `z_p` only for the six cap-2 points, with total occurrence 19. It adds Wang subspace capacities as CNF cardinality constraints and lazily scans all 417,199 cached subspaces. When a candidate passes all Wang cuts, it canonicalizes the 19-multiset under the corrected 576 common quotient permutations and calls the exact fixed-U SAT layer.

Pilot runs:

- `quick_probe_results.json`: with only dim<=2 cuts, first support solved instantly and had 879 complete-Wang violations.
- `cap2_probe_results.json`: initializing all cuts with cap<=2 gave 35,878 cuts; three supports still had 609, 468, 277 violations.
- `cap3_probe_results.json`: initializing all cuts with cap<=3 gave 118,399 cuts; three supports still had 318, 86, 105 violations. Search time per support rose to roughly 1s, 18s, 50s.

A longer cap<=3 run was submitted as background task `s8_t47_tool1`:

```bash
python -u scripts/e11_occupation_sat_enumerator.py \
  --initial-max-dim 2 --initial-max-cap 3 --max-iters 30 --max-cuts-per-iter 3000 \
  --fixed-u-timeout 180 \
  --json-out data/e11_occupation_sat/cap3_main_results.json \
  --outdir data/e11_occupation_sat/cap3_main
```

It should be collected next. It may find a complete occupation-feasible support, prove UNSAT for the CNF support model with the added cuts, or hit another solver limit. Any `OCCUPATION_INFEASIBLE_FOR_ADDED_CUTS` result is meaningful only if the added cuts are a subset of the cached complete Wang constraints, which the script records by cache index.

A previous long run `s8_t33_tool1` was cancelled after it was superseded by the cap<=3 initialization. Its tail showed the all-CNF enumerator worked and added violations rapidly for five supports; no fixed-U support was tested.

## Fixed-U SAT controls and lift execution

`fixed_u_core_sat.py` was patched to decode SAT solver models and independently verify returned factor masks. Positive control:

```bash
python scripts/fixed_u_core_sat.py \
  --source pool --row 0 \
  --outdir data/e11_capacity_sat \
  --name fixed_u_rank21_poolrow0_control_decoded \
  --solve --solver kissat --timeout 120
```

Output `fixed_u_rank21_poolrow0_control_decoded.json`:

- Known rank-21 E11 pool row verifies with diff 0.
- Fixed-U SAT is `SAT` in about 21s.
- Decoded solver model verifies the E11 core with diff 0.
- Saved decoded core solution at `fixed_u_rank21_poolrow0_control_decoded.solution.npz`.

I also wrote `e11_core_solution_lift.py`, a generic exact lift/verifier from an E11 core `.npz` to full \(T_{333}\). Running it on the rank-21 positive-control core solution produced a verified full rank-24 scheme at `fixed_u_rank21_poolrow0_control_lift.full_t333.npz` with diff 0. The same script should be run immediately if a rank-19 core solution appears.

## Interpretation

This ARTIFACT does not solve the original rank problem. It repairs the orbit algebra and builds reusable exact execution surfaces. The E11 rank-19 route remains alive but difficult: Wang occupation constraints alone have not resolved feasibility, and no complete occupation-feasible support has yet been tested by fixed-U SAT in analysis. The immediate next scientific work is to collect `s8_t47_tool1`, inspect whether it reached complete occupation supports or infeasibility, and, if needed, refine support enumeration using the corrected quotient permutations and cached cuts rather than extending generic CP-SAT time blindly.
