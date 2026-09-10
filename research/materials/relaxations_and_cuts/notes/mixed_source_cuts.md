# mixed-source support cuts from projection leakage

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Mathematical object

Starting from the analysis projection inequality, for a target contraction \(\mu\), a B-side source \(\lambda\), and a C-side source \(\nu\), with
\[
K=r_\mu+r_\lambda+r_\nu-d_B(\lambda,\mu)-d_C(\nu,\mu),
\]
adding the B and C projection bounds and using \(e_B(\mu)+e_C(\mu)\le m_\mu-r_\mu\) gives the direct support inequality
\[
 m_\lambda+m_{\lambda+\mu}+m_\nu+m_{\nu+\mu}\ge 2K.
\]
Here \(m_0=0\) when a source equals the target.  For a distinct support variable \(x_p\), the half-left side is
\[
\sum_p c_p x_p\ge K,
\]
where \(c_p=1\) if \(\mu(p)=1\), and \(c_p=\lambda(p)+\nu(p)\) as an ordinary integer if \(\mu(p)=0\). Thus every coefficient is 0, 1, or 2. This cut is an unconditional support restriction; it does not introduce final-tightness variables.

The coefficient is positive exactly for points outside \(D^\perp\), where \(D=\operatorname{span}\{\lambda,\mu,\nu\}\). Hence the mixed-cut left side is at least the number of support points active on \(D\). The canonical Wang row for \(D^\perp\) gives at least \(L(D)\) active points, so the mixed cut is already implied by that single row whenever \(L(D)\ge K\).

## Files produced

- [mixed_source_cuts.py](../code/mixed_source_cuts.py): constructs mixed-source cuts, compares them with the single Wang row for \(D\), scans L15/analysis, enumerates global single-row domination, and exports unique non-single-dominated coefficient patterns.
- [dlocal_wang_implication.py](../../quotient_cores/code/dlocal_wang_implication.py): tests whether all Wang rows living inside \(D\) imply a selected cut by exact enumeration of the pattern-count problem for \(\dim D\le 3\).
- [wang_lp_cut_compare.py](../../quotient_cores/code/wang_lp_cut_compare.py): minimizes selected cut left sides over the linear relaxation of all complete Wang rows.
- [lazy_mixed_cut_dfs.py](../../quotient_cores/code/lazy_mixed_cut_dfs.py) and `lazy_mixed_cut_dfs_fast.py`: timeout-limited DFS pilots using cap-≤2 Wang rows and direct mixed cuts as partial-support upper-bound pruning.
- [direct_mixed_cut_cpsat.py](../../quotient_cores/code/direct_mixed_cut_cpsat.py): CP-SAT model adding direct mixed cuts to reduced or complete Wang occupation models.
- Data are under `workspace/data/mixed_source_cuts/`.

## near-support comparison

For the best B/C source pairs that caused analysis violations:

- L15 has three best-pair mixed cuts. One has \(K=12=L(D)\) and is the same obstruction as a violated Wang row: support active-on-\(D\)=11 < 12, equivalently occupancy in \(D^\perp\) is 8 with capacity 7. The other two have \(K=15\), \(L(D)=12\), and are not implied by the single \(D^\perp\) Wang row; L15 has left side 14, active-on-\(D\)=13, one coefficient-2 selected point, and no violation of the single Wang row.
- analysis has two best-pair mixed cuts. One has \(K=12=L(D)\) and is a Wang-row violation. The other has \(K=15\), \(L(D)=12\), left side 14, active-on-\(D\)=13, and no violation of the single Wang row.

Exact file: [known_best_pair_dominance.json](../results/mixed_source_cuts/known_best_pair_dominance.json).

Scanning all violated mixed-source cuts on those supports gives:

- L15: 44 violated mixed cuts; 16 single-row dominated and 28 not single-row dominated. The non-dominated ones all have gap \(K-L(D)=3\).
- analysis: 24 violated mixed cuts; 16 single-row dominated and 8 not single-row dominated. The non-dominated ones all have gap 3.

Exact file: [known_all_mixed_cut_violations.json](../results/mixed_source_cuts/known_all_mixed_cut_violations.json).

## D-local Wang comparison

For the non-single-dominated analysis best cuts, I enumerated the tiny pattern-count problem over \(D\) with all Wang lower bounds for nonzero subspaces \(E\le D\):

- The single-row dominated \(K=12\) cuts are also implied by the \(D\)-local Wang family; their local minimum left side is 12.
- The \(K=15,L(D)=12\) cuts are not implied by the \(D\)-local Wang family. The local minimum left side is 13 while the mixed cut requires 15. The actual L15/analysis supports satisfy those \(D\)-local Wang inequalities but have left side 14.

The all-violation scan agrees: every gap-0 violated cut is \(D\)-local implied; every gap-3 violated cut in L15/analysis is not \(D\)-local implied. Exact files: `dlocal_implication_best_pairs.json` and `dlocal_implication_known_violations.json`.

## Global single-row domination census

Over all \(\mu\) of quotient rank 1 or 2 and all nonzero \(\lambda,\nu\) sources, there are 11,899,575 source triples. The single \(D^\perp\) Wang row dominates 11,015,847 of them. The remaining 883,728 have \(K>L(D)\), with gap histogram
\[
\{1:243216,\ 2:32256,\ 3:602496,\ 6:5760\}.
\]
After merging identical coefficient patterns and keeping the strongest \(K\) for each pattern, there are 133,110 unique non-single-dominated patterns: gap 1: 37,854; gap 2: 7,056; gap 3: 86,760; gap 6: 1,440. The exported top-50k JSON contains all 1,440 gap-6 patterns and many gap-3 patterns.

Exact files: `global_mixed_cut_dominance.json` and `unique_nondominated_cuts_top50k.json`.

## Complete-Wang LP and integer search comparison

For the three non-single-dominated analysis best cuts, minimizing over the linear relaxation of all 417,197 nontrivial complete Wang rows gives optimum 13 for each, below \(K=15\). Thus these cuts are not consequences of the Wang linear relaxation. This does not settle whether complete Wang plus integrality implies them. A CP-SAT attempt to minimize the same three cuts over all complete-Wang-admissible distinct 19-point supports returned `UNKNOWN` for each 120-second run and produced no integer witness.

For three top gap-6 cuts of the form \((\mu,\lambda,\nu)=(1,48,48),(1,50,50),(1,52,52)\), the complete-Wang LP optimum is numerically 15, matching \(K=15\). An exact pattern-count check over \(D\) shows these are implied by the \(D\)-local Wang family despite not being implied by the single \(D^\perp\) row.

Exact files: `wang_lp_cut_compare.json`, `cut_independence_cp.json`, and `wang_lp_cut_compare_topgap.json`.

## Partial-support pruning pilots

The direct mixed cuts do improve partial-support pruning relative to the previous eB/eC budget variables. With first point fixed to 1 and only cap-≤2 Wang rows loaded, the analysis DFS without direct cuts found 331,858 complete cap-≤2 leaves in 60 seconds and no leakage pruning. The vectorized analysis DFS with the 1,440 gap-6 direct cuts explored 64,730 nodes in 60 seconds, recorded 169,393 mixed-cut prunes, and stored only 20 of 22,276 leaves. Pruning begins at depths 15–19. A second run using 2,000 gap-3 non-equal-source patterns recorded 78,000 mixed-cut prunes and 107,647 leaves in 60 seconds. These are timeout-limited branch pilots with only a cut subset, so they are evidence about propagation, not coverage.

CP-SAT with direct cuts remains undecided: reduced Wang + 50,000 direct cuts returned `UNKNOWN` in 120 seconds; complete Wang + the 1,440 gap-6 cuts returned `UNKNOWN` in 120 seconds.

Exact files: `lazy_mixed_cut_dfs_fast_gap6_2k.json`, `lazy_mixed_cut_dfs_fast_gap3_nondlocalheur2k.json`, `direct_mixed_reduced120_top50k.json`, and `direct_mixed_complete120_gap6_10k.json`.

## Scientific meaning for the E11 route

The projection geometry does supply real support restrictions not visible in a single Wang row, and for the L15/analysis near-supports some of the old violations are better understood as mixed B/C source conflicts rather than only occupation excess. The LP evidence shows at least three analysis cuts are not implied by the Wang linear relaxation. At the same time, many visually strong gap-6 cuts are implied by a small family of Wang rows inside the same dual span, so gap above a single row is not by itself independent information. The useful next work is to separate genuinely new mixed-source cuts from Wang-combination consequences and use the remaining cuts in a coverage-preserving branch or PB/SAT proof architecture. The current computations have not produced a rank-19 E11 core and have not excluded the distinct nineteen-direction branch.
