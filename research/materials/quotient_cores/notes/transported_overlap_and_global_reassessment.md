# transported overlap exclusions and global reassessment of the distinct E11 core

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific purpose

The analysis local repair experiment around the current trace-consistent 9-violation support answered its intended local question: small edits do not repair the remaining Wang occupation failures, and radius six already uses almost the full core table. This ARTIFACT therefore moved the useful certified part of that local work back into the global distinct-support problem.

The active finite-field interface remains the E11 quotient core over \(\mathbb F_2\). Repeated projected A-directions are already excluded, so the remaining support problem is 19 distinct nonzero quotient directions satisfying the complete core Wang occupation table, followed by fixed-A B/C compatibility and exact rank-one completion. No complete-Wang support or rank-19 core decomposition has been found.

## Transported overlap consequence

Let

```text
S = [1,2,3,4,8,20,24,31,32,36,64,73,109,127,128,141,160,182,219].
```

analysis produced a DRAT-verified pure-Wang radius-3 local exclusion around this support. The exact local model says there is no complete-Wang-admissible distinct support \(X\) with

\[
|X\cap S|\ge16.
\]

The verified d=3 proof files are:

- `workspace/data/neighborhood_repair/cnf/current_support_repair_d3.cnf`
- [current_support_repair_d3.meta.json](../../occupation_and_completion/results/neighborhood_repair/cnf/current_support_repair_d3.meta.json)
- [current_support_repair_d3.status.json](../../occupation_and_completion/results/neighborhood_repair/cnf/current_support_repair_d3.status.json)
- CNF SHA256 `a2cfc55f4e3faf27291bb3631de8f73de3a71a528d3af1639238bbbdcdae74b9`
- DRAT SHA256 `21e1d03b0f109fcab8d33b8eb2bcfe681e8dde7eecd8ee5b043fb380e65e6f9f`
- CaDiCaL exit 20 and `drat-trim` VERIFIED

Because the E11 stabilizer acts on the entire support and preserves the complete core Wang occupation table, the local exclusion transports to each whole-support image \(gS\):

\[
\sum_{p\in gS}x_p \le 15.
\]

This is a derived A-support occupation consequence for complete-Wang-admissible distinct supports. It is not a new primitive Wang row, not a B/C completion statement, and not a tensor-rank lower bound by itself. It uses one group element acting on the whole center; point-orbit counts are not a substitute.

## Invariance check added in this ARTIFACT

review correctly pointed out that the transported inequalities require an explicit verification that the enumerated 1152 maps preserve the complete core Wang table. I wrote and ran:

- [wang_invariance_check.py](../code/wang_invariance_check.py)
- output [wang_invariance_check.json](../results/transported_overlap/wang_invariance_check.json)

The check establishes:

- 1152 unique point permutations on the 255 nonzero quotient directions;
- every permutation is induced by a linear map of \(\mathbb F_2^8\);
- 9 selected generators close to exactly the 1152 enumerated permutations;
- for every generator, all 417,199 core subspace rows were transformed and the image key set is exactly the same table with zero \(L\)-mismatches;
- the base support has stabilizer size 1 inside this group, giving 1152 unique whole-support images.

Thus the 1152 transported overlap inequalities are now backed by a concrete table-preservation certificate for the enumerated E11 group.

## Stored near-miss overlap accounting

Script:

- [transported_overlap_analysis.py](../code/transported_overlap_analysis.py)

Output:

- [transported_overlap_analysis.json](../results/transported_overlap/transported_overlap_analysis.json)

Among 23 deduplicated stored distinct supports:

- 5 have max transported overlap at least 16 and lie in the certified radius-3 union;
- 18 lie outside it;
- histogram of max overlap with the 1152 transported centers: 11:3, 12:4, 13:1, 14:6, 15:4, 16:1, 18:3, 19:1;
- all 23 remain Wang-inadmissible, so this is a map of previous search basins, not an estimate of admissible supports.

The supports inside the transported union include the analysis 12-violation near-miss, the analysis trace-inconsistent 9-violation variant, the analysis trace-consistent 9-violation base, and two close old supports. Several earlier supports with low violation counts are outside the union, including a 15-violation and a 16-violation support at max overlap 15. The cut family is therefore useful for preventing rediscovery of the known basin, but it does not make the remaining search small.

## Global search with transported cuts

Script:

- [overlap_cut_separator.py](../code/overlap_cut_separator.py)

### L>=15 plus corrected certificate cuts and 1152 overlap cuts

Output:

- [overlap_cut_separator_L15_cert_3r_180s.json](../results/transported_overlap/overlap_cut_separator_L15_cert_3r_180s.json)

Round 0 produced a new support outside the certified basin:

```text
[2,3,16,20,24,28,31,65,72,96,97,108,114,130,146,159,162,216,252]
```

Exact rescan:

- max overlap with transported centers: 13, hence exchange distance 6 from the base orbit;
- 28 complete Wang violations, all excess 1: 26 with \(L=12\), 2 with \(L=14\);
- passes zero-domain, linear membership, transversality, and size-2 quotient-rank checks;
- has 5 local odd-dependency trace inconsistencies;
- the next separation round returned UNKNOWN after 180.941 s.

This support is not complete-Wang-admissible. Scientifically, it shows that after excluding the known radius-3 orbit, the solver moves to a different basin whose failures are still low-L Wang rows, not to an admissible support.

### L>=14 plus corrected certificate cuts and 1152 overlap cuts

Output:

- [overlap_cut_separator_L14_cert_2r_240s.json](../results/transported_overlap/overlap_cut_separator_L14_cert_2r_240s.json)

Round 0 produced another far support:

```text
[8,18,20,22,24,27,31,64,65,72,73,128,144,160,162,216,219,224,252]
```

Exact rescan:

- max transported overlap: 10, distance 9;
- 44 complete Wang violations: 40 with \(L=12\), 4 with \(L=9\), max excess 2;
- 4 zero-domain terms, 10 transversality failures, and 104 size-2 quotient-rank violations;
- 4 local odd-dependency trace inconsistencies;
- the next separation round returned UNKNOWN after 241.347 s.

This is a weaker construction basin and mainly shows that lowering the initial Wang threshold changes the geometry but does not produce a better candidate.

### Adding all size-5 trace cuts

Output:

- [overlap_cut_separator_L15_cert_size5_1r_300s.json](../results/transported_overlap/overlap_cut_separator_L15_cert_size5_1r_300s.json)

With all 216,576 size-5 local odd-dependency cuts, the round-0 solve returned UNKNOWN after 301.317 s. This gives no exclusion and suggests that simply stacking all local trace cuts is not currently a compact global mechanism.

## Row-orbit structure of the exposed low-L failures

Script:

- [violation_orbit_profile.py](../code/violation_orbit_profile.py)

Output:

- [violation_orbit_profile.json](../results/transported_overlap/violation_orbit_profile.json)

The violated rows are concentrated in a small number of E11 row orbits:

- base 9-violation support: 9 rows lie in 4 row orbits; orbit closure has 696 rows, all \(L=12\), with dimensions 5:408 and 6:288;
- analysis L>=15 support: 28 rows lie in 8 row orbits; closure has 1032 rows, with 1008 \(L=12\) and 24 \(L=14\);
- analysis L>=14 support: 44 rows lie in 7 row orbits; closure has 2040 rows, with 1752 \(L=12\) and 288 \(L=9\);
- union of these closures has 2616 rows.

An orbit-closed separator using the base and L>=15 violation row orbits was then tested:

- script [orbit_closed_separator.py](../code/orbit_closed_separator.py)
- output [orbit_closed_separator_base_L15_2r_180s.json](../results/transported_overlap/orbit_closed_separator_base_L15_2r_180s.json)
- initial rows: all \(L\ge15\) rows plus 1032 orbit-closed low-L rows, plus 1152 overlap cuts and corrected certificate cuts;
- round 0 returned UNKNOWN after 181.046 s.

This is not an exclusion. It indicates that adding the first two exposed low-L row orbit families creates a harder but still unresolved point-level model.

## Legitimate orbit-average relaxation

Script:

- [orbit_average_relaxation.py](../code/orbit_average_relaxation.py)

Output:

- [orbit_average_relaxation.json](../results/transported_overlap/orbit_average_relaxation.json)

The six point orbits were used only for a legal group-averaged necessary relaxation, not as exact support variables. The complete nonvacuous core Wang table compresses to 451 averaged row types. The LP with averaged Wang rows and the averaged transported-overlap inequality is feasible; adding averaged contraction-rank inequalities remains feasible. Integer orbit-profile enumeration over the six counts gives 34,335 possible profiles, of which 15,215 pass the averaged Wang+overlap relaxation and the averaged contraction inequalities.

Therefore first-moment orbit averaging is far too weak for a global proof. The obstruction needs point incidences, higher moments, row-orbit subsystems, colored projection data, or B/C compatibility.

## d=4 local proof task status

The managed d=4 CNF task `s54_t23_tool1` timed out after 2400 s. A status summary was written by:

- [d4_timeout_status.py](../code/d4_timeout_status.py)
- output [d4_partial_status_from_timeout.json](../results/transported_overlap/d4_partial_status_from_timeout.json)

Files present:

- `current_support_repair_d4.cnf`, SHA256 `a2749dc2fc7d2f5fa47251c20f0e07e804b3aafb02a8ebe85f309ccba6b6887d`, 14,773,323 variables and 31,606,964 clauses;
- `current_support_repair_d4.drat`, SHA256 `8d0acdc9293f7fbbff5f18cc608d41ae55ef8acd87a50a9b735613584b4d5df7`, size about 1.50 GB;
- CaDiCaL log contains `UNSATISFIABLE` and exit 20;
- `drat_trim` did not write VERIFIED before timeout.

Thus d=4 is solver-UNSAT with an unverified proof artifact, while d=2 and d=3 remain the replayed certificates.

## Directional reassessment

The local basin around the trace-consistent 9-violation support is not worth extending by larger and larger radii. Radius 6 already uses 405,172 of 417,198 nontrivial rows; d=4 proof replay itself is costly. The durable contribution from that local experiment is the transported overlap family, now backed by a table-invariance check.

The next strongest work should use this cumulative information globally. The best targets are:

1. Extract a compact row-orbit or PB subsystem from the base and analysis low-L row-orbit families. The immediate question is whether a small orbit-closed subsystem can become proof-producing, or whether all such subsystems remain too weak without higher-incidence information.
2. Study the low-L Wang failures structurally through annihilator/weight and colored projection views. The repeated emergence of \(L=12\) dimension-5/6 rows suggests that total occupancy is exposing a projection-distribution problem, but the first-moment orbit relaxation is too coarse.
3. Compute exact colored projection polytopes or small quotient-rank refinements for the relevant \(D=U^\perp\) row orbits, especially the four row orbits from the base support and the new row orbits from the L>=15 overlap-cut support.
4. Test whether current far supports have independent fixed-A rank-one completion failures that can yield guarded family cuts. For the new L>=15 support there are already local trace inconsistencies, so the immediate value is lower; a complete-Wang or trace-consistent far support would be more decisive.
5. Keep alternative quotient cores and construction routes alive, but do not dilute effort unless they preserve the exact bridge to the finite-field rank question or reveal a route to characteristic-zero rank.

The research state remains open: no complete-Wang-admissible distinct support, no rank-19 E11 core decomposition, no rank-22 algorithm, and no proof of \(R_{\mathbb F_2}(T_{\langle3,3,3\rangle})\ge21\) has been obtained.
