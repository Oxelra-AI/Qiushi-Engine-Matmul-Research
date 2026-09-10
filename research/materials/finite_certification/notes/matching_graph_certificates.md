# repaired fixed-matching graph certificates

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Purpose

analysis introduced a useful residual-capacity graph for fixed nonadjacent rank-1 matchings in the Wang \(\mathbb F_2\) occupation route, but its interpretation was unsafe. This note records the repaired evidence state.

For a fixed rank-1 matching \(M\), a Wang row \((\Phi,L)\) has residual capacity
\[
 r(\Phi)=(20-L)-|M\cap\Phi|.
\]
Rows with \(r<0\) directly exclude the matching. Rows with \(r=0\) exclude every higher-rank point in \(\Phi\). Rows with \(r=1\) exclude every pair of surviving higher-rank points in \(\Phi\). A completion would require an independent set of size \(20-|M|\) in the resulting incompatibility graph.

## Corrections to analysis

1. The analysis condition `alpha < target` is only valid when the independent-set search completed. If the search times out, the reported `alpha` is merely the largest independent set found, i.e. a lower bound on the true independence number. The patched script [incompatibility_graph.py](../../quotient_cores/code/incompatibility_graph.py) now distinguishes:
   - `target_independent_set_found`,
   - `exhaustive_vertex_plus_edge_exclusion`,
   - `unresolved_independent_set_search`,
   - direct `matching_violates` and `vertex_exclusion`.
2. A certifying alternative was built: explicit clique covers of the incompatibility graph, equivalently colorings of the complement graph into fewer than `target` color classes. These are checkable upper bounds on the independence number.
3. For large residual-0/1 graphs, the graph independent-set problem is encoded directly as a small CNF with one variable per surviving higher-rank point, edge clauses from residual-1 rows, and an at-least-target cardinality circuit. UNSAT plus `drat-trim VERIFIED`, together with row provenance, certifies the graph bound.

## k=7 matching level

All six anchored nonadjacent matching strata with \(k=7\) are now closed as **A-side Wang support conditions over \(\mathbb F_2\)**:

- Direct row violations:
  - idx 32, matching `[1,16,27,256,325,432,511]`, row key `573979715964934`, lb 14, cap 6, matching count 7.
  - idx 37, matching `[1,16,36,192,360,438,455]`, row key `296129345281364071`, lb 14, cap 6, matching count 7.
- Explicit clique-cover certificates:
  - idx 33, matching `[1,16,27,256,325,438,504]`: 82 survivors, target 13, 10 color classes; verified 354 intra-class edge rows.
  - idx 34, matching `[1,16,27,256,360,390,511]`: 82 survivors, target 13, 11 color classes; verified 341 intra-class edge rows.
- Graph-IS CNF/DRAT certificates:
  - idx 35, matching `[1,16,27,256,360,438,455]`: 236 survivors, target 13, 19,930 edge clauses, CNF 3,135 vars / 25,518 clauses; CaDiCaL UNSAT and `drat-trim` verified.
  - idx 36, matching `[1,16,36,192,360,390,511]`: same graph size and verified UNSAT status.

Important files:

- patched exploration script: [incompatibility_graph.py](../../quotient_cores/code/incompatibility_graph.py)
- certificate generator: [graph_coloring_certificate.py](../code/graph_coloring_certificate.py)
- explicit certificate checker: [verify_graph_certificate.py](../code/verify_graph_certificate.py)
- graph-IS CNF encoder: [graph_is_cnf.py](../../quotient_cores/code/graph_is_cnf.py)
- graph-IS provenance checker: [verify_graph_is_cnf.py](../../quotient_cores/code/verify_graph_is_cnf.py)
- strict regenerated-clause checker: [strict_verify_graph_is_cnf.py](../../quotient_cores/code/strict_verify_graph_is_cnf.py)
- k=7 explicit certificates: [summary_k07.json](../../quotient_cores/results/graph_cert/k7_rerun/summary_k07.json)
- direct verification of four explicit certificates: [verification_k7_certified.json](../../quotient_cores/results/graph_cert/k7_rerun/verification_k7_certified.json)
- k=7 graph CNFs: [summary.json](../../quotient_cores/results/graph_cert/k7_graph_is_cnf_with_vex/summary.json)
- strict graph-CNF verification: [strict_verification_graph_is_cnf.json](../../quotient_cores/results/graph_cert/k7_graph_is_cnf_with_vex/strict_verification_graph_is_cnf.json)
- patched analysis rerun: [k7_patched_result.json](../../quotient_cores/results/graph_cert/k7_patched_result.json)

This is not a proof of \(R_{\mathbb F_2}\ge21\): it covers only the nonadjacent matching branch at \(k=7\). The adjacent-pair branch and matching \(k\le6\) remain open.

## k=6 pilot

Using only residual-0/1 consequences, four of ten \(k=6\) strata have explicit clique-cover certificates:

- idx 22: 68 survivors, target 14, 7 color classes.
- idx 23: 147 survivors, target 14, 13 color classes.
- idx 24: 147 survivors, target 14, 13 color classes.
- idx 28: 147 survivors, target 14, 13 color classes.

These four were checked by [verify_graph_certificate.py](../code/verify_graph_certificate.py); see [verification_k6_color_certs.json](../../quotient_cores/results/graph_cert/k6_color_pilot/verification_k6_color_certs.json).

For the six remaining \(k=6\) strata (idx 25,26,27,29,30,31), graph-only CNFs are SAT, not UNSAT. Model-output reruns decoded target-size independent sets of 14 higher-rank points for each. Full-LUT scans of the resulting 20-point supports found thousands of violations:

- idx 25: 10,105 violations, max excess 6.
- idx 26: 9,805 violations, max excess 4.
- idx 27: 7,500 violations, max excess 4.
- idx 29: 8,203 violations, max excess 5.
- idx 30: 12,326 violations, max excess 6.
- idx 31: 7,804 violations, max excess 4.

The decoded supports and violation heads are in [decoded_sat_supports_full_lut_scan_with_models.json](../../occupation_and_completion/results/graph_cert/k6_graph_is_cnf/decoded_sat_supports_full_lut_scan_with_models.json).

A residual-2 profile shows that the remaining \(k=6\) strata have hundreds of thousands of compressed residual-2 masks after vertex exclusions, e.g. idx 25 has 514,014 residual-2 compressed masks and idx 30 has 633,473. This means the next representation must compress or learn higher-residual constraints intelligently rather than adding all ternary clauses naively. See [k6_residual2_profile.json](../../quotient_cores/results/graph_cert/k6_residual2_profile.json).

## Scientific state

The graph route is promising because it converted the two previously hard \(k=7\) fixed-matching leaves from 219k-variable sequential-counter Wang CNFs into 236-vertex graph CNFs that replayed with DRAT verification in seconds. It also gave directly checkable clique covers for several strata.

However, the strict global state is unchanged: no rank-22 algorithm, no rank-23 optimality proof, and no proved \(R_{\mathbb F_2}\ge21\). The current result is a verified support-side exclusion for one matching level plus partial progress at \(k=6\). The next work should extend the certificate framework to residual \(\ge2\) constraints or find a different compact obstruction for the lower matching levels, while keeping the adjacent-pair branch separate.
