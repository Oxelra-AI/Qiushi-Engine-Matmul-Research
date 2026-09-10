# defect/leak-duality refinement of E11 block-spread

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Object and convention

Field: \(\mathbb F_2\).  E11 core slice convention remains the corrected analysis convention
\[
T[3i+j,3j+k,3i+k]=1.
\]
After deleting the \(a=0\) slice, core slice \(s=a-1\) with \(a=3i+j\) occupies the contiguous block
\[
R_j\times C_i,
\qquad R_j=C_j=\{3j,3j+1,3j+2\},
\]
and equals \(I_3\) there, with zero on the other eight \(3\times3\) blocks.

## Lemma: defect budget for a slice

Fix one slice \(s\), let its own block be \(R_j\times C_i\), and let \(S_s\) be the active terms in a putative exact decomposition.  Write \(c=|S_s|=3+d\).  For each active term, split its vectors by groups and form matrices
\[
V_a=(v_t|_{R_a})_{t\in S_s}\in\mathbb F_2^{3\times c},\qquad
W_b=(w_t|_{C_b})_{t\in S_s}\in\mathbb F_2^{3\times c}.
\]
The slice equations are
\[
V_jW_i^T=I_3,
\qquad V_aW_b^T=0\quad((a,b)\ne(j,i)).
\]
Since \(V_jW_i^T=I_3\), both \(V_j\) and \(W_i\) have row rank 3.  Let
\(P=\operatorname{row}(V_j)\) and \(Q=\operatorname{row}(W_i)\) in \(\mathbb F_2^c\).  The pairing between \(P\) and \(Q\) is perfect, so
\[
\mathbb F_2^c=P\oplus Q^\perp=Q\oplus P^\perp,
\]
and \(Q^\perp,P^\perp\) have dimension \(d=c-3\) with a nondegenerate induced dual pairing.

The off-block equations with \(W_i\) give \(\operatorname{row}(V_a)\subseteq Q^\perp\) for \(a\ne j\).  The equations with \(V_j\) give \(\operatorname{row}(W_b)\subseteq P^\perp\) for \(b\ne i\).  The remaining off-block equations force these two leak spaces to be orthogonal under the induced pairing.  Therefore
\[
\dim L_v(s)+\dim L_w(s)\le d=c-3,
\]
where
\[
L_v(s)=\operatorname{span}\{v_t\bmod R_j:t\in S_s\},\qquad
L_w(s)=\operatorname{span}\{w_t\bmod C_i:t\in S_s\}.
\]
This is a necessary condition for an exact decomposition; it is not sufficient.

## Consequences

- \(c=3\): \(d=0\), so both leak spaces vanish.  This recovers the analysis purity lemma and the GL\(_3(\mathbb F_2)\) closed-form slice completion.
- \(c=4\): \(\dim L_v+\dim L_w\le1\), so a capacity-4 slice is half-pure: either all its active \(v_t\)'s lie in the own row group or all its active \(w_t\)'s lie in the own column group.  It cannot leak on both sides.
- \(c=5\): \(\dim L_v+\dim L_w\le2\), with allowed leak-rank patterns \((0,0),(1,0),(0,1),(2,0),(0,2),(1,1)\).  This matches the dominant rank-21 pool pattern \((1,1)\), so capacity 5 is a realistic regime rather than a corner case.
- If two slices are both fully pure and their blocks differ in row or column group, no nonzero term can be active in both; otherwise the shared term would have to be supported in disjoint row or column groups.  Zero rank-one factors can be artificially marked active in nonminimal encodings, so CNF uses should phrase this through nonzero/hitting terms rather than raw \(u\)-bits unless zero terms are separately excluded.
- More generally, if one term serves two slices with different row groups, then in at least one of those slices the term contributes to the row leak; at capacity exactly 4 this forces the slice to be \(w\)-pure.  The analogous statement holds with row/column interchanged.

## Verification on known exact rank-21 E11 core decompositions

Script: [e11_defect_leak_analysis.py](../code/e11_defect_leak_analysis.py).
Output: [defect_leak_analysis.json](../results/block_spread/defect_leak_analysis.json).

Results on the 519-row rank-21 E11 pool:

- Exact slice-equation reconstruction checked for all 519 rows: no failures.
- All 519 rows satisfy the defect inequality, capacity-3 purity, capacity-4 half-purity, own-block rank requirements, and fully-pure slice sharing test: `pool_all_rows_defect_ok = true`.
- Slice leak profiles by capacity:
  - \(c=3\): 237 occurrences, all \((\dim L_v,\dim L_w)=(0,0)\).
  - \(c=4\): 260 occurrences, all half-pure: 128 \((0,1)\), 132 \((1,0)\).
  - \(c=5\): 527 occurrences: 21 \((0,2)\), 486 \((1,1)\), 20 \((2,0)\).
  - Larger capacities also obey \(\dim L_v+\dim L_w\le c-3\), often close to saturation.

This independently supports the derivation and shows that the search-relevant regime is capacity 4/5 and higher, not only the rare capacity-3 case.

## Same-W two-deletion near-miss measurement

The same script also rescanned the 815 same-W two-deletion rank-19 near-miss term lists from the known rank-21 pool.  Shadow had rejected 739 and left 76 shadow-consistent A-supports.  Using the inherited \((u,v,w)\) factors after deletion:

- all 76 shadow survivors fail the new exact-slice structural test;
- 18 fail basic slice capacity (some slice has fewer than 3 active terms);
- 58 pass capacity but violate the defect budget on the inherited factors;
- hence shadow plus inherited-factor defect clears all 815 deletion term lists.

Important interpretation: this is not a proof that the 76 A-supports cannot be completed by different \(v,w\).  The defect test here uses the inherited near-miss factors, while a fixed-support completion search is free to change \(v,w\).  The result is still valuable as evidence that shadow and defect act on different structural failures and together are stronger than shadow alone on this local family.

## Local parameter counts for capacities 3--5

Script: [e11_slice_defect_parameterization.py](../../quotient_cores/code/e11_slice_defect_parameterization.py).
Output: [defect_parameterization_counts.json](../results/block_spread/defect_parameterization_counts.json).

For one labelled slice with labelled active terms:

- \(c=3\): 168 completions, exactly GL\(_3(\mathbb F_2)\).
- \(c=4\): 2,520 choices of row-rank-3 own-block \(V\); for each, 8 choices of own-block \(W\); 20,160 own-block pairs.  The allowed leak-pair count per own pair is 127: one pure case, 63 \(v\)-pure / \(w\)-leaking rank-one cases, and 63 \(w\)-pure / \(v\)-leaking rank-one cases.  Total labelled local completions before quotienting by term permutation: 2,560,320.
- \(c=5\): 26,040 row-rank-3 own-block \(V\)'s; for each, 64 own-block \(W\)'s; 1,666,560 own-block pairs.  Allowed leak-pair count per own pair is 20,098 with profiles `(0,0):1`, `(0,1)/(1,0):189` each, `(0,2)/(2,0):3906` each, `(1,1):11907`.  Total labelled local completions are too many for naive per-slice enumeration, but the defect-space representation is finite and structured.

These counts correct the analysis search picture: GL3 alone is too narrow because known exact decompositions mostly have no capacity-3 slices.  The completion module should be extended around capacity-4 half-pure and capacity-5 two-defect parameterizations, using the shared-term incidence constraints to avoid naive enumeration.

## CNF/proof-use status

The defect lemma is mathematically elementary but new to this investigation.  Before it becomes part of any theorem-bearing UNSAT layer, the group should have an independent derivation/code review and a positive control for the exact augmented configuration.  The safest immediate theorem-bearing addition is the capacity-4 implication
\[
(\text{v-leak in slice }s)\wedge(\text{w-leak in slice }s)\Rightarrow c_s\ge5,
\]
encoded with v/w leak variables and a cardinality guard, because it is exactly the half-purity corollary.  The full defect-rank inequalities require rank constraints on leak spaces; they are better used first for parameterized construction search and candidate filtering.

## Implication for next work

The strongest immediate route is no longer longer monolithic CDCL pilots.  It is to build a completion/search representation whose local slice modules cover capacity 4 and 5, because these are where exact rank-21 cores actually live.  In parallel, the same defect-budget idea should be tested directly on full \(T_{333}\) rank-20 representations: the full tensor has nine block slices including the deleted \(R_0\times C_0\) block, and capacity-4 half-purity may constrain rank-20 decompositions without relying exclusively on the inherited no-rank-one-A DRAT branch.

## Additional analysis support-level and fixed-A probes

After the review check, I implemented the support-level purity-side 2-SAT independently in [e11_purity_2sat_filter.py](../../quotient_cores/code/e11_purity_2sat_filter.py), based on the same defect/leak lemma and the accompanying mathematical analysis.

For each slice it uses variables `B_s` and `C_s` meaning v-side/B-pure and w-side/C-pure.  Capacity 3 forces both; capacity 4 forces `B_s OR C_s`; a selected A-direction sharing two slices with different row groups forbids both `B` variables, and different column groups forbids both `C` variables.  The script also evaluates the cap-5 extension from cap-3 sharing as a post-filter.

Results saved in [purity_2sat_filter.json](../results/block_spread/purity_2sat_filter.json):

- all 519 rank-21 E11 pool decompositions pass both the base 2-SAT and the cap-5 extension, giving another positive control;
- in the same-W two-deletion near-miss family, shadow rejects 739/815 as before.  Of the 76 shadow-consistent deletion supports, 18 have slice capacity <3 and are strictly support-impossible; the base purity 2-SAT rejects 4 further capacity-feasible supports.  The cap-5 extension did not reject additional shadow survivors in this family.  Therefore shadow plus strict support-level capacity/2-SAT rejects 761/815, leaving 54 local A-supports still needing fixed-A completion.  This is more logically careful than the inherited-factor defect measurement: those 54 are not ruled out at support level by the current filters.
- across all 815 deletion supports, the base 2-SAT rejects 45 capacity-feasible supports and capacity rejects 169; together with shadow this is still a local-family measurement, not a global rank-19 support cover.
- a random low-weight calibration (not Wang-filtered) found 1,398 capacity-feasible samples among 5,000 attempts with total weight 31--40; base 2-SAT rejected about 60.0% and the cap-5 extension about 66.6%.  This supports research_record's claim that the obstruction is strongest in low-weight regimes, but it is not a complete frontier count.

I then built a fixed-A exact completion solver [e11_fixed_a_completion_sat.py](../code/e11_fixed_a_completion_sat.py).  It fixes a 19-mask A-list, introduces v/w bits and product bits, and encodes all 648 Brent equations exactly.  On the first five same-W deletion supports that pass shadow and purity, CaDiCaL returned UNSAT quickly:

- support 0: caps `[6,3,6,5,5,4,7,7]`, weight 43, 4,716 vars, 16,641 clauses, UNSAT in 0.989s;
- support 1: caps `[3,7,10,7,6,9,6,8]`, weight 56, 5,769 vars, 20,853 clauses, UNSAT in 0.056s;
- support 2: caps `[6,5,7,4,8,7,6,9]`, weight 52, UNSAT in 0.148s;
- support 3: caps `[9,10,10,5,3,10,8,6]`, weight 61, UNSAT in 0.068s;
- support 4: caps `[3,7,10,7,6,11,6,7]`, weight 57, UNSAT in 0.055s.

Summary: [same_w_shadow_purity_summary.json](../results/fixed_a_completion/same_w_shadow_purity_summary.json); CNFs/logs in `workspace/data/fixed_a_completion/same_w_shadow_purity/`.  I also generated and replay-verified an ASCII DRAT proof for support 0: `workspace/data/fixed_a_completion/proof_check/fixedA_000_ascii.drat` verifies against `fixedA_000.cnf` with `drat-trim` (`s VERIFIED`, 4,716 variables, 16,641 clauses, verification time 0.600s).  This demonstrates that per-support completion exclusions can be made certifiable at small scale.  These five UNSATs remain local fixed-A exclusions, not a theorem about all rank-19 E11 supports.

Longer background tasks were submitted, not yet incorporated: `s6_t47_tool1` runs a 300s CaDiCaL pilot on the half-purity augmented rank-19 CNF; `s6_t48_tool1` runs a 300s CP-SAT Wang+purity support search; `s6_t52_tool1` runs fixed-A completion on up to 100 shadow+purity surviving same-W deletion supports.  Their results must be read before use.
