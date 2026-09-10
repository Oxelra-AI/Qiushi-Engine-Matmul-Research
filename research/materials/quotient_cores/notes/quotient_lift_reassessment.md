# Reassessment of the E11 quotient-lift route

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## Scientific purpose

The active goal is still the exact tensor rank of \(T_{\langle3,3,3\rangle}\). The E11 finite-field route is only an intermediate route: an E11 rank-19 decomposition over \(\mathbb F_2\) would lift by three elementary products to a full \(T_{333}\) rank-22 decomposition over \(\mathbb F_2\). Conversely, failures inside E11 do not by themselves prove characteristic-zero rank 23 optimality.

The previous ARTIFACT tested a quotient-lift idea for a depth-4 E11 A-prefix \([80,122,191,213]\): use a rank-15 decomposition of the quotient by the four-dimensional prefix span, then lift the 15 quotient terms and repair the residual with four prefix-span terms. The ARTIFACT correctly found no lift for the 211 available rank-15 quotient schemes, but its attempted universal closure via a flattening-rank argument was too strong. This note corrects that interpretation and replaces it by an exact coset intersection formulation.

## Correct mathematical formulation

Let \(V\subset \mathbb F_2^8\) be a four-dimensional A-subspace with basis \(u_1,\dots,u_4\), and let
\[
\pi:T_{E11}\to (\mathbb F_2^8/V)\otimes \mathbb F_2^9\otimes \mathbb F_2^9
\]
be the quotient. Suppose a rank-15 quotient CPD is fixed:
\[
\pi(T_{E11})=\sum_{j=1}^{15} \bar a_j\otimes b_j\otimes c_j.
\]
Choose any representatives \(a_j^0\) of \(\bar a_j\). Every lift of this fixed quotient scheme has
\[
a_j=a_j^0+v_j,\qquad v_j\in V.
\]
The residual after the representative lift is
\[
R=T_{E11}-\sum_{j=1}^{15}a_j^0\otimes b_j\otimes c_j\in V\otimes B\otimes C.
\]
A lift to an E11 rank-19 CPD exists exactly when
\[
R+\sum_{j=1}^{15} v_j\otimes b_j\otimes c_j
\]
has tensor rank at most 4 over \(V\otimes B\otimes C\). In coordinates relative to the chosen basis of \(V\), this is
\[
R_{kbc}+\sum_{j=1}^{15} \lambda_{kj}(b_jc_j)_{bc}
   = \sum_{t=1}^{4} \alpha_{tk}\beta_{tb}\gamma_{tc}
\]
for \(k=1,\dots,4\). Equivalently, one intersects the affine coset
\[
R+V\otimes\operatorname{span}\{b_j\otimes c_j\}_{j=1}^{15}
\]
with the rank-\(\le4\) secant variety of \(\mathbb P(V)\times\mathbb P(B)\times\mathbb P(C)\), over \(\mathbb F_2\).

The analysis script `e11_quotient_lift.py` solved only the subcase where the four residual terms are forced to have A-factors equal to the selected basis \(u_1,\dots,u_4\), so the problem separates into four independent rank-one matrix coset tests. That is useful evidence but is not the full lift-back problem. Termwise lift corrections can change all four V-coordinate residual slices simultaneously and the four residual rank-one terms may use arbitrary nonzero A-factors inside \(V\), so a flattening-rank statement about the uncorrected residual does not by itself close the route.

## Exact general coset SAT implementation

I wrote [e11_quotient_lift_general_sat.py](../code/e11_quotient_lift_general_sat.py). For a fixed prefix span and a fixed quotient scheme, it introduces variables

- \(\lambda_{kj}\) for the arbitrary correction of each of the 15 quotient A-lifts by an element of \(V\);
- four residual rank-one terms with variables \(\alpha_{tk}\), \(\beta_{tb}\), \(\gamma_{tc}\);
- product variables for \(\beta_{tb}\gamma_{tc}\) and \(\alpha_{tk}\beta_{tb}\gamma_{tc}\).

It writes a native-XOR CryptoMiniSat formula for all \(4\cdot9\cdot9=324\) parity equations of the residual coset. A SAT model is decoded into a full E11 decomposition and independently verified; if verified, the existing +3 elementary lift would give a full \(T_{333}\) rank-22 decomposition over \(\mathbb F_2\).

This exactly addresses the missing termwise-lift correction and arbitrary residual-A issue for a fixed quotient scheme. It still does **not** prove universality over all possible rank-15 quotient schemes, because the available 211 schemes are a flip-cpd pool, not an exhaustive certified list.

## Results for prefix [80,122,191,213]

Input quotient pool:

[mod2-rank15a.npy](../../exact_baselines/arrays/q_leaf0_flip_workspace/data/schemes_modp/qleaf0/mod2-rank15a.npy)

Fixed-basis lift result from analysis:

[quotient_lift_results.json](../results/quotient_lift/quotient_lift_results.json)

It tried 211 rank-15 quotient schemes and found no separated-basis lift. The summary records `e11_witnesses=0`, `t333_witnesses=0`; it does not contain per-scheme details because the script summary overwrote them.

General coset SAT result from this ARTIFACT:

[leaf0_general_lift_all211.json](../results/general_quotient_lift_leaf0/leaf0_general_lift_all211.json)

Command:

```bash
python -B scripts/e11_quotient_lift_general_sat.py \
  --pool data/q_leaf0_flip_workspace/data/schemes_modp/qleaf0/mod2-rank15a.npy \
  --prefix 80,122,191,213 \
  --outdir data/general_quotient_lift_leaf0 \
  --name leaf0_general_lift_all211 \
  --timeout-per-scheme 60 --threads 8
```

Outcome: all 211 quotient schemes returned `UNSAT` quickly in the exact general coset SAT, with no E11 witness. Each per-scheme instance had 1768 variables and 324 native XOR residual equations; the all-211 run took about 15.3 seconds. This is substantially stronger than the analysis separated-slice test because the solver allowed arbitrary \(V\)-corrections of the 15 quotient terms and arbitrary four-term residual CPD inside \(V\).

Scientific meaning: the 211 available quotient schemes for this prefix do not lift to E11 rank 19. This is a strong negative result for this prefix-and-pool surface. It still does not exclude an unseen rank-15 quotient decomposition of the same quotient tensor, an inequivalent prefix span, or a non-E11 route to full \(T_{333}\) rank 22.

## Standard prefix quotient rank is not proved exactly

The previous ARTIFACT said the standard prefix \([1,2,4,8]\) quotient has rank 12 because flip-cpd stayed at rank 12, matching its 12 nonzero sparse entries. That was not a real lower bound.

What is currently established:

- Dense quotient tensor file: [q_std4.npy](../arrays/q_std4/q_std4.npy).
- Sparse flip tensor file: [qstd4.npy](../arrays/q_std4_flip_workspace/data/tensors/qstd4.npy), containing the 12 nonzero coordinate rows.
- The 12 coordinate entries give a trivial rank-12 CPD upper bound.
- A plain rank-11 SAT run timed out after 300 s:
  [qstd4_rank11_plain.json](../results/qstd4_rank11_sat/qstd4_rank11_plain.json).
- A native rank-11 SAT run is currently entrusted as background task `s13_t8_tool1`:
  output directory `data/qstd4_rank11_native/`.
- A rank-10 native SAT attempt returned `UNKNOWN` after about 301 s:
  [qstd4_rank10_native.json](../../symmetry_and_residuals/results/qstd4_rank10_native/qstd4_rank10_native.json).

Thus the current mathematically supported statement is: the standard quotient rank is at most 12, and no lower bound beyond ordinary flattenings or completed solver evidence has yet been completed in this ARTIFACT. It should not be called exactly 12 until a rank-11 exclusion is certified or a mathematical lower-bound proof is written.

## Occupation search status

The analysis handoff suggested running `e11_occupation_2swap.py` around the 11-violation support
\[
[1,2,3,4,8,9,16,28,65,97,108,144,180,192,195,210,216,227,252].
\]
The first background attempt `s13_t9_tool1` failed before doing science: the script expected a membership array of shape `(255,n_sub)`, but the actual saved membership is `(256,417199)`. Therefore it produced no local-search conclusion. I patched `e11_occupation_2swap.py` so future runs accept both membership orientations and also accept `--out` as an explicit output path.

Rather than repeat the broken run, I launched the already repaired CP-SAT bounded-neighborhood model on the same support. Task `s13_t19_tool1`, label `e11_11viol_radius2_mip`, completed with status `INFEASIBLE` in about 68.45 s. Output:

[iter16_11viol_radius2.json](../results/e11_occupation_neighborhood/iter16_11viol_radius2.json).

The input support has 11 complete-Wang violations, all max-excess 1 (four dimension-4, five dimension-5, and two dimension-6 violations; L-values 15 and 12). The radius-2 CP-SAT model used all 417,197 nontrivial complete-Wang cuts and proved there is no complete-Wang feasible rank-19 A-multiset within two replacements of this 11-violation support. This is a local exclusion only; it does not decide global E11 occupation feasibility.

## Revised research judgment

The quotient-lift route should not be closed by the analysis flattening argument. The correct evidence is more precise:

1. The separated-basis lift test excluded a narrow subcase for 211 quotient schemes at prefix \([80,122,191,213]\).
2. The new general coset SAT excludes the full arbitrary-lift, arbitrary-four-residual-term problem for those same 211 schemes at the same prefix.
3. This still depends on a non-exhaustive quotient-scheme pool. Universality would require either an exhaustive rank-15 quotient CPD enumeration/certificate for that quotient tensor, or an invariant/theorem showing every rank-15 quotient scheme falls into the excluded classes.
4. Prefix orbits under the corrected 576-element E11 quotient action should be used to choose inequivalent four-dimensional prefix spans; quotient-scheme invariants should be recorded before deciding whether the repeated emptiness is structural.
5. Standard quotient rank is only an upper bound plus incomplete lower-bound attempts at present.

## Concrete next work

The next scientifically useful construction/check is not to return to monolithic shallow prefix-Brent SAT. It is to extend the exact coset SAT to orbit-representative prefix spans and selected quotient rank-15 pools:

- classify four-dimensional A-subspaces/prefix spans under the corrected 576-element action, preferably with invariants from the quotient tensor such as nnz, flattening ranks, and flip-cpd rank achieved;
- for each promising orbit representative, generate a rank-15 quotient pool if the quotient admits one;
- run `e11_quotient_lift_general_sat.py` on that pool;
- if SAT, decode, independently verify E11, and apply the +3 full lift;
- if repeated UNSAT, preserve exact records but do not call it universal without an exhaustive quotient-scheme certificate or a proof of invariant coverage.

In parallel, collect the pending `s13_t8_tool1` and `s13_t19_tool1` when the runtime delivers them. The standard quotient rank and the 11-violation occupation neighborhood should then be updated from actual evidence.

## Addendum after review verification and further exact tests

review independently checked the corrected formulation. Its main mathematical reading agrees with the coset equation: for a fixed quotient CPD, lift-back is exactly the search for an element of
\[
R+V\otimes\operatorname{span}\{b_j\otimes c_j\}
\]
with true tensor rank at most the residual budget inside \(V\otimes B\otimes C\). The verifier emphasized that this is true finite-field tensor rank, not a border-rank or Zariski-closure statement, and that changing representatives of the quotient factors only translates \(R\) within the same coset. It also flagged a practical gap: before relying on the new SAT tool, the SAT-success decode path should be exercised on a known positive instance.

### Positive regression for the general lift SAT

I built [e11_make_general_lift_regression.py](../code/e11_make_general_lift_regression.py). Starting from the known verified E11 rank-21 pool row, it selected a four-dimensional prefix span containing exactly four source A-factors:
\[
V=\langle 4,8,36,112\rangle.
\]
The induced quotient CPD has 17 terms and the known residual has four terms, so the total budget is 21. The generator wrote

[known_rank21_inside4_q17_res4.npy](../arrays/general_lift_positive_regression/known_rank21_inside4_q17_res4.npy)

and metadata at

[known_rank21_inside4_meta.json](../results/general_lift_positive_regression/known_rank21_inside4_meta.json).

Running the general lift SAT on this induced quotient returned SAT in about 0.02 s, decoded to an E11 rank-21 decomposition with tensor difference 0, and lifted by the three elementary terms to a full \(T_{333}\) rank-24 decomposition with difference 0:

[known_rank21_inside4_general_lift.json](../results/general_lift_positive_regression/known_rank21_inside4_general_lift.json).

I then wrote and ran an independent mask-level verifier:

[e11_verify_lift_json.py](../code/e11_verify_lift_json.py)

which recomputed both tensor identities from the JSON masks and recorded `all_checked_ok=true` at

[known_rank21_inside4_general_lift_independent_verify.json](../results/general_lift_positive_regression/known_rank21_inside4_general_lift_independent_verify.json).

This does not advance the rank-19 target, but it verifies that the general SAT model can produce, parse, and independently validate SAT solutions.

### Four-dimensional prefix-span orbit landscape

I built [e11_prefix_span_orbit_invariants.py](../code/e11_prefix_span_orbit_invariants.py) and ran it against the verified 576-element quotient action and the complete Wang cache. The full invariant file is

[prefix_span_orbit_invariants_top1000.json](../results/prefix_span_orbits/prefix_span_orbit_invariants_top1000.json).

It finds 620 orbits of four-dimensional A-subspaces. The quotient coordinate-nnz distribution over orbit representatives is

\[
12:22,\;15:14,\;18:85,\;21:57,\;24:47,\;27:128,\;30:84,\;33:44,\;36:43,\;39:42,\;42:31,\;45:16,\;48:6,\;51:1.
\]

The ordinary flattening lower-bound distribution for the representative quotient tensors is `6:3` and `9:617`. The tested leaf prefix \([80,122,191,213]\) lies in orbit 1024; its orbit representative has quotient coordinate nnz 36 and flattening ranks A=4, B=9, C=9. The standard prefix \([1,2,4,8]\) lies in orbit 438; its representative has quotient coordinate nnz 12 and flattening ranks A=4, B=9, C=6. These numbers are orbit/prefix-span invariants for route selection; coordinate nnz remains only an upper bound on quotient rank.

### Coordinate quotient schemes on low-nnz prefix orbits

For the 14 four-dimensional prefix-span orbits whose quotient has exactly 15 nonzero coordinates, I ran the exact general coset SAT on the coordinate rank-15 quotient CPD with residual budget 4:

[q15_all14_scan.json](../results/trivial_quotient_lift_scan/q15_all14_scan.json).

All 14 instances returned UNSAT quickly. This excludes those coordinate quotient schemes for those representatives, not all quotient CPDs.

For three q=12 coordinate quotient representatives, direct general coset SAT with residual budget 7 returned UNKNOWN after 120 s each:

[q12_first3_scan.json](../results/trivial_quotient_lift_scan/q12_first3_scan.json).

For the standard prefix q=12 coordinate quotient, the same direct SAT was UNKNOWN after 600 s:

[std4_rank12_plus7_general_lift.json](../results/general_quotient_lift_std4/std4_rank12_plus7_general_lift.json).

These UNKNOWN results were then explained by a simpler exact invariant below.

### Contraction-coset slice-rank invariant

I wrote [e11_lift_slice_rank_invariants.py](../code/e11_lift_slice_rank_invariants.py). For every nonzero functional \(\phi\in V^*\), it computes exactly
\[
m_\phi=\min_{Y\in R_\phi+\operatorname{span}\{b_j\otimes c_j\}}\operatorname{rank}(Y)
\]
by Gray-code enumeration over the quotient matrices. If a residual lift with at most \(s\) rank-one terms exists, and \(n_v\) counts residual A-factors equal to \(v\in V\setminus\{0\}\), then necessarily
\[
\sum_v n_v\le s,\qquad
\sum_{\phi(v)=1}n_v\ge m_\phi \quad (\phi\ne0).
\]
In particular \(\sum_{\phi\ne0}m_\phi\le 8s\), since each nonzero \(v\) is seen by exactly eight nonzero functionals. The script also checks the small integer covering condition exactly.

For the leaf prefix \([80,122,191,213]\), all 211 rank-15 quotient schemes fail this necessary condition for \(s=4\):

[leaf0_all211_slice_rank.json](../results/lift_slice_rank_invariants/leaf0_all211_slice_rank.json).

The distribution of \(\sum m_\phi\) is 42 for 5 schemes, 44 for 5, 46 for 163, and 48 for 38, while \(8s=32\). Thus the fast general-SAT UNSATs are explained by a transparent contraction-coset rank obstruction for this pool.

For the standard q=12 coordinate quotient with \(s=7\), the same invariant gives \(\sum m_\phi=66>56=8s\) and cover infeasibility:

[std4_q12_res7_slice_rank.json](../results/lift_slice_rank_invariants_std4/std4_q12_res7_slice_rank.json).

Finally, [e11_trivial_quotient_slice_invariant_scan.py](../code/e11_trivial_quotient_slice_invariant_scan.py) scanned all 36 four-dimensional prefix-span orbit representatives whose coordinate quotient rank is at most 15:

[coordinate_q_le15_all36_slice_rank.json](../results/lift_slice_rank_invariants/coordinate_q_le15_all36_slice_rank.json).

All 36 coordinate quotient schemes fail the cover condition within the E11 rank-19 budget. For q=12 representatives, some have \(\sum m_\phi\le 56\), but the stronger covering condition still fails; for q=15 representatives, \(\sum m_\phi>32\) in every case.

### Updated route implications

The corrected quotient-lift route is not closed globally, but it is now much sharper:

- fixed quotient CPDs can be tested exactly by the coset SAT, with a positive regression verified;
- for the leaf0 rank-15 pool and all low-coordinate-rank representative coordinate schemes, a simple contraction-coset rank invariant already excludes rank-19 lifts;
- coordinate sparsity of the quotient tensor is a poor proxy for liftability;
- the hard remaining quotient-lift work is not more separated-slice testing, but either generating genuinely different quotient CPDs or encoding the quotient CPD and lift simultaneously for fixed prefix spans.

The next high-value construction is a fixed-\(V\) joint quotient-and-lift SAT for selected orbit representatives, especially the three representatives with quotient flattening lower bound 6 and high Wang cap, or a direct use of the contraction-coset invariant as a filter during quotient CPD generation. In parallel, the E11 occupation support route remains open; the radius-2 neighborhood around the 11-violation support is now excluded, but global occupation feasibility is not decided.
