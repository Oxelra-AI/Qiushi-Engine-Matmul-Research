# corrected lift reconstruction review

> Historical research record. Read with the [correction guide](../../../corrections.md); recorded conclusions are not new verification receipts.

## What changed from analysis

The analysis lift-row branch closures are not mathematical evidence for a rank-21 lower bound. Two representation mismatches were found before this ARTIFACT and then checked in source:

1. `dc_verified_export.py` and `qcontaining_analysis.py` wrote quotient point `p` as bit `p-1`, while `pair_prop_dfs.cpp` reads native point `p` from bit `p`. Bit 0 is not a valid point in the DFS domain, so rows exported this way act on shifted point labels.
2. The analysis exporters used a section deleting the lowest set bit of the pivot; analysis quotient orbits and branch semantics use the section deleting the highest pivot bit. Either section can be made into coordinates, but merged rows, existing quotient binaries, branch representatives, and peer supports require explicit coordinate transport. analysis did not perform such transport.

## Corrected reconstruction

I reconstructed the lift mechanisms from subspace bases in the analysis high-pivot convention and the native bit-`p` mask convention.

Files:

- [reconstruct_lift_constraints.py](../code/reconstruct_lift_constraints.py)
- [corrected_lift_constraints.json](../results/quotient_lift/corrected_lift_constraints.json)
- [dc_all_dims.py](../code/dc_all_dims.py)
- [dc_all_dims.json](../results/quotient_lift/dc_all_dims.json)
- [qidentity_all_dims_compare.py](../code/qidentity_all_dims_compare.py)
- [qidentity_all_dims_compare.json](../results/quotient_lift/qidentity_all_dims_compare.json)

For a pivot `q`, a quotient point `p` is lifted by inserting a zero in the highest pivot bit:

\[
s(p)=\text{section lift},\qquad a_p=s(p)+\epsilon_p q.
\]

For every quotient subspace `U`, the full subspace `W=<q,s(U)>` containing `q` gives

\[
1+|S\cap U|\le 20-L(W),\qquad |S\cap U|\le 19-L(W),
\]

which is exactly the ordinary length-19 quotient row. The rowwise all-dimensional comparison found no mismatch:

- rank-2 pivot 17: 417198 quotient subspaces checked; 360541 reconstructed cap-≤5 rows; missing 0, cap mismatch 0, extra binary masks 0.
- rank-3 pivot 273: 417198 quotient subspaces checked; 358618 reconstructed cap-≤5 rows; missing 0, cap mismatch 0, extra binary masks 0.

Thus the analysis report of 10796 new q-containing rows per pivot came from representation mismatch, not new mathematics.

For q-avoiding graph families, I recomputed the averaging bound from the complete Wang LUT in all quotient dimensions. For `U` of dimension `d`, graph rows

\[
W_\alpha=\{s(u)+\alpha(u)q:u\in U\},\qquad \alpha\in U^*,
\]

give

\[
|S\cap U|\le \left\lfloor\frac{\sum_\alpha (20-L(W_\alpha))}{2^{d-1}}\right\rfloor.
\]

Across all 417198 nonzero quotient subspaces for each pivot, this averaging bound never improves the ordinary quotient capacity. Both corrected DC export binaries are empty with SHA256 `9e5d9eaacda0529aa3a572d85ecbb9e0edc876addc46fda0718f4edaa1b092cc`.

This preserves the graph-family mechanism but shows that its pure occupation shadow adds no row beyond Wang quotient occupation.

## Lift-bit information that survives

The individual graph inequalities still carry information because they depend on the lift bits. I checked the peer rank-2 Wang-admissible support

\[
[1,3,9,33,99,128,132,144,148,160,184,189,192,198,209,215,224,249,254].
\]

Coordinate sanity file [peer_support_coordinate_check.json](../../occupation_and_completion/results/quotient_lift/peer_support_coordinate_check.json) confirms it has zero violations against the native-bit-p rank-2 quotient binary, while the bit-p-minus-one interpretation gives 3616 violations. This is a direct illustration of the analysis mask shift.

The all-row lift-bit check rebuilt every relevant inequality from the complete Wang LUT:

- script: [lift_bit_feasibility_allrows.py](../../occupation_and_completion/code/lift_bit_feasibility_allrows.py)
- result: [allrows_lift_bit_feasibility_rank2_maxdim9.json](../../occupation_and_completion/results/quotient_lift/allrows_lift_bit_feasibility_rank2_maxdim9.json)

It found no q-containing pure quotient violation for the peer support. It produced 68920 deduplicated nontrivial q-avoiding lift-bit inequalities and CP-SAT returned INFEASIBLE in 0.46 s.

I then wrote an exact 19-bit backtracking verifier independent of CP-SAT solving:

- script: [exact_lift_bit_dfs_peer.py](../../occupation_and_completion/code/exact_lift_bit_dfs_peer.py)
- result: [exact_lift_bit_dfs_peer.json](../../occupation_and_completion/results/quotient_lift/exact_lift_bit_dfs_peer.json)

It visited 359 nodes, pruned 360 children, reached no leaf, and found zero lift assignments. This establishes that the peer support cannot be lifted to a full A-side support satisfying Wang occupation, under the corrected pivot-17 quotient model and the pinned Wang LUT.

A greedy minimization yielded an inclusion-minimal lift-incompatible subset

\[
A=\{9,33,99,160,184,189,192,209,215,224,249,254\}.
\]

Files:

- [minimize_lift_cut_peer.py](../code/minimize_lift_cut_peer.py)
- [minimized_lift_cut_peer.json](../results/quotient_lift/minimized_lift_cut_peer.json)

The restricted system has 3829 constraints and exact DFS finds no lift assignment in 172 nodes. Every one-point deletion was feasible. Therefore the monotone cut

\[
\sum_{p\in A}x_p\le 11
\]

is valid for rank-2 pivot 17 in these coordinates: any extension containing all points of `A` would restrict to a lift assignment on `A`, contradicting the exact infeasibility result.

## Scientific status after this ARTIFACT

The lower bound `R_{F2}(T_{333}) >= 21` is not established. The analysis branch closures using merged lift rows are unusable as evidence. What is now reliable is sharper:

- q-containing full rows reproduce ordinary quotient rows exactly.
- graph-family averaging is sound but adds no pure occupation rows over the complete Wang LUT.
- the peer rank-2 Wang-admissible support is eliminated by genuine coupled lift-bit constraints, not by pure quotient occupation.
- one small monotone lift-incompatibility cut is available for the rank-2 pivot search.

The next research work should integrate corrected lift-bit feasibility into quotient search as a CEGAR-style separation mechanism: when a quotient support or partial support is Wang-admissible, rebuild its lift-bit system from full Wang rows in canonical coordinates, derive small monotone cuts from UNSAT subsets, and continue search with those cuts. This should be done first for the rank-2 branches where a real Wang-admissible survivor already exists, then for rank-3. The route remains promising because it detects information lost by graph averaging, but no global exclusion has yet been obtained.
