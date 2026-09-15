# Unused Wang Nodes

## Certificate Reuse

The producer `tools/global_orbit_unused_certificate.py` uses the existing
certificate emitter and closed predecessor declarations. Run it from the
formalization directory with explicit inputs and node-specific output paths.
It uses the already checked orbit transports, without another global orbit search.

## Completed Bounds

Import `QiushiGlobalOrbitUnused20`; namespace `QiushiMatmul.GlobalOrbit.Unused`:

```lean
rep020 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 20))
  (frozenWangTable.lower 20)
rep086 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 86))
  (frozenWangTable.lower 86)
```

Both labels are 12. Node 20 uses the existing generic deletion theorem with
annihilator codes `[96,128,256]`, six selected B coordinates, and six columns.
The finite independence and fold-uniform checks are kernel proofs. Node 86
follows by containment in node 20. No orbit search or new semantic engine is
used. Exact-type tests and transitive axiom guards pass; both axiom lists are
`[propext, Classical.choice, Quot.sound]`.

## Registry Dependencies

These two bounds are outside the inspected 404-entry registry, so their
integration gives 406 checked entries and leaves 90 interfaces at that checkpoint.

Inspection of the original certificate identifies the original
92-node split as one forced-product node (20), four degeneration nodes
(86,341,418,441), and 87 backtracking nodes. With 20 and 86 closed, the other
three degenerations still need the existing open prerequisites 162, 284, 289.
The shortest recorded backtracking sizes include 184 (17), 181 (19), 203 (26),
88 (31), 273 (31), and 284 (41). These are discovery priorities, not verified
traces: each original backtracking record stores a size, not its branch proof.
They need explicit semantic branch/leaf certificates before reuse in Lean.
This observation concerns the protobuf text only, not the whole original
package. The separate `.btp` archive contains DFS leaf records. Its decoding
and the remaining semantic proof requirements are described in
[FrozenRegistry/UnusedNodes.md](FrozenRegistry/UnusedNodes.md).

The original certificate metadata and proof-used source imports are evidence
for routing only. No producer success, proof-size field, or numeric label is
accepted as a quotient-rank theorem. No full transport search was rerun.

## Regenerated Node 184

Import `QiushiGlobalOrbitUnused184`; the same namespace now supplies:

```lean
rep184 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 184))
  (frozenWangTable.lower 184)
```

This is the closed bound 15 for `[386,84,32,10,1]`, not a conditional use of the
original certificate label. All 67 subspaces of its four-dimensional quotient
were routed using the already available extension words. Only predecessors
7, 51, 55, 56, 79, 82, 84 are used. Their actual source declarations are in
`certificates/global-unused184/sources.json` and already belong to the clean
main import closure. No other missing rank bound is a premise.

There are 14 source rows, 13 dead rows, and two live cosets. The one Farkas leaf
adds a capacity-five row to the total-at-least-14 row, yielding `0 <= -9`.
The existing `generic_plane_qra` and exact Farkas/branch emitter prove the result;
explicit GL matrices are computed from extension words and checked again by
Lean. The original backtracking size is not used. The emitter's optional module
prefix and supplied-witness arguments leave existing invocations unchanged.

Regenerate into a private staging directory with
`tools/global_orbit_unused_certificate.py --node 184 --bound 15`, supplying
`--bases`, `--transitions`, `--registry`, `--output`, and `--emit`. The first two
inputs are the existing 496-basis export and masked transition JSONL; the third
is the checked registry JSON. The search refuses more than 400 quotient spaces,
255 branch nodes, or a 90-second branch-search budget. Solver results are only
discovery: all rays are verified with exact integers before Lean emission.

The `rep184` type and transitive axiom guards pass with exactly
`[propext, Classical.choice, Quot.sound]`. Together with 20 and 86, this increases
the original 404-entry registry to 407 after integration, leaving 89 interfaces.

## Regenerated Node 181

`QiushiGlobalOrbitUnused181` supplies the closed `Unused.rep181` with the same
exact frozen-table interface, at label 15 for `[258,84,32,10,1]`. Its only
predecessors are 5, 55, 78, 82, 83, 84. Unbound node 33 is explicitly excluded
from the producer's admissible source pool. The certificate has 13 source rows,
12 dead rows, three live cosets, and one exact Farkas leaf with RHS -9.
The 53 node modules and both final axiom guards pass. Together with the previous
additions, integration gives 408 checked entries and 88 remaining interfaces.

## Regenerated Node 203

`QiushiGlobalOrbitUnused203` supplies the closed `Unused.rep203`, at label 16
for `[272,176,68,10,1]`. Its only predecessors are 8, 10, 67, 69. The certificate
has 15 source rows, 11 dead rows, four live cosets, and one exact Farkas leaf:
four occupation rows with weights 2,1,1,1 and the total row with weight 3 give
RHS -24. All 53 node modules and final type/axiom guards pass, with only the
three standard axioms. The pass on 181,184,203 closes three of the 90 interfaces
remaining after 20 and 86, independently of any concurrent registry progress.

All three packages use the same existing Lean extraction/Farkas engine and
the same bounded producer; no source assumptions among those 90 are used.
Their 159 current Lean source hashes match successful compilation receipts.
The 20 global-orbit Python tests and 12 legacy certificate tests pass, including
exact rays for all packaged certificates and rejection of corrupt multipliers.

## Bounded Batch: 273, 284, 291

The modules `QiushiGlobalOrbitUnused273`, `QiushiGlobalOrbitUnused284`, and
`QiushiGlobalOrbitUnused291` supply closed `Unused.rep273`, `Unused.rep284`, and
`Unused.rep291` with exactly the frozen-table interface above. Their bounds
are respectively 16, 17, and 16, for bases `[156,80,2,1]`, `[68,20,10,1]`, and
`[84,32,10,1]`. All 181 generated/interface/test modules passed against the
pinned clean environment; current source hashes match successful receipts.
Each final theorem and wrapper has exactly the three standard axioms.

| Node | Closed predecessors used | Source/dead/live counts | Leaf RHS |
| --- | --- | --- | --- |
| 273 | 23,31,35,97,101,134 | 44/43/1 | -12 |
| 284 | 19,75,96,150,156,159,160,161 | 34/33/2 | -9 |
| 291 | 23,32,35,99,101,120,141,179,180,181,182,183,184,185 | 33/30/3 | -21 |

Each search enumerated only 374 quotient subspaces and produced one Farkas
leaf without branching. The 291 package imports the already proved 181/184
final modules directly, not registry wrappers. The source choices and exact
transports are recorded in the corresponding `certificates/global-unused*`
packages. No additional missing interface is assumed. Node 284 supplies the
prerequisite for the existing 418 degeneration reduction; that registry
consequence is deliberately not duplicated here.

## Closed Node 289

`QiushiGlobalOrbitUnused289` supplies:

```lean
rep289 : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 289))
  (frozenWangTable.lower 289)
```

This is bound 17 for `[258,20,10,1]`. Its only predecessor bounds are
3,7,10,11,17,35,75,118,156,160,161,164,166,175, all existing closed sources.
The package has 27 source rows, 14 dead rows, and 19 live labels. One Farkas
leaf combines 13 occupation rows and the total row (weight 8), with exact
RHS -17. The bounded search again visited only 374 quotient subspaces and
needed no branching. No `.btp` archive search or inspection was needed here.

All 55 node modules, including the frozen-interface and axiom tests, passed.
The final theorem and `rep289` both have exactly
`[propext, Classical.choice, Quot.sound]`. Across 273/284/289/291, all 236 current
source and object hashes match successful compilation receipts. Node 289
supplies the premise for Plato's existing 441 degeneration reduction; its
registry binding remains Plato's responsibility. This completes the assigned
273/284/289 batch and the previously in-flight 291, without new rank premises.
