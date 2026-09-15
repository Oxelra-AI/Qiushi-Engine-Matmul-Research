# Root-Leaf Bounds: 308, 309, 312

Import `QiushiGlobalOrbitUnusedN` for each listed node. The declaration
`QiushiMatmul.GlobalOrbit.Unused.repN` has exactly the type

```lean
QuotientRankAtLeast (spanCodes (frozenWangTable.basis N))
  (frozenWangTable.lower N)
```

| Node | Basis | Bound | Closed predecessors | Source/dead/live rows | Leaf RHS |
| --- | --- | --- | --- | --- | --- |
| 308 | `[288,96,10,1]` | 16 | 3,10,14,35,101,103,120,165,182,183,197 | 28/19/14 | -18 |
| 309 | `[290,96,10,1]` | 17 | 3,11,14,30,31,111,156,166,194,196,216 | 28/16/15 | -8 |
| 312 | `[386,96,10,1]` | 17 | 10,14,35,55,72,161,164,166,178,194,196,201,212,213,216,218 | 20/14/17 | -3 |

The existing bounded producer inspected only the 374 subspaces of each
five-dimensional quotient. Each result is a single root Farkas leaf, with
exact integer arithmetic and no branch expansion or BTP conversion. Explicit
invertible transports, source bounds, and occupation tables are checked by
the unchanged Lean certificate engine; solver results are not trusted.
All selected sources are existing closed declarations. No bounds for
87, 92, 109, or 162, and no new registry assumptions, are needed.

All 163 proof/interface/test modules passed against the pinned clean imports,
and their current source and object hashes match successful replay receipts.
The exact-type and transitive axiom guards passed for both each concrete
bound and its frozen wrapper, with exactly
`[propext, Classical.choice, Quot.sound]`. The 20 global-orbit tests and 12
certificate regression tests also passed. This package does not modify the
registry or add any premise to the main theorem.
