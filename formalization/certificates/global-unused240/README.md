# Root-Leaf Bounds: 240, 248, 249

The three corresponding `QiushiGlobalOrbitUnusedN` modules supply
`QiushiMatmul.GlobalOrbit.Unused.repN`, each with exact type

```lean
QuotientRankAtLeast (spanCodes (frozenWangTable.basis N))
  (frozenWangTable.lower N)
```

| Node | Basis | Bound | Closed predecessors | Source/dead/live rows | Leaf RHS |
| --- | --- | --- | --- | --- | --- |
| 240 | `[261,161,68,19,10]` | 16 | 66,67,84 | 15/6/9 | -4 |
| 248 | `[8,4,2,1]` | 14 | 5,20,23,25,88 | 23/3/28 | -2 |
| 249 | `[80,4,2,1]` | 14 | 23,25,27,88 | 29/3/28 | -28 |

Each certificate is one exact Farkas leaf, obtained with the existing
`tools/global_orbit_unused_certificate.py` from closed source declarations.
The search visited only 67 quotient subspaces for 240 and 374 for 248/249;
it needed no branch expansion, global orbit search, or BTP trace conversion.
Explicit invertible transports and finite occupation tables are checked by
Lean using the unchanged certificate engine. Solver output is not trusted.

All 163 proof/interface/test modules passed, with source and object hashes
matching successful build receipts. The 54 required newer import modules were
also recompiled in independent output against the pinned clean environment.
In particular, 248/249 reuse `QiushiGlobalOrbitUnused88Final`, and 249 additionally
reuses `QiushiFrozenRank27`; these imports are not duplicated in the packages.
No bound for 87, 92, 109, or 162 is a premise.

The exact-type and transitive axiom guards passed for each bound, with exactly
`[propext, Classical.choice, Quot.sound]`. The 20 global-orbit tests and 12
certificate regression tests passed, including exact integer rays and
malformed-certificate rejection. Registry integration is separate; these
theorems introduce no new premise to the main theorem.
