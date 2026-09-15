# Frozen bounds 394, 395, and 396

The modules `QiushiGlobalOrbitUnused394`, `QiushiGlobalOrbitUnused395`, and
`QiushiGlobalOrbitUnused396` prove the frozen representative bounds 17.
Their `rep394`, `rep395`, and `rep396` interfaces have type
`QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
(frozenWangTable.lower i)` in namespace `QiushiMatmul.GlobalOrbit.Unused`.

Each certificate is a single root Farkas contradiction with exact integer
multipliers: right-hand sides -10, -10, and -24, respectively. All source
bounds are already proved; nodes 395 and 396 use `QiushiFrozenRank162`.
The generated Lean modules check invertible transports, occupation
constraints, and the contradiction in the kernel. The sibling certificate
directories contain each node's complete data.

No new rank assumptions, registry entries, or backtracking archive replay
are involved. Interface tests check the exact frozen types and allow only
`propext`, `Classical.choice`, and `Quot.sound`.
