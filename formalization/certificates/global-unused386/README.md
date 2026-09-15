# Frozen bounds 386, 387, and 388

The modules `QiushiGlobalOrbitUnused386`, `QiushiGlobalOrbitUnused387`, and
`QiushiGlobalOrbitUnused388` prove the frozen representative bounds 17.
Their `rep386`, `rep387`, and `rep388` interfaces have type
`QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
(frozenWangTable.lower i)` in namespace `QiushiMatmul.GlobalOrbit.Unused`.

Each certificate is a single root Farkas contradiction with exact integer
multipliers: right-hand sides -4, -8, and -4, respectively. All source bounds
are already proved. The generated Lean modules check their invertible
transports, occupation constraints, and contradiction in the kernel.
Node 386 uses the closed bound 240; node 388 uses `QiushiFrozenRank162`.
The sibling certificate directories contain each node's complete data.

No new rank assumptions, registry entries, or backtracking archive replay
are involved. Interface tests check the exact frozen types and allow only
`propext`, `Classical.choice`, and `Quot.sound`.
