# Frozen bounds 389, 390, and 392

The modules `QiushiGlobalOrbitUnused389`, `QiushiGlobalOrbitUnused390`, and
`QiushiGlobalOrbitUnused392` prove the frozen representative bounds 17.
Their `rep389`, `rep390`, and `rep392` interfaces have type
`QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
(frozenWangTable.lower i)` in namespace `QiushiMatmul.GlobalOrbit.Unused`.

Each certificate is a single root Farkas contradiction with exact integer
multipliers: right-hand sides -21, -6, and -6, respectively. All source
bounds are already proved; the generated Lean modules check their
invertible transports, occupation constraints, and contradiction.
The sibling certificate directories contain each node's complete data.

No new rank assumptions, registry entries, or backtracking archive replay
are involved. Interface tests check the exact frozen types and allow only
`propext`, `Classical.choice`, and `Quot.sound`.
