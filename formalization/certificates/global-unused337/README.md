# Frozen bounds 337, 339, and 353

The modules `QiushiGlobalOrbitUnused337`, `QiushiGlobalOrbitUnused339`, and
`QiushiGlobalOrbitUnused353` prove the frozen representative bounds 16, 16,
and 17, respectively. Their `rep337`, `rep339`, and `rep353` interfaces have
type `QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
(frozenWangTable.lower i)` in namespace `QiushiMatmul.GlobalOrbit.Unused`.

Each certificate uses already proved source bounds, explicitly checked
invertible transports, occupation constraints, and exact integer Farkas
identities. Nodes 337 and 339 each have a single root contradiction with
right-hand side -6. Node 353 branches once on occupation label 25 at zero;
the two leaves have right-hand sides -1 and -6. These are regenerated small
certificates, not replays of the original backtracking archive.

The sibling directories `global-unused339` and `global-unused353` contain
their respective inputs, selected source declarations, transports, and
branch certificates. Python tests check exact multipliers and transports;
the generated Lean modules check the actual rank arguments in the kernel.
The interface tests report only `propext`, `Classical.choice`, and
`Quot.sound`. No new rank assumptions or registry entries are introduced.
