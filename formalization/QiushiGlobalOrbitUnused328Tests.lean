import QiushiGlobalOrbitUnused328

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 328))
    (frozenWangTable.lower 328) := rep328

example : QuotientRankAtLeast (spanCodes [140,96,16,1]) 16 := plane328UnusedGen_lb16

run_cmd do
  for name in #[``rep328, ``QiushiMatmul.plane328UnusedGen_lb16,
      ``QiushiMatmul.plane328UnusedGenNoModel, ``QiushiMatmul.plane328UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
