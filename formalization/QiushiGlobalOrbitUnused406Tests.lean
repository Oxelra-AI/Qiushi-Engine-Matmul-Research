import QiushiGlobalOrbitUnused406

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 406))
    (frozenWangTable.lower 406) := rep406

example : QuotientRankAtLeast (spanCodes [276,179,68,10]) 17 := plane406UnusedGen_lb17

run_cmd do
  for name in #[``rep406, ``QiushiMatmul.plane406UnusedGen_lb17,
      ``QiushiMatmul.plane406UnusedGenNoModel, ``QiushiMatmul.plane406UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
