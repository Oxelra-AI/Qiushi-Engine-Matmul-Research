import QiushiGlobalOrbitUnused301

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 301))
    (frozenWangTable.lower 301) := rep301

example : QuotientRankAtLeast (spanCodes [176,68,10,1]) 17 := plane301UnusedGen_lb17

run_cmd do
  for name in #[``rep301, ``QiushiMatmul.plane301UnusedGen_lb17,
      ``QiushiMatmul.plane301UnusedGenNoModel, ``QiushiMatmul.plane301UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
