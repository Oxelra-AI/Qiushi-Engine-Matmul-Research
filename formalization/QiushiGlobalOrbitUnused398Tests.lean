import QiushiGlobalOrbitUnused398

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 398))
    (frozenWangTable.lower 398) := rep398

example : QuotientRankAtLeast (spanCodes [161,96,20,10]) 17 := plane398UnusedGen_lb17

run_cmd do
  for name in #[``rep398, ``QiushiMatmul.plane398UnusedGen_lb17,
      ``QiushiMatmul.plane398UnusedGenNoModel, ``QiushiMatmul.plane398UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
