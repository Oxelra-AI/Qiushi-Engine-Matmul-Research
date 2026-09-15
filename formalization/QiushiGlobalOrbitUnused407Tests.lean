import QiushiGlobalOrbitUnused407

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 407))
    (frozenWangTable.lower 407) := rep407

example : QuotientRankAtLeast (spanCodes [257,163,84,10]) 17 := plane407UnusedGen_lb17

run_cmd do
  for name in #[``rep407, ``QiushiMatmul.plane407UnusedGen_lb17,
      ``QiushiMatmul.plane407UnusedGenNoModel, ``QiushiMatmul.plane407UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
