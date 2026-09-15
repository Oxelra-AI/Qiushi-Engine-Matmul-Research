import QiushiGlobalOrbitUnused321

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 321))
    (frozenWangTable.lower 321) := rep321

example : QuotientRankAtLeast (spanCodes [306,160,10,1]) 17 := plane321UnusedGen_lb17

run_cmd do
  for name in #[``rep321, ``QiushiMatmul.plane321UnusedGen_lb17,
      ``QiushiMatmul.plane321UnusedGenNoModel, ``QiushiMatmul.plane321UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
