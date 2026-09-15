import QiushiGlobalOrbitUnused401

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 401))
    (frozenWangTable.lower 401) := rep401

example : QuotientRankAtLeast (spanCodes [261,96,20,10]) 17 := plane401UnusedGen_lb17

run_cmd do
  for name in #[``rep401, ``QiushiMatmul.plane401UnusedGen_lb17,
      ``QiushiMatmul.plane401UnusedGenNoModel, ``QiushiMatmul.plane401UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
