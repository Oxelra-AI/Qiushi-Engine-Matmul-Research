import QiushiGlobalOrbitUnused304

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 304))
    (frozenWangTable.lower 304) := rep304

example : QuotientRankAtLeast (spanCodes [256,84,10,1]) 16 := plane304UnusedGen_lb16

run_cmd do
  for name in #[``rep304, ``QiushiMatmul.plane304UnusedGen_lb16,
      ``QiushiMatmul.plane304UnusedGenNoModel, ``QiushiMatmul.plane304UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
