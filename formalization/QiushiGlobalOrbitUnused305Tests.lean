import QiushiGlobalOrbitUnused305

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [258,84,10,1]) 17 := plane305UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 305))
    (frozenWangTable.lower 305) := rep305
example : plane305UnusedGenConfig.nOcc = 84 := by decide +kernel
example : plane305UnusedGenConfig.nDead = 1 := by decide +kernel
example : plane305UnusedGenConfig.nLive = 30 := by decide +kernel

run_cmd do
  for name in #[``rep305, ``QiushiMatmul.plane305UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
