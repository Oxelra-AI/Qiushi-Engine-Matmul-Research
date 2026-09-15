import QiushiGlobalOrbitUnused355

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [164,96,20,1]) 17 := plane355UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 355))
    (frozenWangTable.lower 355) := rep355
example : plane355UnusedGenConfig.nOcc = 21 := by decide +kernel
example : plane355UnusedGenConfig.nDead = 9 := by decide +kernel
example : plane355UnusedGenConfig.nLive = 22 := by decide +kernel

run_cmd do
  for name in #[``rep355, ``QiushiMatmul.plane355UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
