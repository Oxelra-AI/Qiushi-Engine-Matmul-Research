import QiushiGlobalOrbitUnused356

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [290,96,20,1]) 17 := plane356UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 356))
    (frozenWangTable.lower 356) := rep356
example : plane356UnusedGenConfig.nOcc = 27 := by decide +kernel
example : plane356UnusedGenConfig.nDead = 11 := by decide +kernel
example : plane356UnusedGenConfig.nLive = 20 := by decide +kernel

run_cmd do
  for name in #[``rep356, ``QiushiMatmul.plane356UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
