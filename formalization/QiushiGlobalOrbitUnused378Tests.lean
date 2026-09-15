import QiushiGlobalOrbitUnused378

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [162,68,19,10]) 17 := plane378UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 378))
    (frozenWangTable.lower 378) := rep378
example : plane378UnusedGenConfig.nOcc = 17 := by decide +kernel
example : plane378UnusedGenConfig.nDead = 16 := by decide +kernel
example : plane378UnusedGenConfig.nLive = 15 := by decide +kernel

run_cmd do
  for name in #[``rep378, ``QiushiMatmul.plane378UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
