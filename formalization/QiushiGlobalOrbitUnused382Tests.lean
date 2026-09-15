import QiushiGlobalOrbitUnused382

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [262,68,19,10]) 17 := plane382UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 382))
    (frozenWangTable.lower 382) := rep382
example : plane382UnusedGenConfig.nOcc = 23 := by decide +kernel
example : plane382UnusedGenConfig.nDead = 19 := by decide +kernel
example : plane382UnusedGenConfig.nLive = 12 := by decide +kernel

run_cmd do
  for name in #[``rep382, ``QiushiMatmul.plane382UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
