import QiushiGlobalOrbitUnused380

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [258,68,19,10]) 17 := plane380UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 380))
    (frozenWangTable.lower 380) := rep380
example : plane380UnusedGenConfig.nOcc = 26 := by decide +kernel
example : plane380UnusedGenConfig.nDead = 21 := by decide +kernel
example : plane380UnusedGenConfig.nLive = 10 := by decide +kernel

run_cmd do
  for name in #[``rep380, ``QiushiMatmul.plane380UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
