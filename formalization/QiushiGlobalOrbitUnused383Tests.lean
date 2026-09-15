import QiushiGlobalOrbitUnused383

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [289,68,19,10]) 17 := plane383UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 383))
    (frozenWangTable.lower 383) := rep383
example : plane383UnusedGenConfig.nOcc = 28 := by decide +kernel
example : plane383UnusedGenConfig.nDead = 19 := by decide +kernel
example : plane383UnusedGenConfig.nLive = 12 := by decide +kernel

run_cmd do
  for name in #[``rep383, ``QiushiMatmul.plane383UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
