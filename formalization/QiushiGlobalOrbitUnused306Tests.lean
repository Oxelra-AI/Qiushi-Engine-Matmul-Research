import QiushiGlobalOrbitUnused306

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [132,96,10,1]) 17 := plane306UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 306))
    (frozenWangTable.lower 306) := rep306
example : plane306UnusedGenConfig.nOcc = 30 := by decide +kernel
example : plane306UnusedGenConfig.nDead = 14 := by decide +kernel
example : plane306UnusedGenConfig.nLive = 17 := by decide +kernel

run_cmd do
  for name in #[``rep306, ``QiushiMatmul.plane306UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
