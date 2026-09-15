import QiushiGlobalOrbitUnused371

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [290,224,20,1]) 17 := plane371UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 371))
    (frozenWangTable.lower 371) := rep371
example : plane371UnusedGenConfig.nOcc = 38 := by decide +kernel
example : plane371UnusedGenConfig.nDead = 14 := by decide +kernel
example : plane371UnusedGenConfig.nLive = 18 := by decide +kernel

run_cmd do
  for name in #[``rep371, ``QiushiMatmul.plane371UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
