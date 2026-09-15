import QiushiGlobalOrbitUnused376

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [160,68,19,10]) 17 := plane376UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 376))
    (frozenWangTable.lower 376) := rep376
example : plane376UnusedGenConfig.nOcc = 15 := by decide +kernel
example : plane376UnusedGenConfig.nDead = 10 := by decide +kernel
example : plane376UnusedGenConfig.nLive = 21 := by decide +kernel

run_cmd do
  for name in #[``rep376, ``QiushiMatmul.plane376UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
