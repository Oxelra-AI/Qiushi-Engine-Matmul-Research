import QiushiGlobalOrbitUnused88

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 88))
    (frozenWangTable.lower 88) := rep088

example : QuotientRankAtLeast (spanCodes [80,8,4,2,1]) 13 :=
  plane88UnusedGen_lb13

example : plane88UnusedGenConfig.nOcc = 13 := by decide +kernel
example : plane88UnusedGenConfig.nDead = 12 := by decide +kernel
example : plane88UnusedGenConfig.nLive = 3 := by decide +kernel

run_cmd do
  for name in #[``rep088, ``QiushiMatmul.plane88UnusedGen_lb13] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
