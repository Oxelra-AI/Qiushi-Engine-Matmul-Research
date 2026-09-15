import QiushiGlobalOrbitUnused92

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 92))
    (frozenWangTable.lower 92) := rep092
example : QuotientRankAtLeast (spanCodes [160,80,4,2,1]) 13 :=
  plane92UnusedGen_lb13

example : plane92UnusedGenConfig.nOcc = 11 := by decide +kernel
example : plane92UnusedGenConfig.nDead = 6 := by decide +kernel
example : plane92UnusedGenConfig.nLive = 9 := by decide +kernel

run_cmd do
  for name in #[``rep092, ``QiushiMatmul.plane92UnusedGen_lb13] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
