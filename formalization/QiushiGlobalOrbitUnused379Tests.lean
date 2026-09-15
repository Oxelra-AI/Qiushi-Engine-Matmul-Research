import QiushiGlobalOrbitUnused379

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [164,68,19,10]) 17 := plane379UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 379))
    (frozenWangTable.lower 379) := rep379
example : plane379UnusedGenConfig.nOcc = 22 := by decide +kernel
example : plane379UnusedGenConfig.nDead = 15 := by decide +kernel
example : plane379UnusedGenConfig.nLive = 16 := by decide +kernel

run_cmd do
  for name in #[``rep379, ``QiushiMatmul.plane379UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
