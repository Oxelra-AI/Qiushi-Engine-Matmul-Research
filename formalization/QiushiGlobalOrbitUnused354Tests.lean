import QiushiGlobalOrbitUnused354

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [136,96,20,1]) 17 := plane354UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 354))
    (frozenWangTable.lower 354) := rep354
example : plane354UnusedGenConfig.nOcc = 30 := by decide +kernel
example : plane354UnusedGenConfig.nDead = 11 := by decide +kernel
example : plane354UnusedGenConfig.nLive = 20 := by decide +kernel

run_cmd do
  for name in #[``rep354, ``QiushiMatmul.plane354UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
