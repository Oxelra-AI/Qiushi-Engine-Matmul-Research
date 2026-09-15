import QiushiGlobalOrbitUnused307

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [272,96,10,1]) 17 := plane307UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 307))
    (frozenWangTable.lower 307) := rep307
example : plane307UnusedGenConfig.nOcc = 20 := by decide +kernel
example : plane307UnusedGenConfig.nDead = 12 := by decide +kernel
example : plane307UnusedGenConfig.nLive = 19 := by decide +kernel

run_cmd do
  for name in #[``rep307, ``QiushiMatmul.plane307UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
