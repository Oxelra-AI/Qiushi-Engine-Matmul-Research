import QiushiGlobalOrbitUnused372

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [298,224,20,1]) 17 := plane372UnusedGen_lb17
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 372))
    (frozenWangTable.lower 372) := rep372
example : plane372UnusedGenConfig.nOcc = 37 := by decide +kernel
example : plane372UnusedGenConfig.nDead = 5 := by decide +kernel
example : plane372UnusedGenConfig.nLive = 26 := by decide +kernel

run_cmd do
  for name in #[``rep372, ``QiushiMatmul.plane372UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
