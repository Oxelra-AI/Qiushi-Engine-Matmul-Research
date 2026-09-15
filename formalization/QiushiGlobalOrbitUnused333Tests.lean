import QiushiGlobalOrbitUnused333

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 333))
    (frozenWangTable.lower 333) := rep333

example : QuotientRankAtLeast (spanCodes [298,96,16,1]) 16 := plane333UnusedGen_lb16

run_cmd do
  for name in #[``rep333, ``QiushiMatmul.plane333UnusedGen_lb16,
      ``QiushiMatmul.plane333UnusedGenNoModel, ``QiushiMatmul.plane333UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
