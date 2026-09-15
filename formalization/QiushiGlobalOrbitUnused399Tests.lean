import QiushiGlobalOrbitUnused399

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 399))
    (frozenWangTable.lower 399) := rep399

example : QuotientRankAtLeast (spanCodes [164,96,20,10]) 17 := plane399UnusedGen_lb17

run_cmd do
  for name in #[``rep399, ``QiushiMatmul.plane399UnusedGen_lb17,
      ``QiushiMatmul.plane399UnusedGenNoModel, ``QiushiMatmul.plane399UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
