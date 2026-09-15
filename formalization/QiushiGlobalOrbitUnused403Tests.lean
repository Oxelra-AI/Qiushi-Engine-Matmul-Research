import QiushiGlobalOrbitUnused403

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 403))
    (frozenWangTable.lower 403) := rep403

example : QuotientRankAtLeast (spanCodes [304,161,68,10]) 17 := plane403UnusedGen_lb17

run_cmd do
  for name in #[``rep403, ``QiushiMatmul.plane403UnusedGen_lb17,
      ``QiushiMatmul.plane403UnusedGenNoModel, ``QiushiMatmul.plane403UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
