import QiushiGlobalOrbitUnused302

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 302))
    (frozenWangTable.lower 302) := rep302

example : QuotientRankAtLeast (spanCodes [304,68,10,1]) 17 := plane302UnusedGen_lb17

run_cmd do
  for name in #[``rep302, ``QiushiMatmul.plane302UnusedGen_lb17,
      ``QiushiMatmul.plane302UnusedGenNoModel, ``QiushiMatmul.plane302UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
