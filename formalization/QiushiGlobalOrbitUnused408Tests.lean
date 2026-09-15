import QiushiGlobalOrbitUnused408

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 408))
    (frozenWangTable.lower 408) := rep408

example : QuotientRankAtLeast (spanCodes [262,163,84,10]) 17 := plane408UnusedGen_lb17

run_cmd do
  for name in #[``rep408, ``QiushiMatmul.plane408UnusedGen_lb17,
      ``QiushiMatmul.plane408UnusedGenNoModel, ``QiushiMatmul.plane408UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
