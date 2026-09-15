import QiushiGlobalOrbitUnused402

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 402))
    (frozenWangTable.lower 402) := rep402

example : QuotientRankAtLeast (spanCodes [391,96,20,10]) 17 := plane402UnusedGen_lb17

run_cmd do
  for name in #[``rep402, ``QiushiMatmul.plane402UnusedGen_lb17,
      ``QiushiMatmul.plane402UnusedGenNoModel, ``QiushiMatmul.plane402UnusedGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
