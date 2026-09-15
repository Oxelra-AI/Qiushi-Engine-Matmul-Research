import QiushiGlobalOrbitUnused390

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 390))
    (frozenWangTable.lower 390) := rep390

run_cmd do
  for name in #[``rep390, ``QiushiMatmul.plane390UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
