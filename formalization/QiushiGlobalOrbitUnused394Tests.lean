import QiushiGlobalOrbitUnused394

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 394))
    (frozenWangTable.lower 394) := rep394

run_cmd do
  for name in #[``rep394, ``QiushiMatmul.plane394UnusedGen_lb17] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
