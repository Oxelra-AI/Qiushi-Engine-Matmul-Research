import QiushiGlobalOrbitUnused20

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 20))
    (frozenWangTable.lower 20) := rep020

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 86))
    (frozenWangTable.lower 86) := rep086

run_cmd do
  for name in #[``rep020, ``rep086] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
