import QiushiGlobalOrbitUnused87

namespace QiushiMatmul.GlobalOrbit.Unused

example : QuotientRankAtLeast (spanCodes [64,8,4,2,1]) 11 := node87_bound
example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 87))
    (frozenWangTable.lower 87) := rep087
example (i : Fin 9) : QuotientRankAtLeast (spanCodes (sources087 i)) 9 :=
  sources087_rank i
example : ∀ c : Fin 512, ∃ i : Fin 9,
    spanContainsCode (sources087 i) c.val = true := sources087_cover

run_cmd do
  for name in #[``sources087_rank, ``sources087_contain, ``sources087_cover,
      ``node87_bound, ``rep087] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"UNUSED_NODE_AXIOMS {name}: {axioms}"

end QiushiMatmul.GlobalOrbit.Unused
