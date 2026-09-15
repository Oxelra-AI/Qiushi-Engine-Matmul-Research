import QiushiGlobalOrbitUnused20

namespace QiushiMatmul.FrozenRegistry.Seed020

theorem qra12 : QuotientRankAtLeast (spanCodes [96,16,8,4,2,1]) 12 :=
  GlobalOrbit.Unused.node20_bound

end QiushiMatmul.FrozenRegistry.Seed020

run_cmd do
  let name := ``QiushiMatmul.FrozenRegistry.Seed020.qra12
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom {ax} in {name}"
  Lean.logInfo m!"SEED_AXIOMS {name}: {axioms}"
