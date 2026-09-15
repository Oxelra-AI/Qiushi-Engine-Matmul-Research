import FrozenRegistry.Global

open QiushiMatmul QiushiMatmul.FrozenRegistry

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

example : ∀ i : Fin 496,
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis i))
      (frozenWangTable.lower i) := all_representatives

example : ∀ W : Submodule F2 Mat3,
    QuotientRankAtLeast W (frozenWangTable.L0 W) := L0_rank_sound

example : ∀ W : Submodule F2 Mat3,
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W ∧
      QuotientRankAtLeast W (frozenWangTable.lower i) := coverage_with_rank_bound

#check all_representatives
#check L0_rank_sound
#check coverage_with_rank_bound

run_cmd do
  for name in #[``all_representatives, ``L0_rank_sound, ``coverage_with_rank_bound] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"FROZEN_GLOBAL_AXIOMS {name}: {axioms}"
  Lean.logInfo "FROZEN_GLOBAL_CHECKED 496"
