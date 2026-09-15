import FrozenRegistry.Bindings

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace QiushiMatmul.FrozenRegistry

-- Retained interface: the complete checked registry leaves no rank goals.
def remainingTargets : List (Fin 496 × List Nat × Nat) := []

theorem remainingTargets_match : ∀ t ∈ remainingTargets,
    frozenWangTable.basis t.1 = t.2.1 ∧ frozenWangTable.lower t.1 = t.2.2 := by
  decide

theorem remainingTargets_complement :
    remainingTargets.map (fun t => t.1.val) =
      (List.range 496).filter (fun i => !checkedIds.contains i) := by
  decide

theorem remainingTargets_count : remainingTargets.length = 0 := by decide

theorem remainingTarget_iff (t : Fin 496 × List Nat × Nat) (ht : t ∈ remainingTargets) :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis t.1))
      (frozenWangTable.lower t.1) ↔ QuotientRankAtLeast (spanCodes t.2.1) t.2.2 := by
  obtain ⟨hb, hn⟩ := remainingTargets_match t ht
  rw [hb, hn]

end QiushiMatmul.FrozenRegistry

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
    ``QiushiMatmul.FrozenRegistry.remainingTargets_match,
    ``QiushiMatmul.FrozenRegistry.remainingTargets_complement,
    ``QiushiMatmul.FrozenRegistry.remainingTargets_count,
    ``QiushiMatmul.FrozenRegistry.remainingTarget_iff] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"REMAINING_AXIOMS {name}: {axioms}"
  for (i, basis, lower) in QiushiMatmul.FrozenRegistry.remainingTargets do
    Lean.logInfo m!"REMAINING_GOAL {i.val}: QuotientRankAtLeast (spanCodes {basis}) {lower}"
  Lean.logInfo m!"REMAINING_GOALS_CHECKED {QiushiMatmul.FrozenRegistry.remainingTargets.length}"
