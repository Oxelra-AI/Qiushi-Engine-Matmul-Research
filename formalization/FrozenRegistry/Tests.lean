import FrozenRegistry.Bindings

open Lean Meta Elab Command
open QiushiMatmul QiushiMatmul.FrozenRegistry

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

example : checkedIds.Nodup := by decide
example : checkedIds.length = 496 := by decide
example : ∀ i ∈ checkedIds, i < 496 := by decide
example : spanContainsCode [] 1 = false := by decide
example : spanContainsCode [272, 4, 1] 96 = false := by decide
example : spanContainsCode [96, 2, 1] 272 = false := by decide

#check span_eq_of_checked
#check bind_contained
#check bind_orbit
#check entryDecompOfZeroQuotient
#check zero_quotient_bound
#check orbit416

run_cmd liftTermElabM do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for i in checkedIds do
    let digits := toString i
    let suffix := String.ofList (List.replicate (3 - digits.length) '0') ++ digits
    let name := Name.str `QiushiMatmul.FrozenRegistry ("rep" ++ suffix)
    let info ← getConstInfo name
    let expected ← Lean.Elab.Term.elabTerm (← `(
      QuotientRankAtLeast (spanCodes (frozenWangTable.basis $(quote i)))
        (frozenWangTable.lower $(quote i)))) none
    unless ← isDefEq info.type expected do
      throwError "Wrong representative bound type for {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"REGISTRY_TYPE {name}: {← ppExpr info.type}"
    logInfo m!"REGISTRY_AXIOMS {name}: {axioms}"
  for name in #[``span_le_of_checked, ``span_eq_of_checked, ``bind_exact,
      ``bind_contained, ``bind_orbit, ``entryDecompOfZeroQuotient,
      ``zero_quotient_bound, ``orbit416, ``bound416] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"REGISTRY_HELPER_AXIOMS {name}: {axioms}"
  logInfo m!"REGISTRY_CHECKED {checkedIds.length}"
