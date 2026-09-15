import FrozenRegistry.Btp287Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 287))
    (frozenWangTable.lower 287) := by
  rw [show frozenWangTable.basis 287 = [160, 20, 10, 1] by decide +kernel,
      show frozenWangTable.lower 287 = 17 by decide +kernel]
  exact plane287BtpGen_lb17

run_cmd do
  for name in #[``plane287BtpGen_lb17, ``plane287BtpGenNoModel,
      ``plane287BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP287_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP287_CHECKED"
#check plane287BtpGen_lb17
