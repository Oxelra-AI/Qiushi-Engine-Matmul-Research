import FrozenRegistry.Btp285Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 285))
    (frozenWangTable.lower 285) := by
  rw [show frozenWangTable.basis 285 = [96, 20, 10, 1] by decide +kernel,
      show frozenWangTable.lower 285 = 17 by decide +kernel]
  exact plane285BtpGen_lb17

run_cmd do
  for name in #[``plane285BtpGen_lb17, ``plane285BtpGenNoModel,
      ``plane285BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP285_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP285_CHECKED"
#check plane285BtpGen_lb17
