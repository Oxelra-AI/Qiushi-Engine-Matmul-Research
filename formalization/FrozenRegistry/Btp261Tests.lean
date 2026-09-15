import FrozenRegistry.Btp261Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 261))
    (frozenWangTable.lower 261) := by
  rw [show frozenWangTable.basis 261 = [96, 12, 2, 1] by decide +kernel,
      show frozenWangTable.lower 261 = 16 by decide +kernel]
  exact plane261BtpGen_lb16

run_cmd do
  for name in #[``plane261BtpGen_lb16, ``plane261BtpGenNoModel,
      ``plane261BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP261_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP261_CHECKED"
#check plane261BtpGen_lb16
