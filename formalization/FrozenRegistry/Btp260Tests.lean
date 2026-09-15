import FrozenRegistry.Btp260Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 260))
    (frozenWangTable.lower 260) := by
  rw [show frozenWangTable.basis 260 = [80, 12, 2, 1] by decide +kernel,
      show frozenWangTable.lower 260 = 16 by decide +kernel]
  exact plane260BtpGen_lb16

run_cmd do
  for name in #[``plane260BtpGen_lb16, ``plane260BtpGenNoModel,
      ``plane260BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP260_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP260_CHECKED"
#check plane260BtpGen_lb16
