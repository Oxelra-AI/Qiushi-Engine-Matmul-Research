import FrozenRegistry.Btp420Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 420))
    (frozenWangTable.lower 420) := by
  rw [show frozenWangTable.basis 420 = [68, 10, 1] by decide +kernel,
      show frozenWangTable.lower 420 = 18 by decide +kernel]
  exact plane420BtpGen_lb18

run_cmd do
  for name in #[``plane420BtpGen_lb18, ``plane420BtpGenNoModel,
      ``plane420BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP420_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP420_CHECKED"
#check plane420BtpGen_lb18
