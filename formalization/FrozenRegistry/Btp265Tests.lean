import FrozenRegistry.Btp265Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 265))
    (frozenWangTable.lower 265) := by
  rw [show frozenWangTable.basis 265 = [272, 12, 2, 1] by decide +kernel,
      show frozenWangTable.lower 265 = 16 by decide +kernel]
  exact plane265BtpGen_lb16

run_cmd do
  for name in #[``plane265BtpGen_lb16, ``plane265BtpGenNoModel,
      ``plane265BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP265_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP265_CHECKED"
#check plane265BtpGen_lb16
