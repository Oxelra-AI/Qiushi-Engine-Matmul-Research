import FrozenRegistry.Btp410Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 410))
    (frozenWangTable.lower 410) := by
  rw [show frozenWangTable.basis 410 = [4, 2, 1] by decide +kernel,
      show frozenWangTable.lower 410 = 15 by decide +kernel]
  exact plane410BtpGen_lb15

run_cmd do
  for name in #[``plane410BtpGen_lb15, ``plane410BtpGenNoModel,
      ``plane410BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP410_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP410_CHECKED"
#check plane410BtpGen_lb15
