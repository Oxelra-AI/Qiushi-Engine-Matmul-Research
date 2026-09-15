import FrozenRegistry.Btp224Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 224))
    (frozenWangTable.lower 224) := by
  rw [show frozenWangTable.basis 224 = [302,132,96,16,1] by decide +kernel,
      show frozenWangTable.lower 224 = 15 by decide +kernel]
  exact plane224BtpGen_lb15

run_cmd do
  for name in #[``plane224BtpGen_lb15, ``plane224BtpGenNoModel,
      ``plane224BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP224_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP224_CHECKED"
#check plane224BtpGen_lb15
