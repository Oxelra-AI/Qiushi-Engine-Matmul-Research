import FrozenRegistry.Btp263Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 263))
    (frozenWangTable.lower 263) := by
  rw [show frozenWangTable.basis 263 = [160, 12, 2, 1] by decide +kernel,
      show frozenWangTable.lower 263 = 16 by decide +kernel]
  exact plane263BtpGen_lb16

run_cmd do
  for name in #[``plane263BtpGen_lb16, ``plane263BtpGenNoModel,
      ``plane263BtpGenSourceQRA] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP263_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP263_CHECKED"
#check plane263BtpGen_lb16
