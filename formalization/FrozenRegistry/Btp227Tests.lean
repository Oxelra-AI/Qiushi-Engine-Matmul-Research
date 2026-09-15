import FrozenRegistry.Btp227Final
import QiushiFrozenWangData

open QiushiMatmul

example : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 227))
    (frozenWangTable.lower 227) := by
  rw [show frozenWangTable.basis 227 = [294,140,96,16,1] by decide +kernel,
      show frozenWangTable.lower 227 = 15 by decide +kernel]
  exact plane227BtpGen_lb15

run_cmd do
  for name in #[``plane227BtpGen_lb15, ``plane227BtpGenNoModel,
      ``plane227BtpGenSourceQRA, ``FrozenRegistry.padded_plane_qra] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"BTP227_AXIOMS {name}: {axioms}"
  Lean.logInfo "BTP227_CHECKED"
#check plane227BtpGen_lb15
#check FrozenRegistry.padded_plane_qra
