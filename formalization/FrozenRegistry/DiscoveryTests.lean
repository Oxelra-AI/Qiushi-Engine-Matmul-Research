import QiushiMatmul
import FrozenRegistry.AdditionalSources

namespace QiushiMatmul.FrozenRegistry.DiscoveryTests

theorem row416_first : QuotientRankAtLeast (spanCodes [272, 80, 8, 4, 1]) 15 :=
  step113_416_row_qr (0 : Fin 373)

theorem row416_last : QuotientRankAtLeast (spanCodes [264, 128, 66, 34, 24, 4, 1]) 12 :=
  step113_416_row_qr (372 : Fin 373)

theorem row373_first : QuotientRankAtLeast (spanCodes [1, 14, 20, 224, 290]) 16 :=
  step107_o373_row_qr (0 : Fin 57)

theorem row373_last : QuotientRankAtLeast (spanCodes [1, 4, 16, 34, 74, 136, 266]) 12 :=
  step107_o373_row_qr (56 : Fin 57)

theorem row262_first : QuotientRankAtLeast (spanCodes [128, 80, 8, 4, 2, 1]) 12 :=
  step113_262_row_qr (0 : Fin 49)

theorem row262_last : QuotientRankAtLeast (spanCodes [256, 132, 64, 32, 20, 12, 2, 1]) 9 :=
  step113_262_row_qr (48 : Fin 49)

theorem row415_first : QuotientRankAtLeast (spanCodes [273, 32, 9, 4, 2]) 15 :=
  step113_415_row_qr (0 : Fin 101)

theorem row415_last : QuotientRankAtLeast (spanCodes [272, 208, 32, 8, 4, 2, 1]) 9 :=
  step113_415_row_qr (100 : Fin 101)

theorem dead413_last : QuotientRankAtLeast (spanCodes [468, 32, 2, 1]) 15 :=
  plane413GenDeadQRA (40 : Fin 41)

end QiushiMatmul.FrozenRegistry.DiscoveryTests

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row416_first,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row416_last,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row373_first,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row373_last,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row262_first,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row262_last,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row415_first,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.row415_last,
    ``QiushiMatmul.FrozenRegistry.DiscoveryTests.dead413_last]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"DISCOVERY_AXIOMS {name}: {axioms}"
  Lean.logInfo m!"DISCOVERY_CHECKED {names.size}"
