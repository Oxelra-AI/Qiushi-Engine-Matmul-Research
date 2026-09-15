import FrozenRegistry.Bridge
import QiushiFirstRowQuotient

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace QiushiMatmul.FrozenRegistry.Reductions

-- These implications leave their source rank bounds as explicit open goals.
theorem rep086_of_rep020
    (h : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 20))
      (frozenWangTable.lower 20)) :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 86))
      (frozenWangTable.lower 86) := by
  rw [show frozenWangTable.basis 20 = [96, 16, 8, 4, 2, 1] by decide,
    show frozenWangTable.lower 20 = 12 by decide] at h
  rw [show frozenWangTable.basis 86 = [16, 8, 4, 2, 1] by decide,
    show frozenWangTable.lower 86 = 12 by decide]
  exact bind_contained _ _ h (by decide) (by decide)

theorem orbit341 :
    frozenWangTable.OrbitImage 341 (spanCodes [128, 96, 30, 1]) := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 341
    [(128, 16), (96, 290), (30, 100), (1, 1)]
    (codeMat 161) (codeMat 305) (codeMat 305) true
    (by decide) (by decide) (by decide)
    (by rw [show frozenWangTable.basis 341 = [290, 100, 16, 1] by decide]; decide)
    (by rw [show frozenWangTable.basis 341 = [290, 100, 16, 1] by decide]; decide)

theorem rep341_of_rep162
    (h : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 162))
      (frozenWangTable.lower 162)) :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 341))
      (frozenWangTable.lower 341) := by
  rw [show frozenWangTable.basis 162 = [128, 96, 20, 10, 1] by decide,
    show frozenWangTable.lower 162 = 16 by decide] at h
  have htarget := bind_contained [128, 96, 30, 1] [128, 96, 20, 10, 1]
    h (by decide) (Nat.le_refl _)
  exact bind_orbit frozenWangTable 341 orbit341 htarget (by decide)

theorem rep418_of_rep284
    (h : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 284))
      (frozenWangTable.lower 284)) :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 418))
      (frozenWangTable.lower 418) := by
  rw [show frozenWangTable.basis 284 = [68, 20, 10, 1] by decide,
    show frozenWangTable.lower 284 = 17 by decide] at h
  rw [show frozenWangTable.basis 418 = [20, 10, 1] by decide,
    show frozenWangTable.lower 418 = 17 by decide]
  exact bind_contained _ _ h (by decide) (by decide)

theorem rep441_of_rep289
    (h : QuotientRankAtLeast (spanCodes (frozenWangTable.basis 289))
      (frozenWangTable.lower 289)) :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 441))
      (frozenWangTable.lower 441) := by
  rw [show frozenWangTable.basis 289 = [258, 20, 10, 1] by decide,
    show frozenWangTable.lower 289 = 17 by decide] at h
  rw [show frozenWangTable.basis 441 = [258, 20, 1] by decide,
    show frozenWangTable.lower 441 = 17 by decide]
  exact bind_contained _ _ h (by decide) (by decide)

theorem rep410_iff_rectangular :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 410))
      (frozenWangTable.lower 410) ↔
    ∀ r : Nat, RectTensorDecomp r → 15 ≤ r := by
  rw [show frozenWangTable.basis 410 = [4, 2, 1] by decide,
    show frozenWangTable.lower 410 = 15 by decide]
  exact firstRow_quotient_rankAtLeast_iff 15

end QiushiMatmul.FrozenRegistry.Reductions

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[
    ``QiushiMatmul.FrozenRegistry.Reductions.rep086_of_rep020,
    ``QiushiMatmul.FrozenRegistry.Reductions.orbit341,
    ``QiushiMatmul.FrozenRegistry.Reductions.rep341_of_rep162,
    ``QiushiMatmul.FrozenRegistry.Reductions.rep418_of_rep284,
    ``QiushiMatmul.FrozenRegistry.Reductions.rep441_of_rep289,
    ``QiushiMatmul.FrozenRegistry.Reductions.rep410_iff_rectangular] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"REDUCTION_AXIOMS {name}: {axioms}"
  Lean.logInfo "REDUCTION_CHECKED 6"
