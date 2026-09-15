import QiushiCalibration
import QiushiCalibrationCatalogue

namespace QiushiMatmul.Calibration

open OccupationSystemBridge

/-- The remaining numeric binding obligation. This is a proposition, not an axiom
or a proof that the raw LUT values equal the frozen orbit-maximum L0. -/
def ExactL0 : Prop := ∀ i : Fin 8, ∀ j : Fin 29210,
  frozenWangTable.L0 (actualRows i j).space = (tableRow j).storedLabel i

theorem target19_fullOccupation (hExact : ExactL0) (i : Fin 8) :
    FullOccupation (controlConfig i 19) frozenWangTable.L0 (weight i (target19Points i)) :=
  target19_fullOccupation_of_exactL0 i (actualRows i) (actualRows_mask i)
    (fun U hWU hU => (actualRows_complete i U hWU hU).exists) (hExact i)

theorem projected_fullOccupation (hExact : ExactL0) (i : Fin 8) :
    FullOccupation (controlConfig i 23) frozenWangTable.L0 (weight i (projectedPoints i)) :=
  projected_fullOccupation_of_exactL0 i (actualRows i) (actualRows_mask i)
    (fun U hWU hU => (actualRows_complete i U hWU hU).exists) (hExact i)

end QiushiMatmul.Calibration
