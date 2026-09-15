import QiushiCalibrationData
import QiushiCalibrationRowsPlane484
import QiushiCalibrationRowsPlane485
import QiushiCalibrationRowsPlane486
import QiushiCalibrationRowsPlane487
import QiushiCalibrationRowsPlane488
import QiushiCalibrationRowsPlane489
import QiushiCalibrationRowsPlane490
import QiushiCalibrationRowsPlane491

namespace QiushiMatmul.Calibration

/-- The independently checked whole-quotient charts, in calibration orbit order. -/
def coordinates : (i : Fin 8) → CalibrationRows.Coordinates (planeBasis i)
  | ⟨0, _⟩ => CalibrationRows.coordinates484
  | ⟨1, _⟩ => CalibrationRows.coordinates485
  | ⟨2, _⟩ => CalibrationRows.coordinates486
  | ⟨3, _⟩ => CalibrationRows.coordinates487
  | ⟨4, _⟩ => CalibrationRows.coordinates488
  | ⟨5, _⟩ => CalibrationRows.coordinates489
  | ⟨6, _⟩ => CalibrationRows.coordinates490
  | ⟨7, _⟩ => CalibrationRows.coordinates491

def coordinateLift (i : Fin 8) : Fin 128 → Fin 512 := (coordinates i).lift
def coordinateLabel (i : Fin 8) : Fin 512 → Fin 128 := (coordinates i).label

end QiushiMatmul.Calibration
