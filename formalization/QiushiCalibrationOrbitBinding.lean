import QiushiCalibrationActual
import QiushiCalibrationRowL0

namespace QiushiMatmul.Calibration

/-- A checked record for each actual catalogue row discharges the entire L0
binding. The two equalities prevent a certificate from proving another table. -/
theorem exactL0_of_records (rs : Fin 29210 → OrbitRecord)
    (hValid : ∀ j, (rs j).Valid)
    (hBasis : ∀ j, (rs j).basis = CalibrationRows.quotientBasis j)
    (hRow : ∀ j, (rs j).row = tableRow j) : ExactL0 := by
  intro i j
  have hb : ∀ c ∈ CalibrationRows.quotientBasis j, c < 128 := by
    rw [← hBasis j]
    exact (hValid j).1
  rw [actualRows_source i j hb, ← hBasis j, ← hRow j]
  exact orbitRecord_L0 (rs j) (hValid j) i

end QiushiMatmul.Calibration
