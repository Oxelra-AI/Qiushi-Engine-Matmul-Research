import QiushiCalibrationOrbitBinding
import QiushiCalibrationOrbitTable
import QiushiCalibrationFixtureOccupation
import QiushiCalibrationActualCaps

/-!
Concrete calibration controls for all eight frozen Wang planes. The checked
transports identify all 29,210 row labels with the actual orbit-maximum `L0`;
the complete quotient catalogue then supplies every strict proper superspace.
This does not assert global tensor-rank soundness of the frozen labels.
-/

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem allOrbitRecords_basis : allOrbitRecords.map OrbitRecord.basis =
    CalibrationRows.allData.map CalibrationRows.RowData.basis := by decide +kernel

theorem orbitRecordAt_basis (j : Fin 29210) :
    (orbitRecordAt j).basis = CalibrationRows.quotientBasis j := by
  have h := congrArg (fun xs : List (List Nat) => xs[j.val]?) allOrbitRecords_basis
  have hl : j.val < allOrbitRecords.length := by rw [allOrbitRecords_length]; exact j.isLt
  have hr : j.val < CalibrationRows.allData.length := by
    rw [CalibrationRows.allData_length]; exact j.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem hl,
    List.getElem?_eq_getElem hr, Option.map_some, Option.some.injEq] at h
  exact h

/-- Exact labels for every actual row, with no remaining certificate hypothesis. -/
theorem exactL0 : ExactL0 :=
  exactL0_of_records orbitRecordAt orbitRecordAt_valid orbitRecordAt_basis orbitRecordAt_row

/-- The concrete target-19 occupation controls, not tensor decompositions. -/
theorem target19_feasible (i : Fin 8) :
    OccupationSystemBridge.FullOccupation (controlConfig i 19) frozenWangTable.L0
      (weight i (target19Points i)) :=
  target19_fullOccupation exactL0 i

theorem projected23_feasible (i : Fin 8) :
    OccupationSystemBridge.FullOccupation (controlConfig i 23) frozenWangTable.L0
      (weight i (projectedPoints i)) :=
  projected_fullOccupation exactL0 i

/-- Occupation counts of the actual projected 23-term tensor fixture. -/
theorem projectedFixture_feasible (i : Fin 8) :
    OccupationSystemBridge.FullOccupation (controlConfig i 23) frozenWangTable.L0
      (projectedOccupation i) := by
  rw [projectedOccupation_eq]
  exact projected23_feasible i

theorem actual_cap_distribution (i : Fin 8) :
    Nat.card {q : OccupationSystemBridge.Direction (W i) // L0SingletonCap i q = 0} =
      ![84, 86, 87, 79, 86, 95, 84, 78] i ∧
    Nat.card {q : OccupationSystemBridge.Direction (W i) // L0SingletonCap i q = 1} =
      ![43, 41, 40, 48, 41, 31, 43, 49] i ∧
    Nat.card {q : OccupationSystemBridge.Direction (W i) // L0SingletonCap i q = 2} =
      (if i = 5 then 1 else 0) :=
  L0_cap_distribution exactL0 i

theorem actual_seven_boolean_caps (i : Fin 8) (hi : i ≠ 5)
    (q : OccupationSystemBridge.Direction (W i)) :
    L0SingletonCap i q = 0 ∨ L0SingletonCap i q = 1 :=
  L0_seven_boolean_caps exactL0 i hi q

theorem actual_orbit489_unique_cap_two (q : OccupationSystemBridge.Direction (W 5)) :
    L0SingletonCap 5 q = 2 ↔ q = directionSection 5 1 :=
  L0_orbit489_unique_cap_two exactL0 q

end QiushiMatmul.Calibration
