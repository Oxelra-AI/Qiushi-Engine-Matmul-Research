import QiushiCalibrationTable
import QiushiCalibrationProjection
import QiushiCalibrationRowsAll
import QiushiCalibrationRowSource
import QiushiCalibrationOrbitTable

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

private theorem orbitRecord_masks :
    allOrbitRecords.map (fun r => r.row.mask) =
      CalibrationRows.allData.map CalibrationRows.RowData.mask := by
  decide +kernel

/-- Equality of the entire ordered mask lists, not an assumed correspondence. -/
theorem catalogue_masks : orderedTable.map TableRow.mask =
    CalibrationRows.allData.map CalibrationRows.RowData.mask := by
  rw [← allOrbitRecords_table, List.map_map]
  exact orbitRecord_masks

theorem tableRow_mask (j : Fin 29210) : (tableRow j).mask = CalibrationRows.rowMask j := by
  have h := congrArg (fun xs : List Nat => xs[j.val]?) catalogue_masks
  have ht : j.val < orderedTable.length := by rw [orderedTable_length]; exact j.isLt
  have hr : j.val < CalibrationRows.allData.length := by
    rw [CalibrationRows.allData_length]; exact j.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem ht, List.getElem?_eq_getElem hr,
    Option.map_some, Option.some.injEq] at h
  exact h

/-- Reuse the complete coordinate-transported row catalogue. -/
noncomputable def actualRows : (i : Fin 8) → Fin 29210 → CalibrationRows.Row (coordinates i)
  | ⟨0, _⟩ => CalibrationRows.rows484
  | ⟨1, _⟩ => CalibrationRows.rows485
  | ⟨2, _⟩ => CalibrationRows.rows486
  | ⟨3, _⟩ => CalibrationRows.rows487
  | ⟨4, _⟩ => CalibrationRows.rows488
  | ⟨5, _⟩ => CalibrationRows.rows489
  | ⟨6, _⟩ => CalibrationRows.rows490
  | ⟨7, _⟩ => CalibrationRows.rows491

theorem actualRows_mask (i : Fin 8) (j : Fin 29210) :
    (actualRows i j).mask = (tableRow j).mask := by
  rw [tableRow_mask]
  fin_cases i <;> rfl

theorem actualRows_complete (i : Fin 8) (U : Submodule F2 Mat3)
    (hWU : W i < U) (hU : U < ⊤) : ∃! j, (actualRows i j).space = U := by
  fin_cases i
  · exact CalibrationRows.rows484_complete U hWU hU
  · exact CalibrationRows.rows485_complete U hWU hU
  · exact CalibrationRows.rows486_complete U hWU hU
  · exact CalibrationRows.rows487_complete U hWU hU
  · exact CalibrationRows.rows488_complete U hWU hU
  · exact CalibrationRows.rows489_complete U hWU hU
  · exact CalibrationRows.rows490_complete U hWU hU
  · exact CalibrationRows.rows491_complete U hWU hU

theorem actualRows_source (i : Fin 8) (j : Fin 29210)
    (hb : ∀ c ∈ CalibrationRows.quotientBasis j, c < 128) :
    (actualRows i j).space = spanCodes (rowSource i (CalibrationRows.quotientBasis j)) := by
  rw [rowSource_eq_map i _ hb]
  fin_cases i
  · exact CalibrationRows.rows484_space j
  · exact CalibrationRows.rows485_space j
  · exact CalibrationRows.rows486_space j
  · exact CalibrationRows.rows487_space j
  · exact CalibrationRows.rows488_space j
  · exact CalibrationRows.rows489_space j
  · exact CalibrationRows.rows490_space j
  · exact CalibrationRows.rows491_space j

end QiushiMatmul.Calibration
