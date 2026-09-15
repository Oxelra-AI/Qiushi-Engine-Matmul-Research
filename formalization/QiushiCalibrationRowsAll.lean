import QiushiCalibrationRowsData
import QiushiCalibrationRowsSpanMap
import QiushiCalibrationRowsProjection
import QiushiCalibrationRowsLabels
import QiushiCalibrationRowsTransport484
import QiushiCalibrationRowsTransport485
import QiushiCalibrationRowsTransport486
import QiushiCalibrationRowsTransport487
import QiushiCalibrationRowsTransport488
import QiushiCalibrationRowsTransport489
import QiushiCalibrationRowsTransport490
import QiushiCalibrationRowsTransport491

namespace QiushiMatmul.CalibrationRows

open OccupationSystemBridge

def rowMask (i : Fin 29210) : Nat := (standardRows i).mask

def quotientBasis (i : Fin 29210) : List Nat :=
  (allData.get ⟨i.val, by rw [allData_length]; exact i.isLt⟩).basis

def rowBasis484 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images484 (codeMat c)))

noncomputable def rows484 (i : Fin 29210) : Row coordinates484 :=
  (standardRows i).transport transport484

theorem rows484_mask (i : Fin 29210) : (rows484 i).mask = rowMask i := rfl

theorem rows484_space (i : Fin 29210) :
    (rows484 i).space = spanCodes (rowBasis484 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images484)

theorem rows484_complete (U : Submodule F2 Mat3)
    (hWU : plane484GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows484 i).space = U :=
  transported_rows_complete transport484 standardRows standardRows_distinct U hWU hU

theorem rowBasis484_complete (U : Submodule F2 Mat3)
    (hWU : plane484GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis484 i) = U := by
  simpa only [rows484_space] using rows484_complete U hWU hU

theorem rows484_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates484.weight x) (spanCodes (rowBasis484 i)) := by
  simpa only [rows484_mask, rows484_space] using (rows484 i).maskMass_eq x

theorem caps484_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis484 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane484GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates484.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows484_mask, rows484_space] using
    row_caps_iff rows484 (fun U hWU hU => (rows484_complete U hWU hU).exists)
      L target x

def rowBasis485 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images485 (codeMat c)))

noncomputable def rows485 (i : Fin 29210) : Row coordinates485 :=
  (standardRows i).transport transport485

theorem rows485_mask (i : Fin 29210) : (rows485 i).mask = rowMask i := rfl

theorem rows485_space (i : Fin 29210) :
    (rows485 i).space = spanCodes (rowBasis485 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images485)

theorem rows485_complete (U : Submodule F2 Mat3)
    (hWU : plane485GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows485 i).space = U :=
  transported_rows_complete transport485 standardRows standardRows_distinct U hWU hU

theorem rowBasis485_complete (U : Submodule F2 Mat3)
    (hWU : plane485GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis485 i) = U := by
  simpa only [rows485_space] using rows485_complete U hWU hU

theorem rows485_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates485.weight x) (spanCodes (rowBasis485 i)) := by
  simpa only [rows485_mask, rows485_space] using (rows485 i).maskMass_eq x

theorem caps485_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis485 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane485GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates485.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows485_mask, rows485_space] using
    row_caps_iff rows485 (fun U hWU hU => (rows485_complete U hWU hU).exists)
      L target x

def rowBasis486 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images486 (codeMat c)))

noncomputable def rows486 (i : Fin 29210) : Row coordinates486 :=
  (standardRows i).transport transport486

theorem rows486_mask (i : Fin 29210) : (rows486 i).mask = rowMask i := rfl

theorem rows486_space (i : Fin 29210) :
    (rows486 i).space = spanCodes (rowBasis486 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images486)

theorem rows486_complete (U : Submodule F2 Mat3)
    (hWU : plane486GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows486 i).space = U :=
  transported_rows_complete transport486 standardRows standardRows_distinct U hWU hU

theorem rowBasis486_complete (U : Submodule F2 Mat3)
    (hWU : plane486GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis486 i) = U := by
  simpa only [rows486_space] using rows486_complete U hWU hU

theorem rows486_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates486.weight x) (spanCodes (rowBasis486 i)) := by
  simpa only [rows486_mask, rows486_space] using (rows486 i).maskMass_eq x

theorem caps486_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis486 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane486GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates486.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows486_mask, rows486_space] using
    row_caps_iff rows486 (fun U hWU hU => (rows486_complete U hWU hU).exists)
      L target x

def rowBasis487 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images487 (codeMat c)))

noncomputable def rows487 (i : Fin 29210) : Row coordinates487 :=
  (standardRows i).transport transport487

theorem rows487_mask (i : Fin 29210) : (rows487 i).mask = rowMask i := rfl

theorem rows487_space (i : Fin 29210) :
    (rows487 i).space = spanCodes (rowBasis487 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images487)

theorem rows487_complete (U : Submodule F2 Mat3)
    (hWU : plane487GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows487 i).space = U :=
  transported_rows_complete transport487 standardRows standardRows_distinct U hWU hU

theorem rowBasis487_complete (U : Submodule F2 Mat3)
    (hWU : plane487GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis487 i) = U := by
  simpa only [rows487_space] using rows487_complete U hWU hU

theorem rows487_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates487.weight x) (spanCodes (rowBasis487 i)) := by
  simpa only [rows487_mask, rows487_space] using (rows487 i).maskMass_eq x

theorem caps487_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis487 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane487GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates487.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows487_mask, rows487_space] using
    row_caps_iff rows487 (fun U hWU hU => (rows487_complete U hWU hU).exists)
      L target x

def rowBasis488 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images488 (codeMat c)))

noncomputable def rows488 (i : Fin 29210) : Row coordinates488 :=
  (standardRows i).transport transport488

theorem rows488_mask (i : Fin 29210) : (rows488 i).mask = rowMask i := rfl

theorem rows488_space (i : Fin 29210) :
    (rows488 i).space = spanCodes (rowBasis488 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images488)

theorem rows488_complete (U : Submodule F2 Mat3)
    (hWU : plane488GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows488 i).space = U :=
  transported_rows_complete transport488 standardRows standardRows_distinct U hWU hU

theorem rowBasis488_complete (U : Submodule F2 Mat3)
    (hWU : plane488GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis488 i) = U := by
  simpa only [rows488_space] using rows488_complete U hWU hU

theorem rows488_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates488.weight x) (spanCodes (rowBasis488 i)) := by
  simpa only [rows488_mask, rows488_space] using (rows488 i).maskMass_eq x

theorem caps488_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis488 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane488GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates488.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows488_mask, rows488_space] using
    row_caps_iff rows488 (fun U hWU hU => (rows488_complete U hWU hU).exists)
      L target x

def rowBasis489 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images489 (codeMat c)))

noncomputable def rows489 (i : Fin 29210) : Row coordinates489 :=
  (standardRows i).transport transport489

theorem rows489_mask (i : Fin 29210) : (rows489 i).mask = rowMask i := rfl

theorem rows489_space (i : Fin 29210) :
    (rows489 i).space = spanCodes (rowBasis489 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images489)

theorem rows489_complete (U : Submodule F2 Mat3)
    (hWU : plane489GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows489 i).space = U :=
  transported_rows_complete transport489 standardRows standardRows_distinct U hWU hU

theorem rowBasis489_complete (U : Submodule F2 Mat3)
    (hWU : plane489GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis489 i) = U := by
  simpa only [rows489_space] using rows489_complete U hWU hU

theorem rows489_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates489.weight x) (spanCodes (rowBasis489 i)) := by
  simpa only [rows489_mask, rows489_space] using (rows489 i).maskMass_eq x

theorem caps489_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis489 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane489GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates489.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows489_mask, rows489_space] using
    row_caps_iff rows489 (fun U hWU hU => (rows489_complete U hWU hU).exists)
      L target x

def rowBasis490 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images490 (codeMat c)))

noncomputable def rows490 (i : Fin 29210) : Row coordinates490 :=
  (standardRows i).transport transport490

theorem rows490_mask (i : Fin 29210) : (rows490 i).mask = rowMask i := rfl

theorem rows490_space (i : Fin 29210) :
    (rows490 i).space = spanCodes (rowBasis490 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images490)

theorem rows490_complete (U : Submodule F2 Mat3)
    (hWU : plane490GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows490 i).space = U :=
  transported_rows_complete transport490 standardRows standardRows_distinct U hWU hU

theorem rowBasis490_complete (U : Submodule F2 Mat3)
    (hWU : plane490GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis490 i) = U := by
  simpa only [rows490_space] using rows490_complete U hWU hU

theorem rows490_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates490.weight x) (spanCodes (rowBasis490 i)) := by
  simpa only [rows490_mask, rows490_space] using (rows490 i).maskMass_eq x

theorem caps490_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis490 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane490GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates490.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows490_mask, rows490_space] using
    row_caps_iff rows490 (fun U hWU hU => (rows490_complete U hWU hU).exists)
      L target x

def rowBasis491 (i : Fin 29210) : List Nat :=
  ([256, 128] ++ quotientBasis i).map
    (fun c => matrixCodeNat (codeLinear images491 (codeMat c)))

noncomputable def rows491 (i : Fin 29210) : Row coordinates491 :=
  (standardRows i).transport transport491

theorem rows491_mask (i : Fin 29210) : (rows491 i).mask = rowMask i := rfl

theorem rows491_space (i : Fin 29210) :
    (rows491 i).space = spanCodes (rowBasis491 i) :=
  spanCodes_map_eq ([256, 128] ++ quotientBasis i) (codeLinear images491)

theorem rows491_complete (U : Submodule F2 Mat3)
    (hWU : plane491GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, (rows491 i).space = U :=
  transported_rows_complete transport491 standardRows standardRows_distinct U hWU hU

theorem rowBasis491_complete (U : Submodule F2 Mat3)
    (hWU : plane491GenConfig.W < U) (hU : U < ⊤) :
    ∃! i, spanCodes (rowBasis491 i) = U := by
  simpa only [rows491_space] using rows491_complete U hWU hU

theorem rows491_mass (i : Fin 29210) (x : Fin 127 → Int) :
    maskMass (rowMask i) x =
      quotientMass (coordinates491.weight x) (spanCodes (rowBasis491 i)) := by
  simpa only [rows491_mask, rows491_space] using (rows491 i).maskMass_eq x

theorem caps491_iff (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ target - (L (spanCodes (rowBasis491 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane491GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates491.weight x) U ≤ target - (L U : Int) := by
  simpa only [rows491_mask, rows491_space] using
    row_caps_iff rows491 (fun U hWU hU => (rows491_complete U hWU hU).exists)
      L target x

end QiushiMatmul.CalibrationRows
