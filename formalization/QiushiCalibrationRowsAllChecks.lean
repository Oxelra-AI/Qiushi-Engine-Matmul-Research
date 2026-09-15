import QiushiCalibrationRowsAll

open QiushiMatmul QiushiMatmul.CalibrationRows
open QiushiMatmul.OccupationSystemBridge BigOperators

set_option maxRecDepth 200000
set_option maxHeartbeats 80000000

example : allData.length = 29210 := allData_length
example : rowMask 0 = 1 := by decide
example : rowBasis484 0 = [19, 10, 1] := by decide

example (U : Submodule F2 Mat3) (hWU : plane491GenConfig.W < U) (hU : U < ⊤) :
    ∃! i : Fin 29210, spanCodes (rowBasis491 i) = U := rowBasis491_complete U hWU hU

example (i : Fin 29210) (x : Fin 127 → Int) :
    (∑ j : Fin 127 with (rowMask i).testBit j.val = true, x j) =
      quotientMass (coordinates489.weight x) (spanCodes (rowBasis489 i)) := rows489_mass i x

example (L : Submodule F2 Mat3 → Nat) (x : Fin 127 → Int) :
    (∀ i, maskMass (rowMask i) x ≤ (19 : Int) - (L (spanCodes (rowBasis484 i)) : Int)) ↔
      ∀ U : Submodule F2 Mat3, plane484GenConfig.W < U → U < ⊤ →
        quotientMass (coordinates484.weight x) U ≤ (19 : Int) - (L U : Int) :=
  caps484_iff L 19 x

section
attribute [local instance] Classical.propDecidable

example {n : Nat} (codes : Fin n → Fin 512) (weights : Fin n → Int)
    (q : Direction plane491GenConfig.W) :
    coordinates491.weight (coordinates491.labelCounts codes weights) q =
      ∑ t with plane491GenConfig.W.mkQ (codeMat (codes t).val) = q.val, weights t :=
  coordinates491.labelCounts_correct codes weights q

end

example : (⟨[1], 1, 0, 1⟩ : RowData).Valid := by decide
example : ¬(⟨[1], 2, 0, 1⟩ : RowData).Valid := by decide
example : ¬(⟨[1], 2 ^ 127 + 1, 0, 1⟩ : RowData).Valid := by decide
example : ¬(⟨[], 0, 0, 1⟩ : RowData).Valid := by decide
example : ¬(⟨[64, 32, 16, 8, 4, 2, 1], 2 ^ 127 - 1, 0, 1⟩ : RowData).Valid := by decide

#print axioms standardRows_complete
#print axioms rowBasis484_complete
#print axioms rowBasis485_complete
#print axioms rowBasis486_complete
#print axioms rowBasis487_complete
#print axioms rowBasis488_complete
#print axioms rowBasis489_complete
#print axioms rowBasis490_complete
#print axioms rowBasis491_complete
#print axioms caps484_iff
#print axioms caps491_iff
#print axioms Coordinates.labelCounts_correct
#print axioms Coordinates.labelCounts_total
#print axioms LabelsExact.of_orbitImages
#print axioms labeled_row_caps_iff

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Coordinates.plane_finrank, ``Coordinates.row_count, ``Row.transport,
    ``transported_rows_complete, ``spanMask_bit, ``RowData.row,
    ``catalogueRows_distinct, ``allData_valid, ``allData_sorted, ``standardRows_complete,
    ``rowBasis484_complete, ``rowBasis485_complete, ``rowBasis486_complete,
    ``rowBasis487_complete, ``rowBasis488_complete, ``rowBasis489_complete,
    ``rowBasis490_complete, ``rowBasis491_complete,
    ``rows484_mass, ``rows485_mass, ``rows486_mass, ``rows487_mass,
    ``rows488_mass, ``rows489_mass, ``rows490_mass, ``rows491_mass,
    ``caps484_iff, ``caps485_iff, ``caps486_iff, ``caps487_iff,
    ``caps488_iff, ``caps489_iff, ``caps490_iff, ``caps491_iff,
    ``Coordinates.labelCounts_correct, ``Coordinates.labelCounts_nonneg,
    ``Coordinates.labelCounts_total, ``L0_eq_of_consistent_orbit,
    ``LabelsExact.of_orbitImages, ``labeled_row_caps_iff]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for dependency in axioms do
      unless allowed.contains dependency do
        throwError "{decl}: forbidden axiom {dependency}"
  Lean.logInfo m!"Standard-axiom guard passed for {declarations.size} declarations."
