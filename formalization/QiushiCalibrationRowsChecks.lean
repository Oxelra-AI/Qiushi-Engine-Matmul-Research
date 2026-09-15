import QiushiCalibrationRowsPlane484
import QiushiCalibrationRowsPlane485
import QiushiCalibrationRowsPlane486
import QiushiCalibrationRowsPlane487
import QiushiCalibrationRowsPlane488
import QiushiCalibrationRowsPlane489
import QiushiCalibrationRowsPlane490
import QiushiCalibrationRowsPlane491

open QiushiMatmul QiushiMatmul.CalibrationRows
open QiushiMatmul.OccupationSystemBridge BigOperators

example (j : Fin 127) :
    (coordinates484.directionEquiv j).val =
      plane484GenConfig.W.mkQ (codeMat (lift484 ⟨j.val + 1, by omega⟩).val) := rfl

example (c : Fin 512) :
    coordinates491.quotientEquiv (label491 c) =
      plane491GenConfig.W.mkQ (codeMat c.val) := label491_correct c

example (x : Fin 127 → Int) :
    (∑ q : Direction plane488GenConfig.W, coordinates488.weight x q) = ∑ j, x j :=
  coordinates488.weight_total x

example {bs : List Nat} (C : Coordinates bs) (row : Row C) (x : Fin 127 → Int) :
    (∑ j : Fin 127 with row.mask.testBit j.val = true, x j) =
      quotientMass (C.weight x) row.space := row.maskMass_eq x

-- Bit zero is label one; labels zero and 127 are not off by one.
example : lift484 1 = 1 := by decide
example : lift484 127 = 487 := by decide
example : label484 19 = 0 := by decide
example : label491 163 = 0 := by decide
example : label491 84 = 0 := by decide
example : maskMass 0 (fun _ => 3) = 0 := by decide
example : maskMass 1 (fun _ => 3) = 3 := by decide

#print axioms Coordinates.directionEquiv
#print axioms Coordinates.label_correct
#print axioms Row.ofCheck
#print axioms Row.maskMass_eq
#print axioms rows_complete
#print axioms fullOccupation_iff
#print axioms coordinates484
#print axioms coordinates485
#print axioms coordinates486
#print axioms coordinates487
#print axioms coordinates488
#print axioms coordinates489
#print axioms coordinates490
#print axioms coordinates491

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Coordinates.quotientEquiv, ``Coordinates.directionEquiv,
    ``Coordinates.label_correct, ``Coordinates.label_eq_zero_iff,
    ``Coordinates.weight_nonneg_iff, ``Coordinates.weight_total,
    ``mask_membership_of_check, ``Row.ofCheck, ``Row.maskMass_eq,
    ``row_space_injective, ``rows_complete, ``row_caps_iff, ``fullOccupation_iff,
    ``coordinates484, ``coordinates485, ``coordinates486, ``coordinates487,
    ``coordinates488, ``coordinates489, ``coordinates490, ``coordinates491]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for dependency in axioms do
      unless allowed.contains dependency do
        throwError "{decl}: forbidden axiom {dependency}"
  Lean.logInfo m!"Standard-axiom guard passed for {declarations.size} declarations."
