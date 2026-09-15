import QiushiCalibrationFixture
import QiushiCalibrationCoordinates

namespace QiushiMatmul.Calibration

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

def W (i : Fin 8) : Submodule F2 Mat3 := spanCodes (planeBasis i)

def liftCode (i : Fin 8) (q : Fin 127) : Fin 512 :=
  coordinateLift i ⟨q.val + 1, by omega⟩

noncomputable def directionSection (i : Fin 8) (q : Fin 127) :
    OccupationSystemBridge.Direction (W i) := (coordinates i).directionEquiv q

def projectedDecomp (i : Fin 8) : QuotientTensorDecomp (W i) 23 :=
  entrywise_to_quotient fixture (W i)

theorem projection_check : ∀ i t,
    spanContainsCode (planeBasis i)
      (fixtureACode t ^^^ (liftCode i (projectedPoints i t)).val) = true := by
  decide +kernel

theorem projected_A_eq (i : Fin 8) (t : Fin 23) :
    (W i).mkQ ((projectedDecomp i).A t) = (directionSection i (projectedPoints i t)).val := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  have h := spanContainsCode_implies_mem_spanCodes _ _ (projection_check i t)
  have hx := codeMat_xor (fixtureACode t) (liftCode i (projectedPoints i t)).val
  have h' : codeMat (fixtureACode t) + codeMat (liftCode i (projectedPoints i t)).val ∈ W i :=
    hx ▸ h
  simpa only [sub_eq_add_neg, CalibrationRows.matrix_neg_eq_self, projectedDecomp,
    entrywise_to_quotient, fixture, liftCode, coordinateLift] using h'

theorem projected_A_not_mem (i : Fin 8) (t : Fin 23) :
    (projectedDecomp i).A t ∉ W i := by
  intro h
  have hz : (W i).mkQ ((projectedDecomp i).A t) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr h
  rw [projected_A_eq] at hz
  exact (directionSection i (projectedPoints i t)).property hz

theorem planeBasis_frozen : ∀ i : Fin 8,
    planeBasis i = frozenWangBasis ⟨484 + i.val, by omega⟩ := by decide +kernel

end QiushiMatmul.Calibration
