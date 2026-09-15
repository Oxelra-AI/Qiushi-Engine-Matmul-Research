import QiushiCalibrationData

open BigOperators

namespace QiushiMatmul.Calibration

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The exact occupation row formula, counting repetitions in the point list. -/
def pointMass {n : Nat} (points : Fin n → Fin 127) (mask : Nat) : Nat :=
  ∑ t, if mask.testBit (points t).val then 1 else 0

/-- List evaluation avoids reducing Finset enumeration in every data row. -/
def pointMassFast {n : Nat} (points : Fin n → Fin 127) (mask : Nat) : Nat :=
  ((List.ofFn points).map fun q => if mask.testBit q.val then 1 else 0).sum

theorem pointMassFast_eq {n : Nat} (points : Fin n → Fin 127) (mask : Nat) :
    pointMassFast points mask = pointMass points mask := by
  simp [pointMassFast, pointMass, List.map_ofFn, List.sum_ofFn]

theorem mass19Eval_eq (i : Fin 8) (mask : Nat) :
    mass19Eval i mask = pointMass (target19Points i) mask := by
  fin_cases i <;> simp only [pointMass, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> rfl

theorem mass23Eval_eq (i : Fin 8) (mask : Nat) :
    mass23Eval i mask = pointMass (projectedPoints i) mask := by
  fin_cases i <;> simp only [pointMass, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> rfl

/-- Literal public row data. `labels` packs eight five-bit LUT values, NOT L0 proofs. -/
structure TableRow where
  mask : Nat
  labels : Nat
  deriving Inhabited, DecidableEq

def TableRow.storedLabel (row : TableRow) (i : Fin 8) : Nat :=
  (row.labels >>> (5 * i.val)) &&& 31

def TableRow.ControlsHold (row : TableRow) : Prop := ∀ i : Fin 8,
  pointMass (target19Points i) row.mask + row.storedLabel i ≤ 19 ∧
  pointMass (projectedPoints i) row.mask + row.storedLabel i ≤ 23

def TableRow.check (row : TableRow) : Bool :=
  (List.ofFn fun i : Fin 8 =>
    decide (mass19Eval i row.mask + row.storedLabel i ≤ 19 ∧
      mass23Eval i row.mask + row.storedLabel i ≤ 23)).all id

theorem TableRow.check_iff (row : TableRow) : row.check = true ↔ row.ControlsHold := by
  simp only [TableRow.check, List.all_eq_true, List.mem_ofFn]
  constructor
  · intro h i
    have hi := h _ ⟨i, rfl⟩
    simpa only [id_eq, decide_eq_true_eq, mass19Eval_eq, mass23Eval_eq] using hi
  · intro h b hb
    obtain ⟨i, rfl⟩ := hb
    simpa only [id_eq, decide_eq_true_eq, mass19Eval_eq, mass23Eval_eq] using h i

theorem controlsHold_of_all_check (rows : List TableRow) (h : rows.all TableRow.check = true)
    (row : TableRow) (hr : row ∈ rows) : row.ControlsHold :=
  row.check_iff.mp (List.all_eq_true.mp h row hr)

end QiushiMatmul.Calibration
