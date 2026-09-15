import QiushiCalibrationRowOrbit
import QiushiCalibrationCoordinates
import QiushiCalibrationFormula

namespace QiushiMatmul.Calibration

/-- Producer order: the two plane generators, followed by the lifted quotient
basis in its original order. Reduction modulo 128 is irrelevant on checked bases. -/
def rowSource (i : Fin 8) (basis : List Nat) : List Nat :=
  planeBasis i ++ basis.map (fun c => (coordinateLift i ⟨c % 128, Nat.mod_lt _ (by decide)⟩).val)

structure OrbitRecord where
  basis : List Nat
  row : TableRow
  transports : Fin 8 → GlobalOrbit.Transition

def OrbitRecord.Valid (r : OrbitRecord) : Prop :=
  (∀ c ∈ r.basis, c < 128) ∧ ∀ i : Fin 8,
    RowOrbitCheck (rowSource i r.basis) (r.row.storedLabel i) (r.transports i)

instance (r : OrbitRecord) : Decidable r.Valid :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem orbitRecord_exact
    (hExactOrbit : ∀ k : Fin 496, ∀ U : Submodule F2 Mat3,
      frozenWangTable.OrbitImage k U → frozenWangTable.L0 U = frozenWangLower k)
    (r : OrbitRecord) (h : r.Valid) (i : Fin 8) :
    frozenWangTable.L0 (spanCodes (rowSource i r.basis)) = r.row.storedLabel i :=
  rowOrbitCheck_exact hExactOrbit _ _ _ (h.2 i)

theorem orbitRecords_valid (rs : List OrbitRecord)
    (h : rs.all (fun r => decide r.Valid) = true) (r : OrbitRecord) (hr : r ∈ rs) :
    r.Valid := by
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

end QiushiMatmul.Calibration
