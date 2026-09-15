import QiushiCalibrationOrbitRecords
import QiushiFrozenLabelConsistency

namespace QiushiMatmul.Calibration

theorem rowOrbitCheck_L0 (source : List Nat) (label : Nat) (t : GlobalOrbit.Transition)
    (h : RowOrbitCheck source label t) : frozenWangTable.L0 (spanCodes source) = label :=
  rowOrbitCheck_exact FrozenLabel.L0_exact_of_orbit source label t h

theorem orbitRecord_L0 (r : OrbitRecord) (h : r.Valid) (i : Fin 8) :
    frozenWangTable.L0 (spanCodes (rowSource i r.basis)) = r.row.storedLabel i :=
  orbitRecord_exact FrozenLabel.L0_exact_of_orbit r h i

end QiushiMatmul.Calibration
