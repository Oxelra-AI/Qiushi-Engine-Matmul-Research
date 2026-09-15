import QiushiCalibrationOrbitBinding

open QiushiMatmul QiushiMatmul.Calibration

example (rs : Fin 29210 → OrbitRecord) (hValid : ∀ j, (rs j).Valid)
    (hBasis : ∀ j, (rs j).basis = CalibrationRows.quotientBasis j)
    (hRow : ∀ j, (rs j).row = tableRow j) :
    ∀ i : Fin 8, ∀ j : Fin 29210,
      frozenWangTable.L0 (actualRows i j).space = (tableRow j).storedLabel i :=
  exactL0_of_records rs hValid hBasis hRow

/-- info: 'QiushiMatmul.Calibration.exactL0_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactL0_of_records

/-- info: 'QiushiMatmul.Calibration.sortFuel_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sortFuel_eq
