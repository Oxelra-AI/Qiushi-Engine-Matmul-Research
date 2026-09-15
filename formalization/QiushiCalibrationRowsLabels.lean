import QiushiCalibrationRows

namespace QiushiMatmul.CalibrationRows

open OccupationSystemBridge

/-- Global agreement of frozen labels on intersecting exact orbits. This is a
separate theorem obligation, not a consequence of quotient row geometry. -/
def OrbitLabelsConsistent (table : FrozenOrbitTable) : Prop :=
  ∀ i j W, table.OrbitImage i W → table.OrbitImage j W → table.lower i = table.lower j

theorem L0_eq_of_consistent_orbit (table : FrozenOrbitTable)
    (hConsistent : OrbitLabelsConsistent table) (i : Fin 496)
    {W : Submodule F2 Mat3} (hOrbit : table.OrbitImage i W) :
    table.L0 W = table.lower i := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    split_ifs with hj
    · exact le_of_eq (hConsistent j i W hj hOrbit)
    · exact Nat.zero_le _
  · exact table.lower_le_L0 i hOrbit

/-- Exact binding of stored row labels to the mathematical orbit expansion. -/
def LabelsExact {bs : List Nat} {C : Coordinates bs} {n : Nat}
    (table : FrozenOrbitTable) (rows : Fin n → Row C) (labels : Fin n → Nat) : Prop :=
  ∀ i, labels i = table.L0 (rows i).space

theorem LabelsExact.of_orbitImages {bs : List Nat} {C : Coordinates bs} {n : Nat}
    (table : FrozenOrbitTable) (rows : Fin n → Row C) (labels : Fin n → Nat)
    (indices : Fin n → Fin 496) (hConsistent : OrbitLabelsConsistent table)
    (hStored : ∀ i, labels i = table.lower (indices i))
    (hOrbit : ∀ i, table.OrbitImage (indices i) (rows i).space) :
    LabelsExact table rows labels := by
  intro i
  rw [hStored i]
  exact (L0_eq_of_consistent_orbit table hConsistent (indices i) (hOrbit i)).symm

/-- Stored numeric caps and mathematical frozen-L0 caps are equivalent only
after an explicit label binding. No external table agreement is implicit. -/
theorem labeled_row_caps_iff {bs : List Nat} {C : Coordinates bs}
    (table : FrozenOrbitTable) (rows : Fin 29210 → Row C) (labels : Fin 29210 → Nat)
    (hCover : ∀ U : Submodule F2 Mat3, spanCodes bs < U → U < ⊤ →
      ∃ i, (rows i).space = U)
    (hLabels : LabelsExact table rows labels) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rows i).mask x ≤ target - (labels i : Int)) ↔
      ∀ U : Submodule F2 Mat3, spanCodes bs < U → U < ⊤ →
        quotientMass (C.weight x) U ≤ target - (table.L0 U : Int) := by
  change (∀ i, labels i = table.L0 (rows i).space) at hLabels
  simp_rw [hLabels]
  exact row_caps_iff rows hCover table.L0 target x

end QiushiMatmul.CalibrationRows
