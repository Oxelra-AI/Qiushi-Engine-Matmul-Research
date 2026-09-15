import QiushiFrozenL0LinesAffine
import QiushiPlaneOrbitNormalForm

/-! Label consistency is separate from orbit coverage and quotient-rank soundness. -/
namespace QiushiMatmul.FrozenLabel

open FrozenL0Report PlaneOrbit

def LabelConsistent : Prop :=
  ∀ (i j : Fin 496) (W : Submodule F2 Mat3),
    frozenWangTable.OrbitImage i W → frozenWangTable.OrbitImage j W →
      frozenWangLower i = frozenWangLower j

theorem orbit_image_iff_equivalent (i : Fin 496) (W : Submodule F2 Mat3) :
    frozenWangTable.OrbitImage i W ↔ Equivalent (spanCodes (frozenWangBasis i)) W := by
  rw [equivalent_iff_transport]
  constructor
  · rintro ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, tr, he⟩
    let := hP
    let := hQ
    exact ⟨P, Q, Matrix.isUnit_det_of_invertible _, Matrix.isUnit_det_of_invertible _, tr, he⟩
  · rintro ⟨P, Q, hP, hQ, tr, he⟩
    exact ⟨P, Q, ⟨Matrix.invertibleOfIsUnitDet P hP⟩,
      ⟨Matrix.invertibleOfIsUnitDet Q hQ⟩, tr, he⟩

theorem L0_eq_of_equivalent {W V : Submodule F2 Mat3} (h : Equivalent W V) :
    frozenWangTable.L0 W = frozenWangTable.L0 V := by
  classical
  have hi (i : Fin 496) : frozenWangTable.OrbitImage i W ↔ frozenWangTable.OrbitImage i V := by
    rw [orbit_image_iff_equivalent, orbit_image_iff_equivalent]
    exact ⟨fun hw => equivalent_trans hw h, fun hv => equivalent_trans hv (equivalent_symm h)⟩
  unfold FrozenOrbitTable.L0
  simp_rw [hi]

theorem L0_eq_representative (i : Fin 496) {W : Submodule F2 Mat3}
    (h : frozenWangTable.OrbitImage i W) :
    frozenWangTable.L0 W = frozenWangTable.L0 (spanCodes (frozenWangBasis i)) :=
  (L0_eq_of_equivalent ((orbit_image_iff_equivalent i W).mp h)).symm

theorem exact_on_orbit (i : Fin 496)
    (hi : frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i)
    {W : Submodule F2 Mat3} (hW : frozenWangTable.OrbitImage i W) :
    frozenWangTable.L0 W = frozenWangLower i :=
  (L0_eq_representative i hW).trans hi

theorem labels_eq_of_exact_representatives (i j : Fin 496)
    (hi : frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i)
    (hj : frozenWangTable.L0 (spanCodes (frozenWangBasis j)) = frozenWangLower j)
    (W : Submodule F2 Mat3) (hWi : frozenWangTable.OrbitImage i W)
    (hWj : frozenWangTable.OrbitImage j W) : frozenWangLower i = frozenWangLower j :=
  (exact_on_orbit i hi hWi).symm.trans (exact_on_orbit j hj hWj)

theorem exact_of_label_consistent (h : LabelConsistent) (i : Fin 496)
    {W : Submodule F2 Mat3} (hW : frozenWangTable.OrbitImage i W) :
    frozenWangTable.L0 W = frozenWangLower i := by
  apply le_antisymm
  · apply L0_le_of_orbit_labels
    intro j hj
    exact le_of_eq (h j i W hj hW)
  · exact frozenWangTable.lower_le_L0 i hW

theorem label_consistent_iff_exact_representatives :
    LabelConsistent ↔ ∀ i : Fin 496,
      frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i := by
  constructor
  · intro h i
    exact exact_of_label_consistent h i (representative_orbit i)
  · intro h i j W hi hj
    exact labels_eq_of_exact_representatives i j (h i) (h j) W hi hj

def rankSignature (basis : List Nat) : Nat × Nat × Nat × Nat :=
  ((spanEnum basis).card, codeRankCount basis 1, codeRankCount basis 2, codeRankCount basis 3)

theorem rankSignature_eq_of_overlap (i j : Fin 496) (W : Submodule F2 Mat3)
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    rankSignature (frozenWangBasis i) = rankSignature (frozenWangBasis j) := by
  obtain ⟨hci, hri⟩ := orbit_counts i W hi
  obtain ⟨hcj, hrj⟩ := orbit_counts j W hj
  exact congrArg₂ Prod.mk (hci.symm.trans hcj)
    (congrArg₂ Prod.mk ((hri 1).symm.trans (hrj 1))
      (congrArg₂ Prod.mk ((hri 2).symm.trans (hrj 2)) ((hri 3).symm.trans (hrj 3))))

end QiushiMatmul.FrozenLabel
