import QiushiPlaneOrbitAction

/-! A direct transport normal form for the full-action equivalence relation. -/
open Matrix
namespace QiushiMatmul.PlaneOrbit
noncomputable section

private def sandwichW (L R : Mat3) (W : Space) : Space :=
  leftW L (transposeW (leftW R.transpose (transposeW W)))

private theorem sandwich_one (W : Space) : sandwichW 1 1 W = W := by
  simp [sandwichW, leftW_one, transposeW_transposeW]

private theorem sandwich_left (M L R : Mat3) (W : Space) :
    leftW M (sandwichW L R W) = sandwichW (M * L) R W := by
  simp only [sandwichW, leftW_mul]

private theorem sandwich_transpose (L R : Mat3) (W : Space) :
    transposeW (sandwichW L R W) = sandwichW R.transpose L.transpose (transposeW W) := by
  simp only [sandwichW, leftW, transposeW, ← Submodule.map_comp]
  congr 1
  ext M i j
  simp [leftMap, Matrix.transpose_mul]
  change ((L * (M * R)).transpose) i j = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem sandwich_action (L R : Mat3) (hR : IsUnit R.det) (W : Space) :
    sandwichW L R W = actionW L.transpose R⁻¹.transpose W := by
  rw [action_factor]
  simp only [Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ hR, sandwichW]

private def SandwichImage (W V : Space) : Prop :=
  ∃ L R : Mat3, IsUnit L.det ∧ IsUnit R.det ∧ ∃ tr : Bool,
    V = sandwichW L R (if tr then transposeW W else W)

private theorem sandwich_closed (W : Space) : GeneratorClosed {V | SandwichImage W V} := by
  rintro g V ⟨L, R, hL, hR, tr, rfl⟩
  by_cases hg : g.val = 3
  · have he (X : Space) : genW g X = transposeW X := by simp [genW, genMap, hg, transposeW]
    rw [he, sandwich_transpose]
    refine ⟨R.transpose, L.transpose, by simpa using hR, by simpa using hL, !tr, ?_⟩
    cases tr <;> simp [transposeW_transposeW]
  · have he (X : Space) : genW g X = leftW (rowMatrix ⟨g.val % 3, Nat.mod_lt _ (by decide)⟩) X := by
      simp [genW, genMap, hg, leftW]
    rw [he, sandwich_left]
    refine ⟨_, R, ?_, hR, tr, rfl⟩
    rw [Matrix.det_mul]
    exact (isUnit_iff_ne_zero.mpr (rowMatrix_det _)).mul hL

/-- A single invertible action, with at most one preceding transpose. -/
def Transport (W V : Space) : Prop :=
  ∃ P Q : Mat3, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ tr : Bool,
    V = actionW P Q (if tr then transposeW W else W)

theorem equivalent_iff_transport (W V : Space) : Equivalent W V ↔ Transport W V := by
  constructor
  · intro h
    have hW : SandwichImage W W := ⟨1, 1, by simp, by simp, false, (sandwich_one W).symm⟩
    obtain ⟨L, R, hL, hR, tr, he⟩ := (equivalent_mem_iff (sandwich_closed W) h).mp hW
    let : Invertible R := Matrix.invertibleOfIsUnitDet R hR
    refine ⟨L.transpose, R⁻¹.transpose, by simpa using hL,
      Matrix.isUnit_det_of_invertible _, tr, ?_⟩
    exact he.trans (sandwich_action L R hR _)
  · rintro ⟨P, Q, hP, hQ, tr, rfl⟩
    have ht : Equivalent W (if tr then transposeW W else W) := by
      cases tr
      · exact equivalent_refl W
      · exact transpose_equivalent W
    exact equivalent_trans ht (action_equivalent _ P Q hP hQ)

end
end QiushiMatmul.PlaneOrbit
