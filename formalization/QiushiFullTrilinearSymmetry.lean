import QiushiOrbitTransport
import QiushiBilinearSemantics

/-!
The report's full three-parameter coefficient action and its input pullback.
All formulas use the coordinate pairing and the actual `tensorEntry` convention.
The extra right action cancels algebraically; no finite enumeration is used.
-/

open Matrix BigOperators

namespace QiushiMatmul.FullTrilinearSymmetry

noncomputable section

def coordinatePairing (A X : Mat3) : F2 :=
  ∑ a : Coord9, A a.1 a.2 * X a.1 a.2

theorem coordinatePairing_eq_trace (A X : Mat3) :
    coordinatePairing A X = Matrix.trace (A * X.transpose) := by
  simp [coordinatePairing, Fintype.sum_prod_type, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]

/-- Contracting the actual coefficient tensor gives the report's trilinear form. -/
theorem tensorEntry_trace (X Y Z : Mat3) :
    (∑ c : Coord9, (∑ a : Coord9, ∑ b : Coord9,
      X a.1 a.2 * Y b.1 b.2 * tensorEntry a b c) * Z c.1 c.2) =
      Matrix.trace (X * Y * Z.transpose) := by
  simp_rw [tensorEntry_contract]
  exact coordinatePairing_eq_trace (X * Y) Z

private theorem right_dual_cancel (H B C : Mat3) [Invertible H] :
    (B * H.transpose⁻¹) * (C * H).transpose = B * C.transpose := by
  have hc : (H⁻¹).transpose * H.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_inv_of_invertible, Matrix.transpose_one]
  rw [QiushiMatmul.transpose_inv, Matrix.transpose_mul]
  calc
    (B * (H⁻¹).transpose) * (H.transpose * C.transpose) =
        B * ((H⁻¹).transpose * H.transpose) * C.transpose := by
          simp only [Matrix.mul_assoc]
    _ = B * C.transpose := by rw [hc, Matrix.mul_one]

/-- The full coefficient product is conjugate to the original product. -/
theorem transformed_product (U V H A B C : Mat3)
    [Invertible U] [Invertible V] [Invertible H] :
    (U.transpose * A * V.transpose⁻¹) * (V.transpose * B * H.transpose⁻¹) *
        (U⁻¹ * C * H).transpose =
      U.transpose * (A * B * C.transpose) * (U⁻¹).transpose := by
  have h := QiushiMatmul.transformed_product (P := U) (Q := V)
    (A := A) (B := B * H.transpose⁻¹) (C := C * H)
  rw [Matrix.mul_assoc A (B * H.transpose⁻¹), right_dual_cancel] at h
  simpa only [Matrix.mul_assoc] using h

/-- Exact three-parameter coefficient formula from the report. -/
theorem trilinear_action (U V H A B C : Mat3)
    [Invertible U] [Invertible V] [Invertible H] :
    Matrix.trace ((U.transpose * A * V.transpose⁻¹) *
      (V.transpose * B * H.transpose⁻¹) * (U⁻¹ * C * H).transpose) =
      Matrix.trace (A * B * C.transpose) := by
  have h := QiushiMatmul.trilinear_action (P := U) (Q := V)
    A (B * H.transpose⁻¹) (C * H)
  rw [Matrix.mul_assoc A (B * H.transpose⁻¹), right_dual_cancel] at h
  simpa only [actionA, actionB, actionC, Matrix.mul_assoc] using h

/-- The report's corresponding action on input and test matrices. -/
theorem input_trilinear_action (U V H X Y Z : Mat3)
    [Invertible U] [Invertible V] [Invertible H] :
    Matrix.trace ((U * X * V⁻¹) * (V * Y * H⁻¹) *
      (U.transpose⁻¹ * Z * H.transpose).transpose) =
      Matrix.trace (X * Y * Z.transpose) := by
  simpa only [Matrix.transpose_transpose] using
    trilinear_action U.transpose V.transpose H.transpose X Y Z

theorem pairing_sandwich (L R A X : Mat3) :
    coordinatePairing (L.transpose * A * R.transpose) X =
      coordinatePairing A (L * X * R) := by
  rw [coordinatePairing_eq_trace, coordinatePairing_eq_trace]
  calc
    Matrix.trace ((L.transpose * A * R.transpose) * X.transpose) =
        Matrix.trace (L.transpose * (A * (R.transpose * X.transpose))) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((A * (R.transpose * X.transpose)) * L.transpose) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (A * (L * X * R).transpose) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Each coefficient action is the pullback under the actual coordinate pairing. -/
theorem coefficient_pairing_pullback (U V H A B C X Y Z : Mat3)
    [Invertible U] [Invertible V] [Invertible H] :
    coordinatePairing (U.transpose * A * V.transpose⁻¹) X =
        coordinatePairing A (U * X * V⁻¹) ∧
    coordinatePairing (V.transpose * B * H.transpose⁻¹) Y =
        coordinatePairing B (V * Y * H⁻¹) ∧
    coordinatePairing (U⁻¹ * C * H) Z =
        coordinatePairing C (U.transpose⁻¹ * Z * H.transpose) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [QiushiMatmul.transpose_inv] using pairing_sandwich U V⁻¹ A X
  · simpa only [QiushiMatmul.transpose_inv] using pairing_sandwich V H⁻¹ B Y
  · simpa only [QiushiMatmul.transpose_inv, Matrix.transpose_transpose] using
      pairing_sandwich (U⁻¹).transpose H.transpose C Z

end
end QiushiMatmul.FullTrilinearSymmetry
