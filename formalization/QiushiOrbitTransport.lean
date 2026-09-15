import QiushiDefs

/-!
# Orbit transport for quotient decompositions

This is a replacement candidate for the session file of the same basename.
It keeps the existing `GL₃(F₂) × GL₃(F₂)` action, proves transport by summing
the old quotient identities with the correct pullback weights, and uses the
inverse action in the final lower-bound theorem.
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

/-- The transposed inverse: `(Qᵀ)⁻¹ = (Q⁻¹)ᵀ` for invertible `Q`. -/
lemma transpose_inv {Q : Mat3} [Invertible Q] : Q.transpose⁻¹ = (Q⁻¹).transpose := by
  haveI : Invertible Q.transpose := by
    have h : Q.transpose.det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible Q)
    exact Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr h)
  apply Matrix.inv_eq_right_inv
  calc
    Q.transpose * (Q⁻¹).transpose = (Q⁻¹ * Q).transpose :=
      (Matrix.transpose_mul (Q⁻¹) Q).symm
    _ = (1 : Mat3).transpose :=
      congrArg Matrix.transpose (Matrix.inv_mul_of_invertible (A := Q))
    _ = 1 := Matrix.transpose_one

/-- The transformed matrix product is the indicated conjugate. -/
lemma transformed_product {P Q A B C : Mat3} [Invertible P] [Invertible Q] :
    (P.transpose * A * Q.transpose⁻¹) * (Q.transpose * B) * (P⁻¹ * C).transpose
      = P.transpose * (A * B * C.transpose) * (P⁻¹).transpose := by
  have hcancel : (Q⁻¹).transpose * Q.transpose = 1 := by
    calc
      (Q⁻¹).transpose * Q.transpose = (Q * Q⁻¹).transpose :=
        (Matrix.transpose_mul Q (Q⁻¹)).symm
      _ = (1 : Mat3).transpose :=
        congrArg Matrix.transpose (Matrix.mul_inv_of_invertible (A := Q))
      _ = 1 := Matrix.transpose_one
  rw [transpose_inv, Matrix.transpose_mul]
  calc
    (P.transpose * A * (Q⁻¹).transpose) * (Q.transpose * B) *
          (C.transpose * (P⁻¹).transpose) =
        P.transpose * A * ((Q⁻¹).transpose * Q.transpose) * B * C.transpose *
          (P⁻¹).transpose := by
            simp only [Matrix.mul_assoc]
    _ = P.transpose * A * B * C.transpose * (P⁻¹).transpose := by
          rw [hcancel, Matrix.mul_one]
    _ = P.transpose * (A * B * C.transpose) * (P⁻¹).transpose := by
          simp only [Matrix.mul_assoc]

/-- The action on A-slot matrices: `A ↦ Pᵀ A Q⁻ᵀ`. -/
def actionA (P Q : Mat3) (A : Mat3) : Mat3 :=
  P.transpose * A * Q.transpose⁻¹

/-- The action on B-slot matrices: `B ↦ Qᵀ B`. -/
def actionB (Q : Mat3) (B : Mat3) : Mat3 := Q.transpose * B

/-- The action on C-slot matrices: `C ↦ P⁻¹ C`. -/
def actionC (P : Mat3) (C : Mat3) : Mat3 := P⁻¹ * C

lemma actionA_add (P Q : Mat3) (X Y : Mat3) :
    actionA P Q (X + Y) = actionA P Q X + actionA P Q Y := by
  show P.transpose * (X + Y) * Q.transpose⁻¹ =
    P.transpose * X * Q.transpose⁻¹ + P.transpose * Y * Q.transpose⁻¹
  simp only [mul_add, add_mul]

lemma actionA_smul (P Q : Mat3) (a : F2) (X : Mat3) :
    actionA P Q (a • X) = a • actionA P Q X := by
  show P.transpose * (a • X) * Q.transpose⁻¹ =
    a • (P.transpose * X * Q.transpose⁻¹)
  rw [mul_smul_comm, smul_mul_assoc]

/-- The linear map underlying the A action. -/
def actionALinearMap (P Q : Mat3) : Mat3 →ₗ[F2] Mat3 where
  toFun := actionA P Q
  map_add' := actionA_add P Q
  map_smul' := actionA_smul P Q

/-- The action on A-subspaces. -/
def actionW (P Q : Mat3) (W : Submodule F2 Mat3) : Submodule F2 Mat3 :=
  W.map (actionALinearMap P Q)

/-- The trilinear matrix-multiplication form is preserved by the action. -/
lemma trilinear_action {P Q : Mat3} [Invertible P] [Invertible Q]
    (A B C : Mat3) :
    Matrix.trace ((actionA P Q A) * (actionB Q B) * (actionC P C).transpose) =
      Matrix.trace (A * B * C.transpose) := by
  show (P.transpose * A * Q.transpose⁻¹ * (Q.transpose * B) *
    (P⁻¹ * C).transpose).trace = (A * B * C.transpose).trace
  rw [transformed_product]
  have h1 : (P⁻¹).transpose * P.transpose = 1 := by
    calc
      (P⁻¹).transpose * P.transpose = (P * P⁻¹).transpose :=
        (Matrix.transpose_mul P (P⁻¹)).symm
      _ = (1 : Mat3).transpose :=
        congrArg Matrix.transpose (Matrix.mul_inv_of_invertible (A := P))
      _ = 1 := Matrix.transpose_one
  conv_lhs => rw [Matrix.mul_assoc]
  conv_lhs => rw [Matrix.trace_mul_comm]
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]

/-- The inverse linear operation on the A slot. -/
def pullbackA (P Q : Mat3) (X : Mat3) : Mat3 :=
  (P⁻¹).transpose * X * Q.transpose

lemma pullbackA_add (P Q : Mat3) (X Y : Mat3) :
    pullbackA P Q (X + Y) = pullbackA P Q X + pullbackA P Q Y := by
  show (P⁻¹).transpose * (X + Y) * Q.transpose =
    (P⁻¹).transpose * X * Q.transpose + (P⁻¹).transpose * Y * Q.transpose
  simp only [mul_add, add_mul]

lemma pullbackA_smul (P Q : Mat3) (a : F2) (X : Mat3) :
    pullbackA P Q (a • X) = a • pullbackA P Q X := by
  show (P⁻¹).transpose * (a • X) * Q.transpose =
    a • ((P⁻¹).transpose * X * Q.transpose)
  rw [mul_smul_comm, smul_mul_assoc]

def pullbackALinearMap (P Q : Mat3) : Mat3 →ₗ[F2] Mat3 where
  toFun := pullbackA P Q
  map_add' := pullbackA_add P Q
  map_smul' := pullbackA_smul P Q

lemma pullbackA_sum {ι : Type*} [Fintype ι] (P Q : Mat3) (f : ι → Mat3) :
    pullbackA P Q (∑ i, f i) = ∑ i, pullbackA P Q (f i) := by
  exact map_sum (pullbackALinearMap P Q) f Finset.univ

/-- `pullbackA` is a left inverse to `actionA`. -/
lemma pullbackA_actionA {P Q : Mat3} [Invertible P] [Invertible Q] (X : Mat3) :
    pullbackA P Q (actionA P Q X) = X := by
  have hP : (P⁻¹).transpose * P.transpose = 1 := by
    calc
      (P⁻¹).transpose * P.transpose = (P * P⁻¹).transpose :=
        (Matrix.transpose_mul P (P⁻¹)).symm
      _ = (1 : Mat3).transpose :=
        congrArg Matrix.transpose (Matrix.mul_inv_of_invertible (A := P))
      _ = 1 := Matrix.transpose_one
  have hQ : (Q⁻¹).transpose * Q.transpose = 1 := by
    calc
      (Q⁻¹).transpose * Q.transpose = (Q * Q⁻¹).transpose :=
        (Matrix.transpose_mul Q (Q⁻¹)).symm
      _ = (1 : Mat3).transpose :=
        congrArg Matrix.transpose (Matrix.mul_inv_of_invertible (A := Q))
      _ = 1 := Matrix.transpose_one
  rw [pullbackA, actionA, transpose_inv]
  calc
    (P⁻¹).transpose * (P.transpose * X * (Q⁻¹).transpose) * Q.transpose =
        ((P⁻¹).transpose * P.transpose) * X *
          ((Q⁻¹).transpose * Q.transpose) := by
            simp only [Matrix.mul_assoc]
    _ = X := by rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]

/-- `actionA` is a left inverse to `pullbackA`. -/
lemma actionA_pullbackA {P Q : Mat3} [Invertible P] [Invertible Q] (X : Mat3) :
    actionA P Q (pullbackA P Q X) = X := by
  have hP : P.transpose * (P⁻¹).transpose = 1 := by
    calc
      P.transpose * (P⁻¹).transpose = (P⁻¹ * P).transpose :=
        (Matrix.transpose_mul (P⁻¹) P).symm
      _ = (1 : Mat3).transpose :=
        congrArg Matrix.transpose (Matrix.inv_mul_of_invertible (A := P))
      _ = 1 := Matrix.transpose_one
  have hQ : Q.transpose * (Q⁻¹).transpose = 1 := by
    calc
      Q.transpose * (Q⁻¹).transpose = (Q⁻¹ * Q).transpose :=
        (Matrix.transpose_mul (Q⁻¹) Q).symm
      _ = (1 : Mat3).transpose :=
        congrArg Matrix.transpose (Matrix.inv_mul_of_invertible (A := Q))
      _ = 1 := Matrix.transpose_one
  rw [actionA, pullbackA, transpose_inv]
  calc
    P.transpose * ((P⁻¹).transpose * X * Q.transpose) * (Q⁻¹).transpose =
        (P.transpose * (P⁻¹).transpose) * X *
          (Q.transpose * (Q⁻¹).transpose) := by
            simp only [Matrix.mul_assoc]
    _ = X := by rw [hP, hQ, Matrix.one_mul, Matrix.mul_one]

/-- Closed form of an A-slice.  The row/column order here is worth making
explicit: it is `single c.1 b.1`, not `single b.1 c.1`. -/
lemma tensorASlice_eq_single (b c : Coord9) :
    tensorASlice b c =
      if c.2 = b.2 then Matrix.single c.1 b.1 (1 : F2) else 0 := by
  ext i j
  by_cases h : c.2 = b.2
  · simp [tensorASlice, tensorEntry, Matrix.single, h, and_comm]
  · simp [tensorASlice, tensorEntry, Matrix.single, h]

/-- Split a conjunction inside an `ite` for `simp` use. -/
private lemma ite_and_eq {α : Type*} (p q : Prop) [Decidable p] [Decidable q]
    (a b : α) : (if p ∧ q then a else b) = if p then (if q then a else b) else b := by
  split_ifs <;> simp_all

/-- Evaluate a Matrix-valued double sum pointwise (proved at default transparency). -/
private lemma double_sum_eval (f : I3 → I3 → Mat3) (x y : I3) :
    (∑ i, ∑ j, f i j) x y = ∑ i, ∑ j, f i j x y := by
  erw [Finset.sum_apply, Finset.sum_apply]
  congr 1

/-- Evaluate `(a • M) x y` as `a * M x y` (proved at default transparency). -/
private lemma smul_eval (a : F2) (M : Mat3) (x y : I3) :
    (a • M) x y = a * M x y := by
  erw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]

lemma pullbackA_tensorASlice (P Q : Mat3) (b c : Coord9) :
    pullbackA P Q (tensorASlice b c) =
      ∑ i : I3, ∑ j : I3,
        (Q i b.1 * P⁻¹ c.1 j) • tensorASlice (i, b.2) (j, c.2) := by
  by_cases h : c.2 = b.2
  · -- Positive case: tensorASlice b c = single c.1 b.1 1
    ext x y
    rw [double_sum_eval]
    simp only [smul_eval, pullbackA, tensorASlice_eq_single, h, ite_true,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply,
      ite_and_eq, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]
  · -- Negative case: both sides are 0 at Matrix level
    have h0 : ∀ i j : I3, tensorASlice (i, b.2) (j, c.2) = 0 :=
      fun i j => by simp [tensorASlice_eq_single, h]
    simp [h0, smul_zero, Finset.sum_const_zero,
      pullbackA, tensorASlice_eq_single, h, mul_zero, zero_mul]

/-- Coefficient expansion for the transformed B and C factors. -/
lemma actionBC_coeff (P Q B C : Mat3) (b c : Coord9) :
    actionB Q B b.1 b.2 * actionC P C c.1 c.2 =
      ∑ i : I3, ∑ j : I3,
        (Q i b.1 * P⁻¹ c.1 j) * (B i b.2 * C j c.2) := by
  simp [actionB, actionC, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- The residual appearing in a quotient decomposition. -/
def quotientResidual {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (b c : Coord9) : Mat3 :=
  tensorASlice b c +
    ∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t

/-- The weighted sum of old residuals which is the pullback of one transformed
residual. -/
def weightedResidual {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (P Q : Mat3) (b c : Coord9) : Mat3 :=
  ∑ i : I3, ∑ j : I3,
    (Q i b.1 * P⁻¹ c.1 j) • quotientResidual D (i, b.2) (j, c.2)

/-- Reordering the three finite sums gives exactly the transformed rank-one
part. -/
lemma weighted_decomp_terms {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) (P Q : Mat3) (b c : Coord9) :
    (∑ i : I3, ∑ j : I3,
      (Q i b.1 * P⁻¹ c.1 j) •
        (∑ t : Fin r, (D.B t i b.2 * D.C t j c.2) • D.A t)) =
      ∑ t : Fin r,
        (actionB Q (D.B t) b.1 b.2 * actionC P (D.C t) c.1 c.2) • D.A t := by
  simp_rw [Finset.smul_sum, smul_smul, actionBC_coeff, Finset.sum_smul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- The key identity: the pullback of the transformed residual is a weighted
sum of residuals already known to lie in `W`. -/
lemma pullback_transformed_residual {P Q : Mat3} [Invertible P] [Invertible Q]
    {W : Submodule F2 Mat3} {r : ℕ} (D : QuotientTensorDecomp W r)
    (b c : Coord9) :
    pullbackA P Q
        (tensorASlice b c +
          ∑ t : Fin r,
            (actionB Q (D.B t) b.1 b.2 * actionC P (D.C t) c.1 c.2) •
              actionA P Q (D.A t)) =
      weightedResidual D P Q b c := by
  rw [pullbackA_add, pullbackA_sum]
  simp_rw [pullbackA_smul, pullbackA_actionA]
  rw [pullbackA_tensorASlice]
  unfold weightedResidual quotientResidual
  simp only [smul_add, Finset.sum_add_distrib]
  rw [weighted_decomp_terms]

/-- A quotient decomposition modulo `W` transports to one modulo
`Pᵀ W Q⁻ᵀ`. -/
def transportQuotientDecomp {P Q : Mat3} [Invertible P] [Invertible Q]
    {W : Submodule F2 Mat3} {r : ℕ} (D : QuotientTensorDecomp W r) :
    QuotientTensorDecomp (actionW P Q W) r where
  A := fun t => actionA P Q (D.A t)
  B := fun t => actionB Q (D.B t)
  C := fun t => actionC P (D.C t)
  quotient_identity := by
    intro b c
    let R := weightedResidual D P Q b c
    have hR : R ∈ W := by
      unfold R weightedResidual
      apply Submodule.sum_mem
      intro i _
      apply Submodule.sum_mem
      intro j _
      exact W.smul_mem _ (D.quotient_identity (i, b.2) (j, c.2))
    apply Submodule.mem_map.mpr
    refine ⟨R, hR, ?_⟩
    change actionA P Q R =
      tensorASlice b c +
        ∑ t : Fin r,
          (actionB Q (D.B t) b.1 b.2 * actionC P (D.C t) c.1 c.2) •
            actionA P Q (D.A t)
    calc
      actionA P Q R = actionA P Q
          (pullbackA P Q
            (tensorASlice b c +
              ∑ t : Fin r,
                (actionB Q (D.B t) b.1 b.2 * actionC P (D.C t) c.1 c.2) •
                  actionA P Q (D.A t))) := by
                    apply congrArg (actionA P Q)
                    exact (pullback_transformed_residual D b c).symm
      _ = tensorASlice b c +
            ∑ t : Fin r,
              (actionB Q (D.B t) b.1 b.2 * actionC P (D.C t) c.1 c.2) •
                actionA P Q (D.A t) := actionA_pullbackA _

/-- The inverse action is definitionally the pullback operation. -/
lemma actionA_inv_eq_pullbackA {P Q : Mat3} [Invertible P] [Invertible Q]
    (X : Mat3) : actionA P⁻¹ Q⁻¹ X = pullbackA P Q X := by
  unfold actionA pullbackA
  rw [transpose_inv (Q := Q⁻¹), Matrix.inv_inv_of_invertible]

lemma actionA_inv_actionA {P Q : Mat3} [Invertible P] [Invertible Q]
    (X : Mat3) : actionA P⁻¹ Q⁻¹ (actionA P Q X) = X := by
  rw [actionA_inv_eq_pullbackA, pullbackA_actionA]

/-- Acting by `(P,Q)` and then by `(P⁻¹,Q⁻¹)` returns the original subspace. -/
lemma actionW_inv_actionW {P Q : Mat3} [Invertible P] [Invertible Q]
    (W : Submodule F2 Mat3) : actionW P⁻¹ Q⁻¹ (actionW P Q W) = W := by
  ext X
  constructor
  · intro hX
    change ∃ Y, Y ∈ actionW P Q W ∧ actionA P⁻¹ Q⁻¹ Y = X at hX
    rcases hX with ⟨Y, hY, hYX⟩
    change ∃ Z, Z ∈ W ∧ actionA P Q Z = Y at hY
    rcases hY with ⟨Z, hZ, hZY⟩
    have hXZ : X = Z := by
      rw [← hYX, ← hZY, actionA_inv_actionA]
    exact hXZ.symm ▸ hZ
  · intro hX
    change ∃ Y, Y ∈ actionW P Q W ∧ actionA P⁻¹ Q⁻¹ Y = X
    refine ⟨actionA P Q X, ?_, actionA_inv_actionA X⟩
    change ∃ Z, Z ∈ W ∧ actionA P Q Z = actionA P Q X
    exact ⟨X, hX, rfl⟩

/-- **Orbit invariance of quotient rank.** -/
theorem quotientRankAtLeast_action {P Q : Mat3} [Invertible P] [Invertible Q]
    {W : Submodule F2 Mat3} {n : ℕ} :
    QuotientRankAtLeast W n → QuotientRankAtLeast (actionW P Q W) n := by
  intro h r hr
  constructor
  intro D
  haveI : Invertible (P⁻¹ : Mat3) :=
    { invOf := P
      invOf_mul_self := mul_inv_of_invertible P
      mul_invOf_self := inv_mul_of_invertible P }
  haveI : Invertible (Q⁻¹ : Mat3) :=
    { invOf := Q
      invOf_mul_self := mul_inv_of_invertible Q
      mul_invOf_self := inv_mul_of_invertible Q }
  let Dback := transportQuotientDecomp (P := P⁻¹) (Q := Q⁻¹) D
  have hWW : actionW P⁻¹ Q⁻¹ (actionW P Q W) = W := actionW_inv_actionW W
  have D0 : QuotientTensorDecomp W r := hWW ▸ Dback
  exact (h r hr).false D0

/-- **Orbit invariance of quotient rank (iff form).** -/
theorem quotientRankAtLeast_action_iff {P Q : Mat3} [Invertible P] [Invertible Q]
    {W : Submodule F2 Mat3} {n : ℕ} :
    QuotientRankAtLeast W n ↔ QuotientRankAtLeast (actionW P Q W) n := by
  constructor
  · exact quotientRankAtLeast_action
  · intro h
    haveI : Invertible (P⁻¹ : Mat3) :=
      { invOf := P
        invOf_mul_self := mul_inv_of_invertible P
        mul_invOf_self := inv_mul_of_invertible P }
    haveI : Invertible (Q⁻¹ : Mat3) :=
      { invOf := Q
        invOf_mul_self := mul_inv_of_invertible Q
        mul_invOf_self := inv_mul_of_invertible Q }
    have := @quotientRankAtLeast_action _ _ ‹Invertible (P⁻¹)› ‹Invertible (Q⁻¹)›
      (actionW P Q W) n h
    rwa [actionW_inv_actionW] at this

end QiushiMatmul
end
