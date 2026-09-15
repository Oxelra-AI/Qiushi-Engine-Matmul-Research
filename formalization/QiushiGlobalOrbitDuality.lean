import QiushiPlaneOrbitFrozenClassification
import QiushiQuotientRestriction

/-! Dimension-complementing duality for the genuine matrix-action orbits. -/
open Matrix BigOperators
namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit QuotientRestriction
noncomputable section

abbrev dual := inputAnnihilator

theorem dual_involutive (W : Space) : dual (dual W) = W := inputAnnihilator_involutive W

theorem dual_dimension (W : Space) :
    Module.finrank F2 (dual W) + Module.finrank F2 W = 9 := by
  have he := (quotientEquiv W).finrank_eq
  rw [Subspace.dual_finrank_eq] at he
  have h := W.finrank_quotient_add_finrank
  rw [he, FullSubspaceCount.mat3_finrank] at h
  exact h

theorem pairing_left (L A X : Mat3) : matrixDual (L * A) X = matrixDual A (L.transpose * X) := by
  simp only [matrixDual_trace, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm L (A * X.transpose), Matrix.mul_assoc]

theorem pairing_transpose (A X : Mat3) : matrixDual A.transpose X = matrixDual A X.transpose := by
  simp only [matrixDual_trace, Matrix.transpose_transpose]
  rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

theorem mem_dual_left (L : Mat3) (W : Space) (X : Mat3) :
    X ∈ dual (leftW L W) ↔ L.transpose * X ∈ dual W := by
  simp only [mem_inputAnnihilator]
  constructor
  · intro h A hA
    rw [← pairing_left]
    exact h _ ⟨A, hA, rfl⟩
  · intro h A hA
    obtain ⟨B, hB, rfl⟩ := hA
    exact (pairing_left L B X).trans (h B hB)

theorem dual_left (L : Mat3) (hL : IsUnit L.det) (W : Space) :
    dual (leftW L W) = leftW L.transpose⁻¹ (dual W) := by
  have hLt : IsUnit L.transpose.det := by simpa using hL
  ext X
  rw [mem_dual_left]
  constructor
  · intro h
    refine ⟨L.transpose * X, h, ?_⟩
    change L.transpose⁻¹ * (L.transpose * X) = X
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLt, Matrix.one_mul]
  · rintro ⟨Y, hY, rfl⟩
    change L.transpose * (L.transpose⁻¹ * Y) ∈ dual W
    rwa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLt, Matrix.one_mul]

theorem dual_transpose (W : Space) : dual (transposeW W) = transposeW (dual W) := by
  ext X
  constructor
  · intro h
    refine ⟨X.transpose, ?_, Matrix.transpose_transpose X⟩
    change X.transpose ∈ inputAnnihilator W
    rw [mem_inputAnnihilator] at h ⊢
    intro A hA
    rw [← pairing_transpose]
    exact h _ ⟨A, hA, rfl⟩
  · rintro ⟨Y, hY, rfl⟩
    change Y ∈ inputAnnihilator W at hY
    rw [mem_inputAnnihilator] at hY ⊢
    rintro A ⟨B, hB, rfl⟩
    change matrixDual B.transpose Y.transpose = 0
    simpa only [pairing_transpose, Matrix.transpose_transpose] using hY B hB

theorem dual_left_equivalent (L : Mat3) (hL : IsUnit L.det) (W : Space) :
    Equivalent (dual W) (dual (leftW L W)) := by
  rw [dual_left L hL W, leftW_eq_actionW]
  apply action_equivalent
  · simpa using Matrix.isUnit_nonsing_inv_det L.transpose (by simpa using hL)
  · simp

theorem dual_action_equivalent (P Q : Mat3) (hP : IsUnit P.det)
    (hQ : IsUnit Q.det) (W : Space) : Equivalent (dual W) (dual (actionW P Q W)) := by
  let : Invertible P := Matrix.invertibleOfIsUnitDet P hP
  let : Invertible Q := Matrix.invertibleOfIsUnitDet Q hQ
  have ht (V : Space) : Equivalent (dual V) (dual (transposeW V)) := by
    rw [dual_transpose]
    exact transpose_equivalent _
  rw [action_factor]
  exact equivalent_trans (ht W) (equivalent_trans
    (dual_left_equivalent _ (Matrix.isUnit_det_of_invertible _) _) (equivalent_trans
      (ht _) (dual_left_equivalent _ (Matrix.isUnit_det_of_invertible _) _)))

theorem dual_equivalent {W V : Space} (h : Equivalent W V) : Equivalent (dual W) (dual V) := by
  induction h with
  | rel W V h =>
    rcases h with ⟨P, Q, hP, hQ, rfl⟩ | rfl
    · exact dual_action_equivalent P Q hP hQ W
    · rw [dual_transpose]
      exact transpose_equivalent _
  | refl W => exact equivalent_refl _
  | symm W V h ih => exact equivalent_symm ih
  | trans U V W h h' ih ih' => exact equivalent_trans ih ih'

theorem dual_equivalent_iff (W V : Space) : Equivalent (dual W) (dual V) ↔ Equivalent W V := by
  constructor
  · intro h
    simpa only [dual_involutive] using dual_equivalent h
  · exact dual_equivalent

def representative (i : Fin 496) : Space := spanCodes (frozenWangBasis i)
def Covered (W : Space) : Prop := ∃ i : Fin 496, frozenWangTable.OrbitImage i W
def CoversDimension (d : Nat) : Prop := ∀ W : Space, Module.finrank F2 W = d → Covered W

theorem frozen_image_iff (i : Fin 496) (W : Space) :
    frozenWangTable.OrbitImage i W ↔ Equivalent (representative i) W := by
  rw [equivalent_iff_transport]
  constructor
  · rintro ⟨P, Q, ⟨hP⟩, ⟨hQ⟩, tr, he⟩
    let := hP
    let := hQ
    exact ⟨P, Q, Matrix.isUnit_det_of_invertible _, Matrix.isUnit_det_of_invertible _, tr, he⟩
  · rintro ⟨P, Q, hP, hQ, tr, he⟩
    exact ⟨P, Q, ⟨Matrix.invertibleOfIsUnitDet P hP⟩,
      ⟨Matrix.invertibleOfIsUnitDet Q hQ⟩, tr, he⟩

theorem covered_of_equivalent {W V : Space} (hW : Covered W) (h : Equivalent W V) : Covered V := by
  obtain ⟨i, hi⟩ := hW
  exact ⟨i, (frozen_image_iff i V).mpr (equivalent_trans ((frozen_image_iff i W).mp hi) h)⟩

/-- A finite table-duality certificate reduces global coverage to dimensions at most four. -/
theorem coverage_of_low_dimensions
    (hdual : ∀ i : Fin 496, Covered (dual (representative i)))
    (hlow : ∀ d : Fin 5, CoversDimension d.val) : ∀ W : Space, Covered W := by
  intro W
  by_cases hd : Module.finrank F2 W ≤ 4
  · exact hlow ⟨Module.finrank F2 W, by omega⟩ W rfl
  · have hdW := dual_dimension W
    have hsmall : Module.finrank F2 (dual W) < 5 := by omega
    obtain ⟨i, hi⟩ := hlow ⟨Module.finrank F2 (dual W), hsmall⟩ (dual W) rfl
    have he := dual_equivalent ((frozen_image_iff i (dual W)).mp hi)
    rw [dual_involutive] at he
    exact covered_of_equivalent (hdual i) he

end
end QiushiMatmul.GlobalOrbit
