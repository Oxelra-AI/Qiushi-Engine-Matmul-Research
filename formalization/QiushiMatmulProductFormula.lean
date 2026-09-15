import QiushiDefs

/-!
# Product formula for the split-flattened matrix-multiplication tensor

This module uses the shared `QiushiDefs` constants and proves
`F(A,B,C) * Pinv * F(A',B',C') = F(A * B' * Cᵀ * A', B, C')`.
-/

open Matrix BigOperators

namespace QiushiMatmul

lemma mul_Pinv_apply (X : SplitMat) (r k : SIdx) :
    (X * Pinv) r k = X r (sw k) := by
  classical
  rw [Matrix.mul_apply]
  have hsingle :
      (∑ b : SIdx, X r b * Pinv b k) = X r (sw k) * Pinv (sw k) k := by
    refine @Finset.sum_eq_single SIdx F2 _ Finset.univ
        (fun b => X r b * Pinv b k) (sw k) ?hzero ?hmiss
    · intro b _ hb
      have hk : k ≠ sw b := by
        intro hk
        apply hb
        simpa [sw_involutive] using (congrArg sw hk).symm
      simp [Pinv, hk]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  rw [hsingle]
  simp [Pinv, sw_involutive]

lemma split_product_entry_after_permutation (A B C A' B' C' : Mat3) (r c : SIdx) :
    (F A B C * Pinv * F A' B' C') r c =
      ∑ k : SIdx, F A B C r (sw k) * F A' B' C' k c := by
  classical
  rw [Matrix.mul_apply]
  simp [mul_Pinv_apply]

/-- Rewrite a sum over the triple index type as three nested sums over `Fin 3`. -/
lemma sum_sidx (f : SIdx → F2) :
    (∑ k : SIdx, f k) = ∑ x : I3, ∑ y : I3, ∑ z : I3, f (x, y, z) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_prod_type]

/-- The complete product formula for split-flattened elementary tensors. -/
theorem product_formula (A B C A' B' C' : Mat3) :
    F A B C * Pinv * F A' B' C' = F (A * B' * C.transpose * A') B C' := by
  classical
  ext ⟨i, br, bc⟩ ⟨j, cr, cc⟩
  rw [split_product_entry_after_permutation]
  rw [sum_sidx]
  simp [F, sw, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

end QiushiMatmul
