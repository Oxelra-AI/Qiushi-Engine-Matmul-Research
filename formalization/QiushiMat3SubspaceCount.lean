import QiushiE11SubspaceCount

open Matrix BigOperators
attribute [local instance] Classical.propDecidable Fintype.ofFinite

noncomputable section
namespace QiushiMatmul.FullSubspaceCount

open E11SubspaceCount

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Dimension stratification of actual submodules of a finite binary vector space. -/
def dimensionEquiv (V : Type*) [AddCommGroup V] [Module F2 V] [Finite V]
    {n : Nat} (hn : Module.finrank F2 V = n) :
    Submodule F2 V ≃ Σ k : Fin (n + 1), Spaces V k.val where
  toFun S := ⟨⟨Module.finrank F2 S, by
    have h := Submodule.finrank_le S
    rw [hn] at h
    omega⟩, ⟨S, rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨k, hk⟩, S, hS⟩
    dsimp at hS
    subst k
    rfl

theorem mat3_finrank : Module.finrank F2 Mat3 = 9 := by
  simpa using Module.finrank_matrix (R := F2) (M := F2) I3 I3

def mat3DimensionCounts : Fin 10 → Nat :=
  ![1, 511, 43435, 788035, 3309747, 3309747, 788035, 43435, 511, 1]

/-- The numbers count dimension-indexed submodules, not just Gaussian products. -/
theorem mat3_dimension_counts (k : Fin 10) :
    Nat.card (Spaces Mat3 k.val) = mat3DimensionCounts k := by
  have h := subspace_count_mul_frameCount Mat3 (k := k.val)
    (by rw [mat3_finrank]; omega)
  rw [mat3_finrank] at h
  have hnonzero : frameCount k.val k.val ≠ 0 := by
    fin_cases k <;> norm_num [frameCount, Fin.prod_univ_succ]
  have hnumeric : mat3DimensionCounts k * frameCount k.val k.val = frameCount 9 k.val := by
    fin_cases k <;> norm_num [frameCount, mat3DimensionCounts, Fin.prod_univ_succ]
  exact mul_right_cancel₀ hnonzero (h.trans hnumeric.symm)

/-- Includes the zero space and the whole matrix space. -/
theorem mat3_all_subspace_count : Nat.card (Submodule F2 Mat3) = 8283458 := by
  rw [Nat.card_congr (dimensionEquiv Mat3 mat3_finrank), Nat.card_sigma]
  simp_rw [mat3_dimension_counts]
  norm_num [mat3DimensionCounts, Fin.sum_univ_succ]

theorem mat3_two_plane_count :
    Nat.card {W : Submodule F2 Mat3 // Module.finrank F2 W = 2} = 43435 := by
  exact mat3_dimension_counts 2

/-- A semantic enumeration; no assertion about the contents of a historical LUT. -/
def mat3SubspaceIndex : Fin 8283458 ≃ Submodule F2 Mat3 :=
  (Fintype.equivFinOfCardEq (by simpa using mat3_all_subspace_count)).symm

theorem mat3_subspace_index_complete (W : Submodule F2 Mat3) :
    ∃! i : Fin 8283458, mat3SubspaceIndex i = W := by
  refine ⟨mat3SubspaceIndex.symm W, mat3SubspaceIndex.apply_symm_apply W, ?_⟩
  intro i hi
  exact mat3SubspaceIndex.injective (hi.trans (mat3SubspaceIndex.apply_symm_apply W).symm)

end QiushiMatmul.FullSubspaceCount
