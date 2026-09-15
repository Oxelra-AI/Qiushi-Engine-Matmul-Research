import QiushiMat3SubspaceCount

open Matrix BigOperators
open scoped LinearAlgebra.Projectivization
attribute [local instance] Classical.propDecidable Fintype.ofFinite

noncomputable section
namespace QiushiMatmul.FullSubspaceCount

open E11SubspaceCount

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable (W : Submodule F2 Mat3) (hW : Module.finrank F2 W = 2)

include hW

theorem plane_quotient_finrank : Module.finrank F2 (Mat3 ⧸ W) = 7 := by
  have h := Submodule.finrank_quotient_add_finrank W
  rw [hW, mat3_finrank] at h
  omega

theorem plane_quotient_card : Nat.card (Mat3 ⧸ W) = 128 := by
  rw [Module.natCard_eq_pow_finrank (K := F2), plane_quotient_finrank W hW]
  norm_num [F2]

theorem plane_quotient_nonzero_card : Nat.card {q : Mat3 ⧸ W // q ≠ 0} = 127 := by
  have hcard : Fintype.card (Mat3 ⧸ W) = 128 := by
    simpa using plane_quotient_card W hW
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hcard]

theorem plane_quotient_direction_count : Nat.card (ℙ F2 (Mat3 ⧸ W)) = 127 := by
  rw [Projectivization.card'', plane_quotient_card W hW]
  norm_num [F2]

def planeQuotientDimensionCounts : Fin 8 → Nat :=
  ![1, 127, 2667, 11811, 11811, 2667, 127, 1]

theorem plane_quotient_dimension_counts (k : Fin 8) :
    Nat.card (Spaces (Mat3 ⧸ W) k.val) = planeQuotientDimensionCounts k := by
  have h := subspace_count_mul_frameCount (Mat3 ⧸ W) (k := k.val)
    (by rw [plane_quotient_finrank W hW]; omega)
  rw [plane_quotient_finrank W hW] at h
  have hnonzero : frameCount k.val k.val ≠ 0 := by
    fin_cases k <;> norm_num [frameCount, Fin.prod_univ_succ]
  have hnumeric : planeQuotientDimensionCounts k * frameCount k.val k.val =
      frameCount 7 k.val := by
    fin_cases k <;> norm_num [frameCount, planeQuotientDimensionCounts, Fin.prod_univ_succ]
  exact mul_right_cancel₀ hnonzero (h.trans hnumeric.symm)

theorem plane_quotient_all_subspace_count :
    Nat.card (Submodule F2 (Mat3 ⧸ W)) = 29212 := by
  rw [Nat.card_congr (dimensionEquiv (Mat3 ⧸ W) (plane_quotient_finrank W hW)),
    Nat.card_sigma]
  simp_rw [plane_quotient_dimension_counts W hW]
  norm_num [planeQuotientDimensionCounts, Fin.sum_univ_succ]

/-- Exactly the nonzero proper quotient subspaces indexing the report's rows. -/
theorem plane_quotient_nonzero_proper_subspace_count :
    Nat.card {S : Submodule F2 (Mat3 ⧸ W) // S ≠ ⊥ ∧ S ≠ ⊤} = 29210 := by
  have hbt : (⊥ : Submodule F2 (Mat3 ⧸ W)) ≠ ⊤ := by
    intro h
    have hd := congrArg (fun S : Submodule F2 (Mat3 ⧸ W) => Module.finrank F2 S) h
    simp [plane_quotient_finrank W hW] at hd
  have hall : Fintype.card (Submodule F2 (Mat3 ⧸ W)) = 29212 := by
    simpa using plane_quotient_all_subspace_count W hW
  have hends : Fintype.card {S : Submodule F2 (Mat3 ⧸ W) // S = ⊥ ∨ S = ⊤} = 2 := by
    calc
      _ = ({⊥, ⊤} : Finset (Submodule F2 (Mat3 ⧸ W))).card :=
        Fintype.card_of_subtype _ (by intro S; simp)
      _ = 2 := by simp [hbt]
  have hproper : Fintype.card {S : Submodule F2 (Mat3 ⧸ W) // ¬(S = ⊥ ∨ S = ⊤)} =
      29210 := by
    rw [Fintype.card_subtype_compl, hall, hends]
  simpa only [not_or, Nat.card_eq_fintype_card] using hproper

def planeQuotientRowIndex :
    Fin 29210 ≃ {S : Submodule F2 (Mat3 ⧸ W) // S ≠ ⊥ ∧ S ≠ ⊤} :=
  (Fintype.equivFinOfCardEq
    (by simpa using plane_quotient_nonzero_proper_subspace_count W hW)).symm

theorem plane_quotient_row_index_complete
    (S : Submodule F2 (Mat3 ⧸ W)) (hS : S ≠ ⊥ ∧ S ≠ ⊤) :
    ∃! i : Fin 29210, (planeQuotientRowIndex W hW i).val = S := by
  refine ⟨(planeQuotientRowIndex W hW).symm ⟨S, hS⟩, ?_, ?_⟩
  · exact congrArg Subtype.val ((planeQuotientRowIndex W hW).apply_symm_apply ⟨S, hS⟩)
  · intro i hi
    apply (planeQuotientRowIndex W hW).injective
    rw [(planeQuotientRowIndex W hW).apply_symm_apply]
    exact Subtype.ext hi

/-- The row correspondence excludes both endpoints on both sides. -/
def quotientStrictSupermoduleEquiv :
    {S : Submodule F2 (Mat3 ⧸ W) // S ≠ ⊥ ∧ S ≠ ⊤} ≃
      {V : Submodule F2 Mat3 // W < V ∧ V < ⊤} := by
  let e := Submodule.comapMkQRelIso W
  let e' : {S : Submodule F2 (Mat3 ⧸ W) // S ≠ ⊥ ∧ S ≠ ⊤} ≃
      {V : Set.Ici W // V ≠ ⊥ ∧ V ≠ ⊤} :=
    e.toEquiv.subtypeEquiv (by
      intro S
      change (S ≠ ⊥ ∧ S ≠ ⊤) ↔ (e S ≠ ⊥ ∧ e S ≠ ⊤)
      rw [← e.map_bot, ← e.map_top]
      simp only [ne_eq, e.injective.eq_iff])
  refine e'.trans
    { toFun := fun V => ⟨V.val.val, ?_⟩
      invFun := fun V => ⟨⟨V.val, V.property.1.le⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · constructor
    · apply lt_iff_le_not_ge.mpr
      refine ⟨V.val.property, ?_⟩
      intro h
      exact V.property.1 (Subtype.ext (le_antisymm h V.val.property))
    · apply lt_top_iff_ne_top.mpr
      intro h
      exact V.property.2 (Subtype.ext h)
  · constructor
    · intro h
      exact (ne_of_gt V.property.1) (congrArg Subtype.val h)
    · intro h
      exact (ne_of_lt V.property.2) (congrArg Subtype.val h)

theorem plane_strict_supermodule_count :
    Nat.card {V : Submodule F2 Mat3 // W < V ∧ V < ⊤} = 29210 := by
  rw [← Nat.card_congr (quotientStrictSupermoduleEquiv W)]
  exact plane_quotient_nonzero_proper_subspace_count W hW

end QiushiMatmul.FullSubspaceCount
