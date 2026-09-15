import Mathlib
import QiushiBSlotDeletion

/-!
# Fold-uniform flattening bound via pigeonhole

The *left-kernel form*: if for every nonzero column vector `y`,
`∑ y_j · M_{ij} ≠ 0` for some row `i`, then any bilinear decomposition has
at least `#columns` summands.  Uses the Fintype pigeonhole theorem over F₂.
-/

open BigOperators Finset Matrix

namespace QiushiMatmul

/-- Pigeonhole for F₂ matrices: more columns than rows ⇒ nontrivial right kernel. -/
theorem exists_ne_zero_mulVec_eq_zero {f r : ℕ}
    (Q : Matrix (Fin r) (Fin f) F2) (hfr : r < f) :
    ∃ y : Fin f → F2, y ≠ 0 ∧ Q *ᵥ y = 0 := by
  have hcard : Fintype.card (Fin r → F2) < Fintype.card (Fin f → F2) := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hfr
  obtain ⟨y₁, y₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (Q *ᵥ ·) hcard
  exact ⟨y₁ - y₂, sub_ne_zero.mpr hne, by
    rw [show Q *ᵥ (y₁ - y₂) = Q *ᵥ y₁ - Q *ᵥ y₂ from map_sub Q.mulVecLin y₁ y₂, heq, sub_self]⟩

variable {β γ V : Type*}
variable [AddCommGroup V] [Module F2 V]

/-- Generic fold-uniform flattening bound for slice-family decompositions.
Given a `BSliceFamilyDecomp` of `S` of length `r`, if the `R × f` evaluation
matrix (defined by row functionals `φ` and column evaluations at `(b,c)` pairs)
has trivial right kernel, then `f ≤ r`. -/
theorem fold_uniform_flattening_bound
    {S : β → γ → V} {r : ℕ} {R f : ℕ}
    (D : BSliceFamilyDecomp S r)
    (φ : Fin R → V →ₗ[F2] F2)
    (cols : Fin f → β × γ)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
           ∃ i : Fin R, ∑ j : Fin f, y j * φ i (S (cols j).1 (cols j).2) ≠ 0) :
    f ≤ r := by
  by_contra hfr
  push Not at hfr
  -- Build the r × f matrix RR where RR(t,j) = B_t(b_j) * C_t(c_j)
  let RR : Matrix (Fin r) (Fin f) F2 := fun t j => D.B t (cols j).1 * D.C t (cols j).2
  -- Pigeonhole: ∃ nonzero y with RR *ᵥ y = 0
  obtain ⟨y, hyne, hRy⟩ := exists_ne_zero_mulVec_eq_zero RR (by omega : r < f)
  -- Extract per-row vanishing of RR *ᵥ y
  have hRy_t : ∀ t : Fin r, ∑ j, D.B t (cols j).1 * D.C t (cols j).2 * y j = 0 := by
    intro t
    have := congr_fun hRy t
    simp only [Pi.zero_apply, mulVec, dotProduct] at this
    exact this
  -- Use the decomposition identity to show ∑ y_j * φ_i(S(b_j, c_j)) = 0 for all i
  obtain ⟨i, hi⟩ := hFK y hyne
  apply hi; clear hi
  -- The sum ∑_j y_j * φ_i(S(b_j,c_j)) = ∑_j y_j * φ_i(∑_t (B_t b_j * C_t c_j) • A_t)
  -- = ∑_j y_j * ∑_t (B_t b_j * C_t c_j) * φ_i(A_t)
  -- = ∑_t φ_i(A_t) * ∑_j (B_t b_j * C_t c_j * y_j)
  -- = ∑_t φ_i(A_t) * 0 = 0
  calc ∑ j : Fin f, y j * φ i (S (cols j).1 (cols j).2)
      = ∑ j, y j * φ i (∑ t : Fin r, (D.B t (cols j).1 * D.C t (cols j).2) • D.A t) := by
        apply Finset.sum_congr rfl; intro j _
        rw [D.identity]
      _ = ∑ j, y j * ∑ t, (D.B t (cols j).1 * D.C t (cols j).2) * φ i (D.A t) := by
        apply Finset.sum_congr rfl; intro j _
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl; intro t _
        rw [map_smul, smul_eq_mul]
      _ = ∑ j, ∑ t, y j * ((D.B t (cols j).1 * D.C t (cols j).2) * φ i (D.A t)) := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
      _ = ∑ t, ∑ j, y j * ((D.B t (cols j).1 * D.C t (cols j).2) * φ i (D.A t)) := by
        rw [Finset.sum_comm]
      _ = ∑ t, φ i (D.A t) * ∑ j, D.B t (cols j).1 * D.C t (cols j).2 * y j := by
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      _ = 0 := by
        apply Finset.sum_eq_zero; intro t _
        rw [hRy_t t, mul_zero]

/-- No-short-decomposition form. -/
theorem no_short_decomp_of_fold_uniform
    {S : β → γ → V} {R f : ℕ}
    (φ : Fin R → V →ₗ[F2] F2)
    (cols : Fin f → β × γ)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
           ∃ i : Fin R, ∑ j : Fin f, y j * φ i (S (cols j).1 (cols j).2) ≠ 0) :
    ∀ r : ℕ, r < f → BSliceFamilyDecomp S r → False := by
  intro r hr D
  exact absurd hr (not_lt.mpr (fold_uniform_flattening_bound D φ cols hFK))

end QiushiMatmul
