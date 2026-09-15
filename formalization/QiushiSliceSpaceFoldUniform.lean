import QiushiFoldUniformBound

/-!
# Slice-space fold-uniform flattening bounds

`QiushiFoldUniformBound` proved a point-evaluation version whose columns are
individual `(b,c)` entries.  That theorem is true, but its matrix has rank at
most the quotient-coordinate dimension.  The forced-product residual bounds need
columns indexed by whole slices in the complementary direction.  This file
formalizes the corrected C-slice and B-slice versions.
-/

open BigOperators Finset Matrix

attribute [local instance] Classical.propDecidable

namespace QiushiMatmul

variable {β γ V : Type*}
variable [Fintype β] [Fintype γ]
variable [AddCommGroup V] [Module F2 V]

/-- The C-indexed slice of a B/C-family, viewed as a vector in the B-direction. -/
def cSlice (S : β → γ → V) (c : γ) : β → V := fun b => S b c

/-- The B-indexed slice of a B/C-family, viewed as a vector in the C-direction. -/
def bSlice (S : β → γ → V) (b : β) : γ → V := fun c => S b c

/-- Swap the two exterior slice directions. -/
def swapFamily (S : β → γ → V) : γ → β → V := fun c b => S b c

/-- A decomposition of `S` gives a decomposition of the swapped family with the
B- and C-linear forms exchanged. -/
def swapBSliceFamilyDecomp {S : β → γ → V} {r : ℕ}
    (D : BSliceFamilyDecomp S r) : BSliceFamilyDecomp (swapFamily S) r where
  A := D.A
  B := D.C
  C := D.B
  identity := by
    intro c b
    unfold swapFamily
    simpa [mul_comm] using D.identity b c

/-- Correct fold-uniform bound in the C-slice space.

Columns are C-indices `c_j`; rows are arbitrary linear functionals on the whole
B-slice space `β → V`.  The decomposition factors this matrix through the
`r × f` coefficient matrix `D.C t c_j`, so trivial right kernel of the slice
matrix forces `f ≤ r`. -/
theorem c_slice_space_fold_uniform_bound
    {S : β → γ → V} {r : ℕ} {R f : ℕ}
    (D : BSliceFamilyDecomp S r)
    (ψ : Fin R → (β → V) →ₗ[F2] F2)
    (cols : Fin f → γ)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
           ∃ i : Fin R, ∑ j : Fin f, y j * ψ i (cSlice S (cols j)) ≠ 0) :
    f ≤ r := by
  by_contra hfr
  push_neg at hfr
  let RR : Matrix (Fin r) (Fin f) F2 := fun t j => D.C t (cols j)
  obtain ⟨y, hyne, hRy⟩ := exists_ne_zero_mulVec_eq_zero RR (by omega : r < f)
  have hRy_t : ∀ t : Fin r, ∑ j, D.C t (cols j) * y j = 0 := by
    intro t
    have := congr_fun hRy t
    simp only [Pi.zero_apply, mulVec, dotProduct] at this
    exact this
  obtain ⟨i, hi⟩ := hFK y hyne
  apply hi; clear hi
  calc ∑ j : Fin f, y j * ψ i (cSlice S (cols j))
      = ∑ j, y j * ψ i (∑ t : Fin r,
            (D.C t (cols j)) • (fun b : β => (D.B t b) • D.A t)) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        apply congrArg (ψ i)
        ext b
        unfold cSlice
        calc S b (cols j)
            = ∑ t : Fin r, (D.B t b * D.C t (cols j)) • D.A t := by
              rw [D.identity]
          _ = ∑ t : Fin r, D.C t (cols j) • (D.B t b • D.A t) := by
              apply Finset.sum_congr rfl
              intro t _
              rw [smul_smul]
              congr 1
              ring
          _ = (∑ t : Fin r, D.C t (cols j) • (fun b : β => D.B t b • D.A t)) b := by
              simp only [Finset.sum_apply, Pi.smul_apply]
      _ = ∑ j, y j * ∑ t : Fin r,
            D.C t (cols j) * ψ i (fun b : β => D.B t b • D.A t) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [map_smul, smul_eq_mul]
      _ = ∑ j, ∑ t : Fin r,
            y j * (D.C t (cols j) * ψ i (fun b : β => D.B t b • D.A t)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = ∑ t : Fin r, ∑ j : Fin f,
            y j * (D.C t (cols j) * ψ i (fun b : β => D.B t b • D.A t)) := by
        rw [Finset.sum_comm]
      _ = ∑ t : Fin r,
            ψ i (fun b : β => D.B t b • D.A t) * ∑ j : Fin f, D.C t (cols j) * y j := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        rw [hRy_t t, mul_zero]

/-- No-short-decomposition form for the C-slice-space bound. -/
theorem no_short_decomp_of_c_slice_space_fold_uniform
    {S : β → γ → V} {R f : ℕ}
    (ψ : Fin R → (β → V) →ₗ[F2] F2)
    (cols : Fin f → γ)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
           ∃ i : Fin R, ∑ j : Fin f, y j * ψ i (cSlice S (cols j)) ≠ 0) :
    ∀ r : ℕ, r < f → BSliceFamilyDecomp S r → False := by
  intro r hr D
  exact absurd hr (not_lt.mpr (c_slice_space_fold_uniform_bound D ψ cols hFK))

/-- The B-slice-space version, derived by swapping the two exterior directions. -/
theorem b_slice_space_fold_uniform_bound
    {S : β → γ → V} {r : ℕ} {R f : ℕ}
    (D : BSliceFamilyDecomp S r)
    (ψ : Fin R → (γ → V) →ₗ[F2] F2)
    (cols : Fin f → β)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
           ∃ i : Fin R, ∑ j : Fin f, y j * ψ i (bSlice S (cols j)) ≠ 0) :
    f ≤ r := by
  let Dsw := swapBSliceFamilyDecomp D
  have hFKsw : ∀ y : Fin f → F2, y ≠ 0 →
      ∃ i : Fin R, ∑ j : Fin f, y j * ψ i (cSlice (swapFamily S) (cols j)) ≠ 0 := by
    intro y hy
    obtain ⟨i, hi⟩ := hFK y hy
    refine ⟨i, ?_⟩
    change ∑ j : Fin f, y j * ψ i (bSlice S (cols j)) ≠ 0
    exact hi
  exact c_slice_space_fold_uniform_bound Dsw ψ cols hFKsw

/-- No-short-decomposition form for the B-slice-space bound. -/
theorem no_short_decomp_of_b_slice_space_fold_uniform
    {S : β → γ → V} {R f : ℕ}
    (ψ : Fin R → (γ → V) →ₗ[F2] F2)
    (cols : Fin f → β)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
           ∃ i : Fin R, ∑ j : Fin f, y j * ψ i (bSlice S (cols j)) ≠ 0) :
    ∀ r : ℕ, r < f → BSliceFamilyDecomp S r → False := by
  intro r hr D
  exact absurd hr (not_lt.mpr (b_slice_space_fold_uniform_bound D ψ cols hFK))

end QiushiMatmul
