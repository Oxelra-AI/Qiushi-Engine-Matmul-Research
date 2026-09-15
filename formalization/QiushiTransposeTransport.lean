import QiushiDefs

/-!
# Transpose transport for quotient decompositions

The transpose automorphism `(A,B,C) ↦ (Aᵀ,C,B)` preserves `tr(ABCᵀ)`.
A `QuotientTensorDecomp W r` becomes a `QuotientTensorDecomp (transposeW W) r`
by transposing each `A_t` and swapping `B_t ↔ C_t`.

Combined with orbit transport, this handles the full `GL₃×GL₃ ⋊ ℤ/2` action.
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

-- ============================================================================
-- Transpose linear map
-- ============================================================================

/-- Transpose as an F₂-linear map on 3×3 matrices. -/
def transposeLinearMap : Mat3 →ₗ[F2] Mat3 where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' := fun c A => by
    ext i j; simp only [Matrix.transpose_apply, Matrix.smul_apply, RingHom.id_apply]

@[simp] lemma transposeLinearMap_apply (M : Mat3) :
    transposeLinearMap M = M.transpose := rfl

/-- The transpose action on A-subspaces: `W ↦ Wᵀ`. -/
def transposeW (W : Submodule F2 Mat3) : Submodule F2 Mat3 :=
  W.map transposeLinearMap

-- ============================================================================
-- transposeW is an involution
-- ============================================================================

lemma transposeW_transposeW (W : Submodule F2 Mat3) :
    transposeW (transposeW W) = W := by
  ext X; constructor
  · intro hX
    change ∃ Y, Y ∈ transposeW W ∧ transposeLinearMap Y = X at hX
    obtain ⟨Y, hY, hYX⟩ := hX
    change ∃ Z, Z ∈ W ∧ transposeLinearMap Z = Y at hY
    obtain ⟨Z, hZ, hZY⟩ := hY
    have : X = Z := by
      rw [← hYX, ← hZY]; show Z.transpose.transpose = Z
      exact Matrix.transpose_transpose Z
    exact this ▸ hZ
  · intro hX
    change ∃ Y, Y ∈ transposeW W ∧ transposeLinearMap Y = X
    exact ⟨X.transpose, ⟨X, hX, rfl⟩,
      show X.transpose.transpose = X from Matrix.transpose_transpose X⟩

-- ============================================================================
-- Tensor slice symmetry under transpose
-- ============================================================================

/-- The A-slice transpose identity: `(tensorASlice b c)ᵀ = tensorASlice c b`. -/
lemma tensorASlice_transpose (b c : Coord9) :
    (tensorASlice b c).transpose = tensorASlice c b := by
  ext i j
  show tensorASlice b c j i = tensorASlice c b i j
  simp only [tensorASlice, tensorEntry]
  -- Both sides are `if ... then 1 else 0` with equivalent conditions
  rcases Decidable.em (b.1 = i) with hi | hi <;>
  rcases Decidable.em (c.1 = j) with hj | hj <;>
  rcases Decidable.em (c.2 = b.2) with hk | hk <;>
  simp_all [eq_comm]

-- ============================================================================
-- Helper: transpose distributes over scalar-matrix sums
-- ============================================================================

private lemma transpose_sum_smul {r : ℕ} (f : Fin r → F2) (g : Fin r → Mat3) :
    transposeLinearMap (∑ t : Fin r, f t • g t) =
    ∑ t : Fin r, f t • transposeLinearMap (g t) := by
  simp only [map_sum, map_smul]

-- ============================================================================
-- Transpose of a quotient decomposition
-- ============================================================================

/-- A quotient decomposition of `W` gives one of `transposeW W` by
transposing each A-factor and swapping B ↔ C. -/
def transposeQuotientDecomp {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r) :
    QuotientTensorDecomp (transposeW W) r where
  A := fun t => (D.A t).transpose
  B := fun t => D.C t
  C := fun t => D.B t
  quotient_identity := by
    intro b c
    -- Start from the original identity at swapped arguments (c, b):
    have orig := D.quotient_identity c b
    -- Apply transposeLinearMap to get membership in transposeW W
    have hmem : transposeLinearMap (tensorASlice c b +
        ∑ t : Fin r, (D.B t c.1 c.2 * D.C t b.1 b.2) • D.A t) ∈ transposeW W :=
      Submodule.mem_map.mpr ⟨_, orig, rfl⟩
    -- Simplify transposeLinearMap application using linearity
    rw [map_add, transposeLinearMap_apply, tensorASlice_transpose,
        transpose_sum_smul] at hmem
    simp only [transposeLinearMap_apply] at hmem
    -- hmem : tensorASlice b c + ∑ t, (D.B t c.1 c.2 * D.C t b.1 b.2) • (D.A t).transpose ∈ ...
    -- Goal has D.C t b.1 b.2 * D.B t c.1 c.2 (swapped scalars)
    -- The two sums differ only in scalar order: mul_comm in F₂
    have hcomm : ∀ x : Fin r, D.C x b.1 b.2 * D.B x c.1 c.2 =
        D.B x c.1 c.2 * D.C x b.1 b.2 := fun x => mul_comm _ _
    simp_rw [hcomm]
    exact hmem

-- ============================================================================
-- QuotientRankAtLeast is invariant under transpose
-- ============================================================================

/-- Orbit invariance of quotient rank under transpose. -/
theorem quotientRankAtLeast_transpose {W : Submodule F2 Mat3} {n : ℕ} :
    QuotientRankAtLeast W n → QuotientRankAtLeast (transposeW W) n := by
  intro h r hr; constructor; intro D
  let D' := transposeQuotientDecomp D
  have hWW : transposeW (transposeW W) = W := transposeW_transposeW W
  exact (h r hr).false (hWW ▸ D')

/-- Orbit invariance of quotient rank under transpose (iff form). -/
theorem quotientRankAtLeast_transpose_iff {W : Submodule F2 Mat3} {n : ℕ} :
    QuotientRankAtLeast W n ↔ QuotientRankAtLeast (transposeW W) n := by
  constructor
  · exact quotientRankAtLeast_transpose
  · intro h
    have := @quotientRankAtLeast_transpose (transposeW W) n h
    rwa [transposeW_transposeW] at this

-- ============================================================================
-- spanCodes interaction: transposeW (spanCodes L) relates to transposed codes
-- ============================================================================

/-- Bit-level transpose of a 9-bit row-major matrix code.
Swaps bit positions: 1↔3, 2↔6, 5↔7 (the off-diagonal positions). -/
def transposeCode (n : Nat) : Nat :=
  (n &&& 1) |||                              -- bit 0 stays
  (((n >>> 3) &&& 1) <<< 1) |||             -- bit 3 → bit 1
  (((n >>> 6) &&& 1) <<< 2) |||             -- bit 6 → bit 2
  (((n >>> 1) &&& 1) <<< 3) |||             -- bit 1 → bit 3
  (((n >>> 4) &&& 1) <<< 4) |||             -- bit 4 stays
  (((n >>> 7) &&& 1) <<< 5) |||             -- bit 7 → bit 5
  (((n >>> 2) &&& 1) <<< 6) |||             -- bit 2 → bit 6
  (((n >>> 5) &&& 1) <<< 7) |||             -- bit 5 → bit 7
  (((n >>> 8) &&& 1) <<< 8)                 -- bit 8 stays

end QiushiMatmul
end
