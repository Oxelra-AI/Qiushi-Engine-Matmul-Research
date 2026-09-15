import QiushiSaturationShared

/-!
# Rank-additive decompositions of arbitrary invertible square matrices

The report's general saturation lemma, with no nonempty-index or positive-
dimension assumption. The inverse is Mathlib's matrix nonsingular inverse.
-/

open Matrix BigOperators

noncomputable section
namespace QiushiMatmul.GeneralSaturation

variable {k n ι : Type*} [Field k]
  [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Normalizing on the right gives a complete orthogonal family. -/
theorem normalized_products (P : Matrix n n k) (M : ι → Matrix n n k)
    (hP : IsUnit P.det) (hsum : ∑ t, M t = P)
    (hrank : ∑ t, (M t).rank = P.rank) :
    (∑ t, M t * P⁻¹ = 1) ∧
      ∀ t s, (M t * P⁻¹) * (M s * P⁻¹) =
        if t = s then M t * P⁻¹ else 0 := by
  let Q : ι → ((n → k) →ₗ[k] (n → k)) :=
    fun t => Matrix.toLin' (M t * P⁻¹)
  have hsumMat : ∑ t, M t * P⁻¹ = 1 := by
    rw [← Finset.sum_mul, hsum, Matrix.mul_nonsing_inv P hP]
  have hsumQ : ∑ t, Q t = LinearMap.id := by
    change ∑ t, Matrix.toLin' (M t * P⁻¹) = LinearMap.id
    rw [← map_sum, hsumMat, Matrix.toLin'_one]
  have hrankQ : ∑ t, Module.finrank k (LinearMap.range (Q t)) =
      Module.finrank k (n → k) := by
    change ∑ t, (M t * P⁻¹).rank = Module.finrank k (n → k)
    simp_rw [Matrix.rank_mul_eq_left_of_isUnit_det P⁻¹ (M _) (P.isUnit_nonsing_inv_det hP)]
    rw [hrank, Matrix.rank_of_isUnit P ((Matrix.isUnit_iff_isUnit_det P).mpr hP)]
    simp
  refine ⟨hsumMat, ?_⟩
  intro t s
  have h := QiushiMatmul.orthogonal_idempotents Q hsumQ hrankQ t s
  apply (Matrix.toLin' : Matrix n n k ≃ₗ[k] ((n → k) →ₗ[k] (n → k))).injective
  rw [Matrix.toLin'_mul]
  by_cases hts : t = s
  · simpa [Q, hts] using h
  · simpa [Q, hts] using h

/-- The report's exact identity for an arbitrary rank-additive matrix sum. -/
theorem rank_additive_saturation (P : Matrix n n k) (M : ι → Matrix n n k)
    (hP : IsUnit P.det) (hsum : ∑ t, M t = P)
    (hrank : ∑ t, (M t).rank = P.rank) :
    ∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0 := by
  intro t s
  have h := congrArg (fun X : Matrix n n k => X * P)
    ((normalized_products P M hP hsum hrank).2 t s)
  by_cases hts : t = s
  · simpa [hts, Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP] using h
  · simpa [hts, Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP] using h

/-- The same identity with the report's explicit dimension-valued rank sum. -/
theorem rank_additive_saturation_of_rank_sum_card
    (P : Matrix n n k) (M : ι → Matrix n n k)
    (hP : IsUnit P.det) (hsum : ∑ t, M t = P)
    (hrank : ∑ t, (M t).rank = Fintype.card n) :
    ∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0 := by
  apply rank_additive_saturation P M hP hsum
  rw [Matrix.rank_of_isUnit P ((Matrix.isUnit_iff_isUnit_det P).mpr hP)]
  exact hrank

/-- All three stated conclusions for `E t = M t * P⁻¹`. -/
theorem complete_orthogonal_idempotents
    (P : Matrix n n k) (M : ι → Matrix n n k)
    (hP : IsUnit P.det) (hsum : ∑ t, M t = P)
    (hrank : ∑ t, (M t).rank = P.rank) :
    (∀ t, (M t * P⁻¹) * (M t * P⁻¹) = M t * P⁻¹) ∧
      (∀ t s, t ≠ s → (M t * P⁻¹) * (M s * P⁻¹) = 0) ∧
      (∑ t, M t * P⁻¹ = 1) := by
  obtain ⟨hsumE, hprod⟩ := normalized_products P M hP hsum hrank
  exact ⟨fun t => by simpa using hprod t t,
    fun t s hts => by simpa [hts] using hprod t s, hsumE⟩

end QiushiMatmul.GeneralSaturation
