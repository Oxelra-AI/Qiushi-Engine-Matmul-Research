import QiushiGeneralSaturation

open Matrix BigOperators QiushiMatmul.GeneralSaturation

noncomputable section

set_option format.width 110

#check @normalized_products
#print axioms normalized_products
#check @rank_additive_saturation
#print axioms rank_additive_saturation
#check @rank_additive_saturation_of_rank_sum_card
#print axioms rank_additive_saturation_of_rank_sum_card
#check @complete_orthogonal_idempotents
#print axioms complete_orthogonal_idempotents

namespace GeneralSaturationTests

variable {k n ι : Type*} [Field k]
  [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- Exact-type regression with independent universes and no nonempty instances. -/
example (P : Matrix n n k) (M : ι → Matrix n n k)
    (hP : IsUnit P.det) (hsum : ∑ t, M t = P)
    (hrank : ∑ t, (M t).rank = P.rank) :
    ∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0 :=
  rank_additive_saturation P M hP hsum hrank

example (d r : Nat) (P : Matrix (Fin d) (Fin d) k)
    (M : Fin r → Matrix (Fin d) (Fin d) k) [Invertible P]
    (hsum : ∑ t, M t = P) (hrank : ∑ t, (M t).rank = d) :
    ∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0 := by
  exact rank_additive_saturation_of_rank_sum_card P M
    (Matrix.isUnit_det_of_invertible P) hsum (by simpa using hrank)

/-- In dimension zero, arbitrary matrices and arbitrary finite families qualify. -/
theorem empty_dimension [IsEmpty n] (P : Matrix n n k) (M : ι → Matrix n n k) :
    (∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0) ∧
      (∀ t, (M t * P⁻¹) * (M t * P⁻¹) = M t * P⁻¹) ∧
      (∀ t s, t ≠ s → (M t * P⁻¹) * (M s * P⁻¹) = 0) ∧
      (∑ t, M t * P⁻¹ = 1) := by
  have hP : IsUnit P.det := by simp
  have hsum : ∑ t, M t = P := Subsingleton.elim _ _
  have hrank : ∑ t, (M t).rank = P.rank := by
    have hz : ∀ A : Matrix n n k, A = 0 := fun A => Subsingleton.elim _ _
    simp [hz]
  exact ⟨rank_additive_saturation P M hP hsum hrank,
    complete_orthogonal_idempotents P M hP hsum hrank⟩

omit [DecidableEq ι] in
/-- An empty sum cannot be invertible in positive dimension. -/
theorem empty_index_forces_empty_dimension [IsEmpty ι]
    (P : Matrix n n k) (M : ι → Matrix n n k)
    (hP : IsUnit P.det) (hsum : ∑ t, M t = P) : IsEmpty n := by
  have hz : P = 0 := by simpa using hsum.symm
  have hc := Matrix.rank_of_isUnit P ((Matrix.isUnit_iff_isUnit_det P).mpr hP)
  rw [hz, Matrix.rank_zero] at hc
  exact Fintype.card_eq_zero_iff.mp hc.symm

/-- Both empty indices instantiate the same report theorems, including sum E = I. -/
example (P : Matrix (Fin 0) (Fin 0) k)
    (M : Fin 0 → Matrix (Fin 0) (Fin 0) k) :
    (∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0) ∧
      (∑ t, M t * P⁻¹ = 1) := by
  have h := empty_dimension P M
  exact ⟨h.1, h.2.2.2⟩

/-- A zero summand is allowed, in every dimension and over every field. -/
theorem zero_padded (P : Matrix n n k) (hP : IsUnit P.det) :
    let M : Fin 2 → Matrix n n k := fun t => if t = 0 then P else 0
    ∀ t s, M t * P⁻¹ * M s = if t = s then M t else 0 := by
  dsimp
  apply rank_additive_saturation P _ hP
  · simp
  · simp [Fin.sum_univ_two]

/-- Characteristic zero, dimension one, and P not equal to its inverse. -/
theorem rational_noninvolutory :
    let P : Matrix (Fin 1) (Fin 1) ℚ := !![2]
    P * P ≠ 1 ∧ P * P⁻¹ * P = P := by
  dsimp
  let P : Matrix (Fin 1) (Fin 1) ℚ := !![2]
  have hP : IsUnit P.det := by norm_num [P]
  have h := rank_additive_saturation P (fun _ : Fin 1 => P) hP
    (by simp) (by simp) 0 0
  refine ⟨?_, h.trans (if_pos rfl)⟩
  intro heq
  have he := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℚ => A 0 0) heq
  norm_num [Matrix.mul_apply] at he

#check @empty_dimension
#print axioms empty_dimension
#check @empty_index_forces_empty_dimension
#print axioms empty_index_forces_empty_dimension
#check @zero_padded
#print axioms zero_padded
#check @rational_noninvolutory
#print axioms rational_noninvolutory

end GeneralSaturationTests

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations : Array Lean.Name := #[
    ``normalized_products, ``rank_additive_saturation,
    ``rank_additive_saturation_of_rank_sum_card, ``complete_orthogonal_idempotents,
    ``GeneralSaturationTests.empty_dimension,
    ``GeneralSaturationTests.empty_index_forces_empty_dimension,
    ``GeneralSaturationTests.zero_padded, ``GeneralSaturationTests.rational_noninvolutory]
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  Lean.logInfo m!"Axiom whitelist passed for {declarations.size} declarations."
