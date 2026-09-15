import QiushiMatmulProductFormula

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Rank-additive saturation over the shared Qiushi definitions

This module states the checked saturation endpoint using the canonical
constants from `QiushiDefs`.  It deliberately does not redefine `F`, `Pinv`,
`SIdx`, or `Mat3`; hence it can compose directly with `entrywise_to_split_sum`.
-/

open BigOperators Submodule Finset
open Matrix

namespace QiushiMatmul

section RankAdditiveSaturation

variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def sumOfRanges (Q : ι → (V →ₗ[k] V)) :
    (∀ i, ↥(LinearMap.range (Q i))) →ₗ[k] V :=
  Finset.univ.sum fun i =>
    ((LinearMap.range (Q i)).subtype).comp
      (LinearMap.proj (R := k) (φ := fun j => ↥(LinearMap.range (Q j))) i)

lemma sumOfRanges_apply (Q : ι → (V →ₗ[k] V))
    (f : ∀ i, ↥(LinearMap.range (Q i))) :
    sumOfRanges Q f = ∑ i, (f i : V) := by
  unfold sumOfRanges
  simp [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]

lemma sumOfRanges_surjective (Q : ι → (V →ₗ[k] V))
    (hsum : ∑ i, Q i = LinearMap.id) :
    Function.Surjective (sumOfRanges Q) := by
  intro v
  exact ⟨fun i => ⟨Q i v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩, by
    rw [sumOfRanges_apply]
    show ∑ i, (Q i v : V) = v
    rw [← LinearMap.sum_apply, hsum, LinearMap.id_apply]⟩

lemma sumOfRanges_injective (Q : ι → (V →ₗ[k] V))
    (hsum : ∑ i, Q i = LinearMap.id)
    (hrank : ∑ i, Module.finrank k ↥(LinearMap.range (Q i)) = Module.finrank k V) :
    Function.Injective (sumOfRanges Q) := by
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  have hrn := LinearMap.finrank_range_add_finrank_ker (sumOfRanges Q)
  have hdim : Module.finrank k (∀ i, ↥(LinearMap.range (Q i))) = Module.finrank k V := by
    rw [Module.finrank_pi_fintype]
    exact hrank
  have hrtop : LinearMap.range (sumOfRanges Q) = ⊤ :=
    LinearMap.range_eq_top.mpr (sumOfRanges_surjective Q hsum)
  rw [hrtop, finrank_top k V] at hrn
  omega

/-- Core step: `Qᵢ(v)=δᵢⱼv` for `v∈range(Qⱼ)`. -/
lemma apply_on_range_eq (Q : ι → (V →ₗ[k] V))
    (hsum : ∑ i, Q i = LinearMap.id)
    (hrank : ∑ i, Module.finrank k ↥(LinearMap.range (Q i)) = Module.finrank k V)
    (i j : ι) (v : V) (hv : v ∈ LinearMap.range (Q j)) :
    Q i v = if i = j then v else 0 := by
  have hinj := sumOfRanges_injective Q hsum hrank
  have hg_sum : sumOfRanges Q
      (fun m => ⟨Q m v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩) = v := by
    rw [sumOfRanges_apply, ← LinearMap.sum_apply, hsum, LinearMap.id_apply]
  set f : ∀ m, ↥(LinearMap.range (Q m)) :=
    fun m => if h : m = j then h ▸ ⟨v, hv⟩ else 0 with hf_eq
  have hf_val : ∀ m, (f m : V) = if m = j then v else 0 := by
    intro m
    simp only [hf_eq]
    split_ifs with h
    · subst h
      rfl
    · rfl
  have hf_sum : sumOfRanges Q f = v := by
    rw [sumOfRanges_apply]
    simp_rw [hf_val, sum_ite_eq', mem_univ, if_true]
  have hfg := hinj (hf_sum.trans hg_sum.symm)
  have hi := congrArg Subtype.val (congr_fun hfg i)
  exact hi.symm.trans (hf_val i)

/-- **Orthogonal idempotent decomposition.** `Qᵢ∘Qⱼ = δᵢⱼQⱼ`. -/
theorem orthogonal_idempotents (Q : ι → (V →ₗ[k] V))
    (hsum : ∑ i, Q i = LinearMap.id)
    (hrank : ∑ i, Module.finrank k ↥(LinearMap.range (Q i)) = Module.finrank k V) :
    ∀ i j, (Q i).comp (Q j) = if i = j then Q j else 0 := by
  intro i j
  ext x
  simp only [LinearMap.comp_apply]
  rw [apply_on_range_eq Q hsum hrank i j (Q j x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)]
  split_ifs <;> rfl

end RankAdditiveSaturation

section MatrixApplication

/-- `Pinv` is its own inverse. -/
theorem Pinv_mul_self : Pinv * Pinv = (1 : SplitMat) := by
  decide

lemma toLin_sum_split {n : ℕ} (M : Fin n → SplitMat) :
    Matrix.toLin' (∑ t, M t) = ∑ t, Matrix.toLin' (M t) := by
  apply LinearMap.ext
  intro x
  funext r
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_apply]

lemma toLin_one_split :
    Matrix.toLin' (1 : SplitMat) =
      (LinearMap.id : (SIdx → F2) →ₗ[F2] (SIdx → F2)) := by
  apply LinearMap.ext
  intro x
  funext r
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

lemma rank_mul_Pinv_range (M : SplitMat) :
    Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' (M * Pinv))) =
      Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' M)) := by
  change (M * Pinv).rank = M.rank
  apply le_antisymm
  · exact Matrix.rank_mul_le_left M Pinv
  · calc
      M.rank = ((M * Pinv) * Pinv).rank := by
        rw [Matrix.mul_assoc, Pinv_mul_self, Matrix.mul_one]
      _ ≤ (M * Pinv).rank := Matrix.rank_mul_le_left (M * Pinv) Pinv

/-- Saturation identities for an exact split decomposition with total split rank 27. -/
theorem split_flattening_saturation_identities
    {n : ℕ} (A B C : Fin n → Mat3)
    (hsum : ∑ t, F (A t) (B t) (C t) = Pinv)
    (hrank_sum : ∑ t, Module.finrank F2
        ↥(LinearMap.range (Matrix.toLin' (F (A t) (B t) (C t)))) =
      Fintype.card SIdx) :
    ∀ t s, F (A t) (B t) (C t) * Pinv * F (A s) (B s) (C s) =
      if t = s then F (A s) (B s) (C s) else 0 := by
  classical
  let M : Fin n → SplitMat := fun t => F (A t) (B t) (C t)
  let Q : Fin n → ((SIdx → F2) →ₗ[F2] (SIdx → F2)) :=
    fun t => Matrix.toLin' (M t * Pinv)
  have hsumMat : ∑ t, M t * Pinv = (1 : SplitMat) := by
    calc
      ∑ t, M t * Pinv = (∑ t, M t) * Pinv := by
        rw [Finset.sum_mul]
      _ = Pinv * Pinv := by
        rw [show (∑ t, M t) = Pinv by simpa [M] using hsum]
      _ = 1 := Pinv_mul_self
  have hsumQ : ∑ t, Q t = LinearMap.id := by
    dsimp [Q]
    rw [← toLin_sum_split (fun t => M t * Pinv), hsumMat, toLin_one_split]
  have hrankQ : ∑ t, Module.finrank F2 ↥(LinearMap.range (Q t)) =
      Module.finrank F2 (SIdx → F2) := by
    dsimp [Q]
    trans ∑ t, Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' (M t)))
    · apply Finset.sum_congr rfl
      intro t _
      exact rank_mul_Pinv_range (M t)
    · rw [show (∑ t, Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' (M t)))) =
          Fintype.card SIdx by simpa [M] using hrank_sum]
      simp
  intro t s
  have hlin := orthogonal_idempotents Q hsumQ hrankQ t s
  have hlin2 :
      Matrix.toLin' ((M t * Pinv) * (M s * Pinv)) =
        Matrix.toLin' (if t = s then M s * Pinv else 0) := by
    rw [Matrix.toLin'_mul]
    by_cases h : t = s
    · simp [Q, h] at hlin ⊢
      exact hlin
    · simp [Q, h] at hlin ⊢
      exact hlin
  have hmat : (M t * Pinv) * (M s * Pinv) = if t = s then M s * Pinv else 0 :=
    (Matrix.toLin' : SplitMat ≃ₗ[F2] ((SIdx → F2) →ₗ[F2] (SIdx → F2))).injective hlin2
  have hright := congrArg (fun X : SplitMat => X * Pinv) hmat
  simpa [M, Matrix.mul_assoc, Pinv_mul_self] using hright

section GenericFactorRank

variable {k : Type*} [Field k]
variable {V W X Y : Type*}
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]

noncomputable section

lemma range_comp_le_range_right (f : V →ₗ[k] W) (g : Y →ₗ[k] V) :
    LinearMap.range (f.comp g) ≤ LinearMap.range f := by
  rintro y ⟨x, rfl⟩
  exact ⟨g x, rfl⟩

lemma range_comp_le_map_left (u : W →ₗ[k] X) (f : V →ₗ[k] W) :
    LinearMap.range (u.comp f) ≤ Submodule.map u (LinearMap.range f) := by
  rintro z ⟨x, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, rfl⟩

lemma finrank_range_comp_left_le (u : W →ₗ[k] X) (f : V →ₗ[k] W) :
    Module.finrank k ↥(LinearMap.range (u.comp f)) ≤
      Module.finrank k ↥(LinearMap.range f) := by
  have hle := range_comp_le_map_left u f
  exact le_trans (Submodule.finrank_mono hle)
    (Submodule.finrank_map_le u (LinearMap.range f))

lemma finrank_range_comp_right_le (f : V →ₗ[k] W) (g : Y →ₗ[k] V) :
    Module.finrank k ↥(LinearMap.range (f.comp g)) ≤
      Module.finrank k ↥(LinearMap.range f) := by
  exact Submodule.finrank_mono (range_comp_le_range_right f g)

/-- If `U` has a left inverse and `Vmap` has a right inverse, then
`U ∘ A ∘ Vmap` has the same finite-dimensional rank as `A`. -/
lemma finrank_range_factor_eq
    (A : V →ₗ[k] W) (U : W →ₗ[k] X) (L : X →ₗ[k] W)
    (Vmap : Y →ₗ[k] V) (R : V →ₗ[k] Y)
    (hLU : L.comp U = LinearMap.id)
    (hVR : Vmap.comp R = LinearMap.id) :
    Module.finrank k ↥(LinearMap.range (U.comp (A.comp Vmap))) =
      Module.finrank k ↥(LinearMap.range A) := by
  let M : Y →ₗ[k] X := U.comp (A.comp Vmap)
  have hMdef : M = U.comp (A.comp Vmap) := rfl
  apply le_antisymm
  · rw [← hMdef]
    exact le_trans (finrank_range_comp_left_le U (A.comp Vmap))
      (finrank_range_comp_right_le A Vmap)
  · have hAeq : A = L.comp (M.comp R) := by
      ext x
      dsimp [M]
      have hvrx : Vmap (R x) = x := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hVR x
      have hlu : L (U (A (Vmap (R x)))) = A (Vmap (R x)) := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hLU (A (Vmap (R x)))
      calc
        A x = A (Vmap (R x)) := by rw [hvrx]
        _ = L (U (A (Vmap (R x)))) := hlu.symm
    have hrange : LinearMap.range A = LinearMap.range (L.comp (M.comp R)) := by
      rw [hAeq]
    rw [hrange]
    exact le_trans (finrank_range_comp_right_le (L.comp M) R)
      (finrank_range_comp_left_le L M)

end
end GenericFactorRank

/-- The injection `U_B`: a 3-vector is copied into each `(row,column)` slot with
coefficient from `B`. -/
noncomputable def Umap (B : Mat3) : (I3 → F2) →ₗ[F2] (SIdx → F2) where
  toFun x := fun r => x r.1 * B r.2.1 r.2.2
  map_add' x y := by
    ext r
    simp [add_mul]
  map_smul' a x := by
    ext r
    simp [mul_assoc]

/-- The contraction `V_C`: contract the last two coordinates against `C`. -/
noncomputable def Vmap (C : Mat3) : (SIdx → F2) →ₗ[F2] (I3 → F2) where
  toFun x := fun j => ∑ p : Pair9, C p.1 p.2 * x (j, p)
  map_add' x y := by
    ext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext j
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- A left inverse to `U_B` from a chosen nonzero entry of `B`. -/
noncomputable def Lmap (B : Mat3) (p : Pair9) : (SIdx → F2) →ₗ[F2] (I3 → F2) where
  toFun x := fun i => (B p.1 p.2)⁻¹ * x (i, p)
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' a x := by
    ext i
    simp [mul_assoc, mul_left_comm, mul_comm]

/-- A right inverse to `V_C` from a chosen nonzero entry of `C`. -/
noncomputable def Rmap (C : Mat3) (p : Pair9) : (I3 → F2) →ₗ[F2] (SIdx → F2) where
  toFun x := fun r => if r.2 = p then (C p.1 p.2)⁻¹ * x r.1 else 0
  map_add' x y := by
    ext r
    by_cases h : r.2 = p <;> simp [h, mul_add]
  map_smul' a x := by
    ext r
    by_cases h : r.2 = p <;> simp [h, mul_assoc, mul_left_comm, mul_comm]

lemma Lmap_comp_Umap (B : Mat3) (p : Pair9) (hp : B p.1 p.2 ≠ 0) :
    (Lmap B p).comp (Umap B) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  simp [Lmap, Umap, hp, mul_assoc, mul_left_comm, mul_comm]

lemma Vmap_comp_Rmap (C : Mat3) (p : Pair9) (hp : C p.1 p.2 ≠ 0) :
    (Vmap C).comp (Rmap C p) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext j
  simp [Vmap, Rmap, hp, mul_assoc]

/-- Linear-map factorization of the split-flattened elementary term. -/
theorem toLin_F_factor (A B C : Mat3) :
    Matrix.toLin' (F A B C) = (Umap B).comp ((Matrix.toLin' A).comp (Vmap C)) := by
  apply LinearMap.ext
  intro x
  funext r
  calc
    (Matrix.toLin' (F A B C)) x r
        = ∑ c : SIdx, A r.1 c.1 * B r.2.1 r.2.2 * C c.2.1 c.2.2 * x c := by
            simp [F, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    _ = B r.2.1 r.2.2 * ∑ j : I3, A r.1 j * (∑ p : Pair9, C p.1 p.2 * x (j, p)) := by
            rw [Fintype.sum_prod_type]
            simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ((Umap B).comp ((Matrix.toLin' A).comp (Vmap C))) x r := by
            simp [Umap, Vmap, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
              Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Extract a nonzero entry from a nonzero `3×3` matrix. -/
private lemma Mat3_ne_zero_witness (M : Mat3) (hM : M ≠ 0) :
    ∃ p : Pair9, M p.1 p.2 ≠ 0 := by
  by_contra hall
  simp only [not_exists, ne_eq, not_not] at hall
  exact hM (Matrix.ext (fun i j => hall (i, j)))

/-- Nonzero `B` and `C` do not change the rank of a split elementary term. -/
theorem F_rank_eq_A_rank (A B C : Mat3) (hB : B ≠ 0) (hC : C ≠ 0) :
    (F A B C).rank = A.rank := by
  obtain ⟨pB, hpB⟩ := Mat3_ne_zero_witness B hB
  obtain ⟨pC, hpC⟩ := Mat3_ne_zero_witness C hC
  change Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' (F A B C))) =
    Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' A))
  rw [toLin_F_factor]
  exact finrank_range_factor_eq (Matrix.toLin' A) (Umap B) (Lmap B pB)
    (Vmap C) (Rmap C pC) (Lmap_comp_Umap B pB hpB) (Vmap_comp_Rmap C pC hpC)

/-- The saturation identities follow from a split sum and equality of A-ranks,
provided all second and third factors are nonzero. -/
theorem split_flattening_saturation_identities_from_A_rank
    {n : ℕ} (A B C : Fin n → Mat3)
    (hsum : ∑ t, F (A t) (B t) (C t) = Pinv)
    (hrankA_sum : ∑ t, (A t).rank = Fintype.card SIdx)
    (hB : ∀ t, B t ≠ 0) (hC : ∀ t, C t ≠ 0) :
    ∀ t s, F (A t) (B t) (C t) * Pinv * F (A s) (B s) (C s) =
      if t = s then F (A s) (B s) (C s) else 0 := by
  apply split_flattening_saturation_identities A B C hsum
  change ∑ t, (F (A t) (B t) (C t)).rank = Fintype.card SIdx
  calc
    ∑ t, (F (A t) (B t) (C t)).rank = ∑ t, (A t).rank := by
      apply Finset.sum_congr rfl
      intro t _
      exact F_rank_eq_A_rank (A t) (B t) (C t) (hB t) (hC t)
    _ = Fintype.card SIdx := hrankA_sum

/-- If `F(A,B,C)=0` and `B,C` are nonzero, then `A=0`. -/
theorem F_eq_zero_imp_A_zero
    (A B C : Mat3) (hB : B ≠ 0) (hC : C ≠ 0)
    (hF : F A B C = 0) : A = 0 := by
  obtain ⟨pB, hpB⟩ := Mat3_ne_zero_witness B hB
  obtain ⟨pC, hpC⟩ := Mat3_ne_zero_witness C hC
  ext i j
  have hentry : A i j * B pB.1 pB.2 * C pC.1 pC.2 = 0 := by
    have h := congr_fun (congr_fun hF (i, pB)) (j, pC)
    simpa [F] using h
  rcases mul_eq_zero.mp hentry with hab | hc
  · exact (mul_eq_zero.mp hab).elim id (absurd · hpB)
  · exact absurd hc hpC

/-- Off-diagonal saturation yields the concrete matrix zero equation. -/
theorem off_diagonal_equation
    (At Bt Ct As Bs Cs : Mat3)
    (hBt : Bt ≠ 0) (hCs : Cs ≠ 0)
    (hsat : F At Bt Ct * Pinv * F As Bs Cs = 0) :
    At * Bs * Ct.transpose * As = 0 := by
  rw [product_formula] at hsat
  exact F_eq_zero_imp_A_zero _ Bt Cs hBt hCs hsat

/-- Diagonal saturation yields the concrete matrix identity. -/
theorem diagonal_equation
    (A B C : Mat3) (hB : B ≠ 0) (hC : C ≠ 0)
    (hsat : F A B C * Pinv * F A B C = F A B C) :
    A * B * C.transpose * A = A := by
  rw [product_formula] at hsat
  obtain ⟨pB, hpB⟩ := Mat3_ne_zero_witness B hB
  obtain ⟨pC, hpC⟩ := Mat3_ne_zero_witness C hC
  ext i j
  have hentry := congr_fun (congr_fun hsat (i, pB)) (j, pC)
  simp only [F] at hentry
  exact mul_right_cancel₀ hpB (mul_right_cancel₀ hpC hentry)

lemma det_product_four (A B C D : Mat3) :
    (A * B * C.transpose * D).det = A.det * B.det * C.det * D.det := by
  simp [Matrix.det_mul, Matrix.det_transpose, mul_assoc]

lemma det_nonzero_product_four
    (A B C D : Mat3)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hC : C.det ≠ 0) (hD : D.det ≠ 0) :
    A * B * C.transpose * D ≠ 0 := by
  intro hzero
  have hdet_zero : (A * B * C.transpose * D).det = 0 := by
    rw [hzero]
    exact Matrix.det_zero
  have hprod_zero : A.det * B.det * C.det * D.det = 0 := by
    rw [← det_product_four A B C D]
    exact hdet_zero
  have hprod_ne : A.det * B.det * C.det * D.det ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hA hB) hC) hD
  exact hprod_ne hprod_zero

lemma right_middle_det_nonzero_of_diagonal_identity
    (A B C : Mat3) (hA : A.det ≠ 0)
    (hdiag : A * B * C.transpose * A = A) : B.det ≠ 0 := by
  have hdet_eq : A.det * B.det * C.det * A.det = A.det := by
    rw [← det_product_four A B C A]
    rw [hdiag]
  have hleft_ne : A.det * B.det * C.det * A.det ≠ 0 := by
    intro hzero
    exact hA (by simpa [hzero] using hdet_eq.symm)
  intro hBzero
  apply hleft_ne
  simp [hBzero]

lemma left_middle_det_nonzero_of_diagonal_identity
    (A B C : Mat3) (hA : A.det ≠ 0)
    (hdiag : A * B * C.transpose * A = A) : C.det ≠ 0 := by
  have hdet_eq : A.det * B.det * C.det * A.det = A.det := by
    rw [← det_product_four A B C A]
    rw [hdiag]
  have hleft_ne : A.det * B.det * C.det * A.det ≠ 0 := by
    intro hzero
    exact hA (by simpa [hzero] using hdet_eq.symm)
  intro hCzero
  apply hleft_ne
  simp [hCzero]

/-- Endpoint contradiction once the concrete diagonal and off-diagonal equations are known. -/
theorem two_invertible_A_factors_contradict_saturation_endpoint
    (A1 A2 B1 B2 C1 C2 : Mat3)
    (hA1 : A1.det ≠ 0) (hA2 : A2.det ≠ 0)
    (hdiag1 : A1 * B1 * C1.transpose * A1 = A1)
    (hdiag2 : A2 * B2 * C2.transpose * A2 = A2)
    (hoff : A1 * B2 * C1.transpose * A2 = 0) : False := by
  have hB2 : B2.det ≠ 0 :=
    right_middle_det_nonzero_of_diagonal_identity A2 B2 C2 hA2 hdiag2
  have hC1 : C1.det ≠ 0 :=
    left_middle_det_nonzero_of_diagonal_identity A1 B1 C1 hA1 hdiag1
  exact det_nonzero_product_four A1 B2 C1 A2 hA1 hB2 hC1 hA2 hoff

/-- Contradiction from a genuine split decomposition, saturated A-rank, nonzero
`B,C`, and two distinct invertible A-factors. -/
theorem two_invertible_terms_contradict_from_A_rank_decomposition
    {n : ℕ} (A B C : Fin n → Mat3)
    (hsum : ∑ t, F (A t) (B t) (C t) = Pinv)
    (hrankA_sum : ∑ t, (A t).rank = Fintype.card SIdx)
    (hB : ∀ t, B t ≠ 0) (hC : ∀ t, C t ≠ 0)
    (t s : Fin n) (hts : t ≠ s)
    (hAt : (A t).det ≠ 0) (hAs : (A s).det ≠ 0) : False := by
  have hsat := split_flattening_saturation_identities_from_A_rank A B C hsum hrankA_sum hB hC
  have hdiag_t : A t * B t * (C t).transpose * A t = A t :=
    diagonal_equation (A t) (B t) (C t) (hB t) (hC t) (by simpa using hsat t t)
  have hdiag_s : A s * B s * (C s).transpose * A s = A s :=
    diagonal_equation (A s) (B s) (C s) (hB s) (hC s) (by simpa using hsat s s)
  have hoff_ts : A t * B s * (C t).transpose * A s = 0 :=
    off_diagonal_equation (A t) (B t) (C t) (A s) (B s) (C s) (hB t) (hC s)
      (by simpa [hts] using hsat t s)
  exact two_invertible_A_factors_contradict_saturation_endpoint
    (A t) (A s) (B t) (B s) (C t) (C s) hAt hAs hdiag_t hdiag_s hoff_ts

end MatrixApplication

end QiushiMatmul
