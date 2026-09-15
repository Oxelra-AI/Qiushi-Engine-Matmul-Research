import QiushiBridge

/-!
# Split-flattening lower bound on the total A-rank

This module proves the `split_rank_bound_from_entrywise` theorem required by
`QiushiRank21Root` over the canonical definitions from `QiushiDefs`.
-/

set_option maxHeartbeats 4000000

open Matrix BigOperators Submodule

namespace QiushiMatmul

private theorem Pinv_mul_self_for_rank : Pinv * Pinv = (1 : SplitMat) := by
  decide

private theorem Pinv_rank_full : Pinv.rank = Fintype.card SIdx := by
  suffices h : LinearMap.range Pinv.mulVecLin = ⊤ by
    unfold Matrix.rank
    rw [h, finrank_top F2 (SIdx → F2)]
    simp [Module.finrank_pi_fintype, Module.finrank_self, Finset.card_univ]
  apply LinearMap.range_eq_top.mpr
  intro v
  refine ⟨Pinv *ᵥ v, ?_⟩
  show Pinv *ᵥ (Pinv *ᵥ v) = v
  rw [mulVec_mulVec, Pinv_mul_self_for_rank, one_mulVec]

private theorem split_rank_add_le (A B : SplitMat) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hadd : (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by
    ext v r
    simp [Matrix.mulVecLin_apply, mulVec, dotProduct, add_mul,
      Finset.sum_add_distrib]
  rw [hadd]
  calc
    Module.finrank F2 ↥(LinearMap.range (A.mulVecLin + B.mulVecLin))
        ≤ Module.finrank F2
            ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
      Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ + _ := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
      omega

private theorem rank_finsum_le {n : ℕ} (M : Fin n → SplitMat) :
    (∑ t, M t).rank ≤ ∑ t, (M t).rank := by
  induction n with
  | zero => simp [Finset.univ_eq_empty]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc (f := M),
      Fin.sum_univ_castSucc (f := fun t => (M t).rank)]
    exact le_trans (split_rank_add_le _ _)
      (Nat.add_le_add_right (ih (fun t => M (Fin.castSucc t))) _)

private noncomputable def splitUmap (B : Mat3) :
    (I3 → F2) →ₗ[F2] (SIdx → F2) where
  toFun x := fun r => x r.1 * B r.2.1 r.2.2
  map_add' x y := by ext r; simp [add_mul]
  map_smul' a x := by ext r; simp [mul_assoc]

private noncomputable def splitVmap (C : Mat3) :
    (SIdx → F2) →ₗ[F2] (I3 → F2) where
  toFun x := fun j => ∑ p : Coord9, C p.1 p.2 * x (j, p)
  map_add' x y := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext j
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private lemma range_comp_le_range_right
    {k V W Y : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (f : V →ₗ[k] W) (g : Y →ₗ[k] V) :
    LinearMap.range (f.comp g) ≤ LinearMap.range f := by
  rintro y ⟨x, rfl⟩
  exact ⟨g x, rfl⟩

private lemma range_comp_le_map_left
    {k V W X : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (u : W →ₗ[k] X) (f : V →ₗ[k] W) :
    LinearMap.range (u.comp f) ≤ Submodule.map u (LinearMap.range f) := by
  rintro z ⟨x, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, rfl⟩

private lemma finrank_range_comp_left_le
    {k V W X : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (u : W →ₗ[k] X) (f : V →ₗ[k] W) :
    Module.finrank k ↥(LinearMap.range (u.comp f)) ≤
      Module.finrank k ↥(LinearMap.range f) := by
  exact le_trans (Submodule.finrank_mono (range_comp_le_map_left u f))
    (Submodule.finrank_map_le u (LinearMap.range f))

private lemma finrank_range_comp_right_le
    {k V W Y : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (f : V →ₗ[k] W) (g : Y →ₗ[k] V) :
    Module.finrank k ↥(LinearMap.range (f.comp g)) ≤
      Module.finrank k ↥(LinearMap.range f) :=
  Submodule.finrank_mono (range_comp_le_range_right f g)

private theorem F_rank_le_A_rank_local (A B C : Mat3) :
    (F A B C).rank ≤ A.rank := by
  have hfactor : Matrix.toLin' (F A B C) =
      (splitUmap B).comp ((Matrix.toLin' A).comp (splitVmap C)) := by
    apply LinearMap.ext
    intro x
    funext r
    simp [F, splitUmap, splitVmap, Matrix.toLin'_apply, mulVec, dotProduct,
      Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm]
  change Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' (F A B C))) ≤
    Module.finrank F2 ↥(LinearMap.range (Matrix.toLin' A))
  rw [hfactor]
  exact le_trans
    (finrank_range_comp_left_le (splitUmap B)
      ((Matrix.toLin' A).comp (splitVmap C)))
    (finrank_range_comp_right_le (Matrix.toLin' A) (splitVmap C))

/-- The split flattening forces total A-rank at least 27. -/
theorem split_rank_bound_from_entrywise {r : ℕ} (D : TensorEntryDecomp r) :
    27 ≤ ∑ t : Fin r, (D.A t).rank := by
  have hcard : Fintype.card SIdx = 27 := by decide
  calc
    27 = Fintype.card SIdx := hcard.symm
    _ = Pinv.rank := Pinv_rank_full.symm
    _ = (∑ t : Fin r, F (D.A t) (D.B t) (D.C t)).rank := by
      rw [entrywise_to_split_sum D]
    _ ≤ ∑ t : Fin r, (F (D.A t) (D.B t) (D.C t)).rank :=
      rank_finsum_le _
    _ ≤ ∑ t : Fin r, (D.A t).rank :=
      Finset.sum_le_sum (fun t _ => F_rank_le_A_rank_local (D.A t) (D.B t) (D.C t))

end QiushiMatmul
