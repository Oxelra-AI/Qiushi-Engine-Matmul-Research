import QiushiBSlotDeletion
import QiushiSliceSpaceFoldUniform

/-!
# Combined forced-product lower bound via deletion + fold-uniform transfer

Two independent halves:
1. **Deletion iteration**: `k` deletions reduce decomposition length `r` to `r−k`.
2. **Fold-uniform transfer**: witnesses that annihilate the selected directions
   are invisible to the product-residual perturbation.

Combined: `k + f ≤ r`.
-/

open BigOperators Finset

set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable

namespace QiushiMatmul

variable {β γ V : Type*}
variable [Fintype β] [Fintype γ]
variable [AddCommGroup V] [Module F2 V]

/-! ## The fold-uniform witness condition -/

/-- For every nonzero `y ∈ F₂^f`, there exist a point `b` and a functional `phi`
on `V` that annihilates all selected evaluation sums while detecting at `b`. -/
def FoldUniformWitness (S : β → γ → V) {k f : ℕ}
    (sels : Fin k → β) (cols : Fin f → γ) : Prop :=
  ∀ y : Fin f → F2, y ≠ 0 →
    ∃ (b : β) (phi : V →ₗ[F2] F2),
      (∀ l : Fin k, phi (∑ j, y j • S (sels l) (cols j)) = 0) ∧
      phi (∑ j, y j • S b (cols j)) ≠ 0

/-! ## Transfer lemma -/

/-- Algebraic identity: if `phi` annihilates the direction `b₀`, the product-
residual perturbation `g(b) • S(b₀, c)` is invisible. -/
theorem residual_eval_invisible
    {S : β → γ → V} {f : ℕ}
    (b b₀ : β) (cols : Fin f → γ) (g : β → F2)
    (phi : V →ₗ[F2] F2) (y : Fin f → F2)
    (hann : phi (∑ j : Fin f, y j • S b₀ (cols j)) = 0) :
    phi (∑ j : Fin f, y j • (S b (cols j) + g b • S b₀ (cols j)))
      = phi (∑ j : Fin f, y j • S b (cols j)) := by
  have step1 : ∀ j : Fin f,
      y j • (S b (cols j) + g b • S b₀ (cols j)) =
      y j • S b (cols j) + (y j * g b) • S b₀ (cols j) := by
    intro j; rw [smul_add, smul_smul]
  simp_rw [step1]
  rw [Finset.sum_add_distrib, map_add]
  have step3 : (∑ j : Fin f, (y j * g b) • S b₀ (cols j)) =
      g b • (∑ j : Fin f, y j • S b₀ (cols j)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _; rw [smul_smul, mul_comm]
  rw [step3, map_smul, hann, smul_zero, add_zero]

/-- **Transfer lemma.** The fold-uniform witness condition passes through a
depth-1 product residual unchanged. -/
theorem fold_uniform_witness_transfer
    {S : β → γ → V} {k f : ℕ}
    (sels : Fin (k + 1) → β) (cols : Fin f → γ)
    (g : β → F2)
    (hFK : FoldUniformWitness S sels cols)
    (S' : β → γ → V)
    (hRes : ∀ b c, S' b c = S b c + g b • S (sels 0) c) :
    FoldUniformWitness S' (fun l => sels (Fin.succ l)) cols := by
  intro y hy
  obtain ⟨b_y, phi_y, hann, hdet⟩ := hFK y hy
  refine ⟨b_y, phi_y, fun l => ?_, ?_⟩
  · have hconv : (∑ j, y j • S' (sels (Fin.succ l)) (cols j)) =
        (∑ j, y j • (S (sels (Fin.succ l)) (cols j) +
          g (sels (Fin.succ l)) • S (sels 0) (cols j))) := by
      apply Finset.sum_congr rfl; intro j _; congr 1; exact hRes _ _
    rw [hconv, residual_eval_invisible _ _ cols g phi_y y (hann 0)]
    exact hann (Fin.succ l)
  · have hconv : (∑ j, y j • S' b_y (cols j)) =
        (∑ j, y j • (S b_y (cols j) + g b_y • S (sels 0) (cols j))) := by
      apply Finset.sum_congr rfl; intro j _; congr 1; exact hRes _ _
    rw [hconv, residual_eval_invisible _ _ cols g phi_y y (hann 0)]
    exact hdet

/-! ## Base case: fold-uniform witnesses → pigeonhole bound -/

/-- When `k = 0`, the witnesses directly contradict a too-short decomposition.
The proof: any nonzero kernel vector of the C-coefficient matrix annihilates
`∑ y_j S(b, c_j)` for every `b` (by the decomposition identity), contradicting
the witness that detects at some `b`. -/
theorem fold_uniform_base_bound
    {S : β → γ → V} {r f : ℕ}
    (D : BSliceFamilyDecomp S r)
    (cols : Fin f → γ)
    (hFK : ∀ y : Fin f → F2, y ≠ 0 →
      ∃ (b : β) (phi : V →ₗ[F2] F2),
        phi (∑ j, y j • S b (cols j)) ≠ 0) :
    f ≤ r := by
  by_contra hfr
  push_neg at hfr
  let RR : Matrix (Fin r) (Fin f) F2 := fun t j => D.C t (cols j)
  obtain ⟨y, hyne, hRy⟩ := exists_ne_zero_mulVec_eq_zero RR (by omega : r < f)
  have hRy_t : ∀ t : Fin r, ∑ j, D.C t (cols j) * y j = 0 := by
    intro t; have := congr_fun hRy t
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct] at this; exact this
  obtain ⟨b, phi, hdet⟩ := hFK y hyne
  apply hdet; clear hdet
  -- Show phi(∑ y_j S(b, c_j)) = 0 by factoring through the decomposition
  calc phi (∑ j : Fin f, y j • S b (cols j))
      = ∑ j : Fin f, y j * phi (S b (cols j)) := by
        rw [map_sum]; simp_rw [map_smul, smul_eq_mul]
    _ = ∑ j, y j * (∑ t : Fin r, D.B t b * D.C t (cols j) * phi (D.A t)) := by
        apply Finset.sum_congr rfl; intro j _
        congr 1
        rw [D.identity b (cols j), map_sum]
        apply Finset.sum_congr rfl; intro t _
        rw [map_smul, smul_eq_mul]
    _ = ∑ t : Fin r, (∑ j, y j * D.C t (cols j)) * (D.B t b * phi (D.A t)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro t _
        have hrw : ∀ j, y j * (D.B t b * D.C t (cols j) * phi (D.A t)) =
            (y j * D.C t (cols j)) * (D.B t b * phi (D.A t)) := by intro j; ring
        simp_rw [hrw, ← Finset.sum_mul]
    _ = 0 := by
        apply Finset.sum_eq_zero; intro t _
        have : ∑ j, y j * D.C t (cols j) = ∑ j, D.C t (cols j) * y j := by
          apply Finset.sum_congr rfl; intro j _; ring
        rw [this, hRy_t t, zero_mul]

end QiushiMatmul
