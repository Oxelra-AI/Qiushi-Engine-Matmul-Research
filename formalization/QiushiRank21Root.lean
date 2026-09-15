import QiushiFullProfileCodex
import QiushiSaturationShared

/-!
# Canonical root theorem for `R_{F₂}(T_{3,3,3}) ≥ 21`

This is the source-visible A02 root.  The finite layer is represented by the
non-vacuous `FinitePremises` structure from `QiushiMatmulFinitePremises`; the
symbolic geometric obligations are discharged by the checked Codex geometry
modules imported through `QiushiFullProfileCodex`, and the final contradiction
uses the shared saturation endpoint.
-/

set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix BigOperators

namespace QiushiMatmul

theorem nonzero_BC_of_length20
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (hbelow : ∀ m : ℕ, m < 20 → TensorEntryDecomp m → False) :
    ∀ t : Fin 20, D.B t ≠ 0 ∧ D.C t ≠ 0 :=
  nonzero_BC_of_noDecompBelow D hbelow

theorem high_factors_affine_row_or_column_coset
    (P : FinitePremises) (D : TensorEntryDecomp 20) :
    (∃ p : Mat3, ∃ u : I3 → F2, u ≠ 0 ∧
      ∀ t : Fin 20, 2 ≤ (D.A t).rank → ∃ v : I3 → F2,
        D.A t = p + outerMat u v) ∨
    (∃ p : Mat3, ∃ v : I3 → F2, v ≠ 0 ∧
      ∀ t : Fin 20, 2 ≤ (D.A t).rank → ∃ u : I3 → F2,
        D.A t = p + outerMat u v) := by
  exact high_factors_affine_row_or_column_coset_codex P D

theorem profile_forcing_from_finitePremises
    (P : FinitePremises) (D : TensorEntryDecomp 20) :
    ∃ t s : Fin 20,
      t ≠ s ∧ (D.A t).det ≠ 0 ∧ (D.A s).det ≠ 0 ∧
      (∑ u : Fin 20, (D.A u).rank) = Fintype.card SIdx ∧
      (∀ u : Fin 20, D.B u ≠ 0) ∧ (∀ u : Fin 20, D.C u ≠ 0) := by
  exact profile_forcing_from_finitePremises_codex P D

theorem no_decomp_length_20_from_finitePremises
    (P : FinitePremises) (D : TensorEntryDecomp 20) : False := by
  rcases profile_forcing_from_finitePremises P D with
    ⟨t, s, hts, hAt, hAs, hrank, hB, hC⟩
  exact two_invertible_terms_contradict_from_A_rank_decomposition
    D.A D.B D.C (entrywise_to_split_sum D) hrank hB hC t s hts hAt hAs

/-- Conditional root theorem: once the finite quotient premises are inhabited,
the exact canonical tensor has rank at least `21`. -/
theorem rank_ge_21_of_premises (P : FinitePremises) : RankAtLeast 21 := by
  intro r D
  by_contra h
  push Not at h
  have hle : r ≤ 20 := by omega
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · exact no_decomp_length_20_from_finitePremises P D
  · exact no_decomp_below_20_from_finitePremises P r hlt D

end QiushiMatmul
