import QiushiLineOrbit
import QiushiConversion
import QiushiOccupation

/-!
# Excluding exact decompositions of length below 20

The proof first extracts a nonzero A-factor from a concrete nonzero A-slice.
It then quotients the entrywise decomposition by the zero subspace and applies
the occupation inequality to the line spanned by that factor.  The line lower
bound forces at least 19 terms, while the killed chosen term forces strictly
more than 19 terms.
-/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

theorem no_decomp_below_20_from_finitePremises
    (P : FinitePremises) (r : ℕ) (hr : r < 20)
    (D : TensorEntryDecomp r) : False := by
  let b : Coord9 := (0, 0)
  let c : Coord9 := (0, 0)
  have hslice : tensorASlice b c ≠ 0 := by
    change tensorASlice ((0, 0) : Coord9) ((0, 0) : Coord9) ≠ 0
    decide
  have hA : ∃ t : Fin r, D.A t ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero :
        (∑ t : Fin r,
          (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [h t, smul_zero]
    have hsliceZero : tensorASlice b c = 0 := by
      rw [← smul_sum_eq_slice D b c]
      exact hzero
    exact hslice hsliceZero
  rcases hA with ⟨t, ht⟩
  let W : Submodule F2 Mat3 := Submodule.span F2 ({D.A t} : Set Mat3)
  have hW : QuotientRankAtLeast W 19 := nonzero_line_lb19 P (D.A t) ht
  have hr19 : 19 ≤ r := rank_lower_bound_from_quotient D W hW
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) r :=
    entrywise_to_quotient D ⊥
  have htW : D0.A t ∈ W := by
    change D.A t ∈ Submodule.span F2 ({D.A t} : Set Mat3)
    exact Submodule.mem_span_singleton_self (R := F2) (D.A t)
  have htKill : t ∈ killSet D0 W := by
    simp [killSet, htW]
  have hkillPositive : 1 ≤ (killSet D0 W).card :=
    Finset.one_le_card.mpr ⟨t, htKill⟩
  have hoccupation : (killSet D0 W).card ≤ r - 19 :=
    occupation_inequality (show (⊥ : Submodule F2 Mat3) ≤ W from bot_le)
      D0 hW hr19
  omega

end QiushiMatmul
end
