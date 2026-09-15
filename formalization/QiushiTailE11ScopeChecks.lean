import QiushiTailCoverageChecks

open Matrix BigOperators
open scoped LinearAlgebra.Projectivization

noncomputable section
namespace QiushiMatmul.TailE11Scope

abbrev E11Quotient := Mat3 ⧸ lineRank1

theorem e11_quotient_finrank : Module.finrank F2 E11Quotient = 8 := by
  have hspan : lineRank1 = Submodule.span F2 {codeMat 1} := by
    unfold lineRank1 spanCodes
    congr 1
    ext X
    simp
  have hline : Module.finrank F2 lineRank1 = 1 := by
    rw [hspan]
    exact finrank_span_singleton (by decide : (codeMat 1 : Mat3) ≠ 0)
  have hmatrix : Module.finrank F2 Mat3 = 9 := by
    simpa using Module.finrank_matrix (R := F2) (M := F2) I3 I3
  have h := Submodule.finrank_quotient_add_finrank lineRank1
  change Module.finrank F2 E11Quotient + Module.finrank F2 lineRank1 =
    Module.finrank F2 Mat3 at h
  omega

theorem e11_quotient_card : Nat.card E11Quotient = 256 := by
  rw [Module.natCard_eq_pow_finrank (K := F2), e11_quotient_finrank]
  norm_num [F2]

/-- Directions are counted in projective space, not only as a numeric power of two. -/
theorem e11_direction_count : Nat.card (ℙ F2 E11Quotient) = 255 := by
  rw [Projectivization.card'', e11_quotient_card]
  norm_num [F2]

/-- The known full-tensor lower endpoint 21 implies only 18 through the +3 lift. -/
theorem e11_quotient_lb18_of_full_lb21 (hlower : RankAtLeast 21) :
    QuotientRankAtLeast lineRank1 18 := by
  intro r hr
  refine ⟨fun D => ?_⟩
  obtain ⟨E⟩ := TailCoverage.e11_quotient_lifts_by_three D
  have h := hlower (r + 3) E
  omega

end QiushiMatmul.TailE11Scope
