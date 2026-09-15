import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport

/-! Finite witnesses for transporting a proved quotient bound to an actual
source subspace. Witness search is external; every witness is checked here. -/

namespace QiushiMatmul

theorem quotientRankAtLeast_weaken {W : Submodule F2 Mat3} {m n : Nat}
    (h : QuotientRankAtLeast W n) (hmn : m ≤ n) : QuotientRankAtLeast W m := by
  intro r hr
  exact h r (lt_of_lt_of_le hr hmn)

theorem quotientRankAtLeast_of_code_transport
    (basis : List Nat) (pairs : List (Nat × Nat))
    (P Q Qinv : Mat3) (flip : Bool) {n : Nat}
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (hInv : Q.transpose * Qinv.transpose = 1)
    (hPairs : ∀ e ∈ pairs,
      spanContainsCode basis e.2 = true ∧
      P.transpose * (if flip then (codeMat e.2).transpose else codeMat e.2) *
        Qinv.transpose = codeMat e.1)
    (hSource : QuotientRankAtLeast (spanCodes basis) n) :
    QuotientRankAtLeast (spanCodes (pairs.map Prod.fst)) n := by
  letI : Invertible P := Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP)
  letI : Invertible Q := Matrix.invertibleOfIsUnitDet Q (isUnit_iff_ne_zero.mpr hQ)
  have hInv' : Q.transpose⁻¹ = Qinv.transpose := Matrix.inv_eq_right_inv hInv
  let U := if flip then transposeW (spanCodes basis) else spanCodes basis
  have hU : QuotientRankAtLeast U n := by
    cases flip
    · exact hSource
    · exact quotientRankAtLeast_transpose hSource
  apply quotientRankAtLeast_mono (U := actionW P Q U) _ (quotientRankAtLeast_action hU)
  unfold spanCodes
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hmem, heq⟩ := hPairs e he
  have hw := spanContainsCode_implies_mem_spanCodes basis e.2 hmem
  have hu : (if flip then (codeMat e.2).transpose else codeMat e.2) ∈ U := by
    cases flip
    · exact hw
    · exact ⟨codeMat e.2, hw, rfl⟩
  refine ⟨_, hu, ?_⟩
  change P.transpose * (if flip then (codeMat e.2).transpose else codeMat e.2) *
    Q.transpose⁻¹ = codeMat e.1
  rw [hInv']
  exact heq

end QiushiMatmul
