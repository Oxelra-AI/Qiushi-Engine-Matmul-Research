import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit55Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o131from55_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o131from55_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 131, basis [288, 160, 12, 2, 1]. -/
def o131W_mono : Submodule F2 Mat3 := spanCodes [288, 160, 12, 2, 1]

private theorem o131from55_QtInv :
    (codeMat 314 : Mat3).transpose⁻¹ = (codeMat 271 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 314 : Mat3).transpose * (codeMat 271 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o131W_le_action_55 :
    o131W_mono ≤ actionW (codeMat 169) (codeMat 314) o55W := by
  apply o131from55_spanCodes_le_of_gens [288, 160, 12, 2, 1]
    (actionW (codeMat 169) (codeMat 314) o55W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 438 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 169) (codeMat 314) (codeMat 438) = codeMat 288 := by
      unfold actionA
      rw [o131from55_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 438 * (codeMat 271 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o131from55_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 411 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 411 (by decide)
    have hact : actionA (codeMat 169) (codeMat 314) (codeMat 411) = codeMat 160 := by
      unfold actionA
      rw [o131from55_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 411 * (codeMat 271 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o131from55_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 134 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 134 (by decide)
    have hact : actionA (codeMat 169) (codeMat 314) (codeMat 134) = codeMat 12 := by
      unfold actionA
      rw [o131from55_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 134 * (codeMat 271 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o131from55_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 3 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 169) (codeMat 314) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [o131from55_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 3 * (codeMat 271 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o131from55_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o55W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 169) (codeMat 314) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [o131from55_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 2 * (codeMat 271 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o131from55_codeMat_mem_actionW_of_witness hw hact

theorem orbit131_lb14_mono : QuotientRankAtLeast o131W_mono 14 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 314 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 314) o55W) 14 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 314) hP hQ o55W 14
      step99_orbit55_lb14_unconditional
  exact quotientRankAtLeast_mono o131W_le_action_55 hAct

end QiushiMatmul
