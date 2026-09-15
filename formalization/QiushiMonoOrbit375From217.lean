import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit217Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o375from217_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o375from217_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 375, basis [298, 160, 84, 1]. -/
def o375W_mono : Submodule F2 Mat3 := spanCodes [298, 160, 84, 1]

private theorem o375from217_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o375W_le_action_217 :
    o375W_mono ≤ actionW (codeMat 158) (codeMat 494) o217W := by
  apply o375from217_spanCodes_le_of_gens [298, 160, 84, 1]
    (actionW (codeMat 158) (codeMat 494) o217W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 239 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 239 (by decide)
    have hact : actionA (codeMat 158) (codeMat 494) (codeMat 239) = codeMat 298 := by
      unfold actionA
      rw [o375from217_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 239 * (codeMat 501 : Mat3).transpose = codeMat 298
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o375from217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 133 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 158) (codeMat 494) (codeMat 133) = codeMat 160 := by
      unfold actionA
      rw [o375from217_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 133 * (codeMat 501 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o375from217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 318 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 318 (by decide)
    have hact : actionA (codeMat 158) (codeMat 494) (codeMat 318) = codeMat 84 := by
      unfold actionA
      rw [o375from217_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 318 * (codeMat 501 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o375from217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 432 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 158) (codeMat 494) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [o375from217_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 432 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o375from217_codeMat_mem_actionW_of_witness hw hact

theorem orbit375_lb16_mono : QuotientRankAtLeast o375W_mono 16 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 494) o217W) 16 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 494) hP hQ o217W 16
      step99_orbit217_lb16_unconditional
  exact quotientRankAtLeast_mono o375W_le_action_217 hAct

end QiushiMatmul
