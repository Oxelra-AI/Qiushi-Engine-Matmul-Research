import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit150Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o347from150_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o347from150_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 347, basis [258, 228, 16, 1]. -/
def o347W_mono : Submodule F2 Mat3 := spanCodes [258, 228, 16, 1]

private theorem o347from150_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o347W_le_action_150 :
    o347W_mono ≤ actionW (codeMat 267) (codeMat 282) o150W := by
  apply o347from150_spanCodes_le_of_gens [258, 228, 16, 1]
    (actionW (codeMat 267) (codeMat 282) o150W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 280 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 280) = codeMat 258 := by
      unfold actionA
      rw [o347from150_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o347from150_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 68 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 68) = codeMat 228 := by
      unfold actionA
      rw [o347from150_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 68 * (codeMat 267 : Mat3).transpose = codeMat 228
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o347from150_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 27 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [o347from150_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o347from150_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o150W :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [o347from150_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o347from150_codeMat_mem_actionW_of_witness hw hact

theorem orbit347_lb16_mono : QuotientRankAtLeast o347W_mono 16 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) o150W) 16 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ o150W 16
      step99_orbit150_lb16_unconditional
  exact quotientRankAtLeast_mono o347W_le_action_150 hAct

end QiushiMatmul
