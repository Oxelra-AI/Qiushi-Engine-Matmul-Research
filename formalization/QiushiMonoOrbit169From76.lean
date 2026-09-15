import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit76Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o169from76_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o169from76_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 169, basis [288, 128, 20, 10, 1]. -/
def o169W_mono : Submodule F2 Mat3 := spanCodes [288, 128, 20, 10, 1]

private theorem o169from76_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o169W_le_action_76 :
    o169W_mono ≤ actionW (codeMat 302) (codeMat 212) o76W := by
  apply o169from76_spanCodes_le_of_gens [288, 128, 20, 10, 1]
    (actionW (codeMat 302) (codeMat 212) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 1) = codeMat 288 := by
      unfold actionA
      rw [o169from76_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o169from76_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 384) = codeMat 128 := by
      unfold actionA
      rw [o169from76_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 384 * (codeMat 86 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o169from76_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 462) = codeMat 20 := by
      unfold actionA
      rw [o169from76_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 462 * (codeMat 86 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o169from76_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 180 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 180) = codeMat 10 := by
      unfold actionA
      rw [o169from76_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 180 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o169from76_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 302) (codeMat 212) (codeMat 288) = codeMat 1 := by
      unfold actionA
      rw [o169from76_QtInv]
      show (codeMat 302 : Mat3).transpose * codeMat 288 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o169from76_codeMat_mem_actionW_of_witness hw hact

theorem orbit169_lb15_mono : QuotientRankAtLeast o169W_mono 15 := by
  have hP : Invertible (codeMat 302 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 302) (codeMat 212) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 302) (codeMat 212) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono o169W_le_action_76 hAct

end QiushiMatmul
