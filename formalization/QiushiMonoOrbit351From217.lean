import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit217Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o351from217_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o351from217_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 351, basis [302, 228, 16, 1]. -/
def o351W_mono : Submodule F2 Mat3 := spanCodes [302, 228, 16, 1]

private theorem o351from217_QtInv :
    (codeMat 330 : Mat3).transpose⁻¹ = (codeMat 394 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 330 : Mat3).transpose * (codeMat 394 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o351W_le_action_217 :
    o351W_mono ≤ actionW (codeMat 298) (codeMat 330) o217W := by
  apply o351from217_spanCodes_le_of_gens [302, 228, 16, 1]
    (actionW (codeMat 298) (codeMat 330) o217W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 106 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 106 (by decide)
    have hact : actionA (codeMat 298) (codeMat 330) (codeMat 106) = codeMat 302 := by
      unfold actionA
      rw [o351from217_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 106 * (codeMat 394 : Mat3).transpose = codeMat 302
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o351from217_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 298) (codeMat 330) (codeMat 228) = codeMat 228 := by
      unfold actionA
      rw [o351from217_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 228 * (codeMat 394 : Mat3).transpose = codeMat 228
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o351from217_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 298) (codeMat 330) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [o351from217_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 1 * (codeMat 394 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o351from217_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 432 ∈ o217W :=
      spanContainsCodeCore_implies_mem_spanCodes [308, 132, 96, 10, 1] 432 (by decide)
    have hact : actionA (codeMat 298) (codeMat 330) (codeMat 432) = codeMat 1 := by
      unfold actionA
      rw [o351from217_QtInv]
      show (codeMat 298 : Mat3).transpose * codeMat 432 * (codeMat 394 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o351from217_codeMat_mem_actionW_of_witness hw hact

theorem orbit351_lb16_mono : QuotientRankAtLeast o351W_mono 16 := by
  have hP : Invertible (codeMat 298 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 330 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 298) (codeMat 330) o217W) 16 :=
    @quotientRankAtLeast_action (codeMat 298) (codeMat 330) hP hQ o217W 16
      step99_orbit217_lb16_unconditional
  exact quotientRankAtLeast_mono o351W_le_action_217 hAct

end QiushiMatmul
