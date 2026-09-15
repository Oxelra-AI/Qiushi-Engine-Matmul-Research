import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit67Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o232from67_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o232from67_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 232, basis [258, 140, 98, 16, 1]. -/
def o232W_mono : Submodule F2 Mat3 := spanCodes [258, 140, 98, 16, 1]

private theorem o232from67_QtInv :
    (codeMat 286 : Mat3).transpose⁻¹ = (codeMat 303 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 286 : Mat3).transpose * (codeMat 303 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o232W_le_action_67 :
    o232W_mono ≤ actionW (codeMat 267) (codeMat 286) o67W := by
  apply o232from67_spanCodes_le_of_gens [258, 140, 98, 16, 1]
    (actionW (codeMat 267) (codeMat 286) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 344 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 344 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 344) = codeMat 258 := by
      unfold actionA
      rw [o232from67_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 344 * (codeMat 303 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o232from67_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 250 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 250 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 250) = codeMat 140 := by
      unfold actionA
      rw [o232from67_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 250 * (codeMat 303 : Mat3).transpose = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o232from67_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 181 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 181 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 181) = codeMat 98 := by
      unfold actionA
      rw [o232from67_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 181 * (codeMat 303 : Mat3).transpose = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o232from67_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [o232from67_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 303 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o232from67_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 286) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [o232from67_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 303 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o232from67_codeMat_mem_actionW_of_witness hw hact

theorem orbit232_lb15_mono : QuotientRankAtLeast o232W_mono 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 286 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 286) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 286) hP hQ o67W 15
      step99_orbit67_lb15_unconditional
  exact quotientRankAtLeast_mono o232W_le_action_67 hAct

end QiushiMatmul
