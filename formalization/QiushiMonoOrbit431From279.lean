import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep104Orbit279Split

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o431from279_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o431from279_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 431, basis [228, 16, 1]. -/
def o431W_mono : Submodule F2 Mat3 := spanCodes [228, 16, 1]

private theorem o431from279_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o431W_le_action_279 :
    o431W_mono ≤ actionW (codeMat 267) (codeMat 282) o279W := by
  apply o431from279_spanCodes_le_of_gens [228, 16, 1]
    (actionW (codeMat 267) (codeMat 282) o279W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2
  · subst h0
    have hw : codeMat 68 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 68) = codeMat 228 := by
      unfold actionA
      rw [o431from279_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 68 * (codeMat 267 : Mat3).transpose = codeMat 228
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o431from279_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 27 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [o431from279_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o431from279_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o279W :=
      spanContainsCodeCore_implies_mem_spanCodes [68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [o431from279_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o431from279_codeMat_mem_actionW_of_witness hw hact

theorem orbit431_lb17_mono : QuotientRankAtLeast o431W_mono 17 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) o279W) 17 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ o279W 17
      step104_orbit279_lb17
  exact quotientRankAtLeast_mono o431W_le_action_279 hAct

end QiushiMatmul
