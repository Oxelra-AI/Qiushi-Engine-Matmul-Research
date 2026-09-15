import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit11FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o38from11_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o38from11_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 38, basis [288, 128, 20, 8, 2, 1]. -/
def o38W_mono : Submodule F2 Mat3 := spanCodes [288, 128, 20, 8, 2, 1]

private theorem o38from11_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o38W_le_action_11 :
    o38W_mono ≤ actionW (codeMat 177) (codeMat 282) orbit11W := by
  apply o38from11_spanCodes_le_of_gens [288, 128, 20, 8, 2, 1]
    (actionW (codeMat 177) (codeMat 282) orbit11W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 32 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 32 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 32) = codeMat 288 := by
      unfold actionA
      rw [o38from11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 32 * (codeMat 267 : Mat3).transpose = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o38from11_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 216 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 216 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 216) = codeMat 128 := by
      unfold actionA
      rw [o38from11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 216 * (codeMat 267 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o38from11_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 196 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 196 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 196) = codeMat 20 := by
      unfold actionA
      rw [o38from11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 196 * (codeMat 267 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o38from11_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 128 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 128 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [o38from11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 128 * (codeMat 267 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o38from11_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 3) = codeMat 2 := by
      unfold actionA
      rw [o38from11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o38from11_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ orbit11W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68, 128] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 282) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [o38from11_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o38from11_codeMat_mem_actionW_of_witness hw hact

theorem orbit38_lb12_mono : QuotientRankAtLeast o38W_mono 12 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 282) orbit11W) 12 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 282) hP hQ orbit11W 12
      orbit11_lb12
  exact quotientRankAtLeast_mono o38W_le_action_11 hAct

end QiushiMatmul
