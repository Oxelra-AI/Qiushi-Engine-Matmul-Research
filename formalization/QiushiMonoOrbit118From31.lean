import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit31FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o118from31_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o118from31_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 118, basis [132, 32, 12, 2, 1]. -/
def o118W_mono : Submodule F2 Mat3 := spanCodes [132, 32, 12, 2, 1]

private theorem o118from31_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o118W_le_action_31 :
    o118W_mono ≤ actionW (codeMat 266) (codeMat 98) orbit31W := by
  apply o118from31_spanCodes_le_of_gens [132, 32, 12, 2, 1]
    (actionW (codeMat 266) (codeMat 98) orbit31W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 80 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 80 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [o118from31_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 80 * (codeMat 140 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o118from31_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [o118from31_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o118from31_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 20 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 20) = codeMat 12 := by
      unfold actionA
      rw [o118from31_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 20 * (codeMat 140 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o118from31_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 8) = codeMat 2 := by
      unfold actionA
      rw [o118from31_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 140 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o118from31_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 32 ∈ orbit31W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 32, 68] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 98) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [o118from31_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o118from31_codeMat_mem_actionW_of_witness hw hact

theorem orbit118_lb15_mono : QuotientRankAtLeast o118W_mono 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 98) orbit31W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 98) hP hQ orbit31W 15
      orbit31_lb15
  exact quotientRankAtLeast_mono o118W_le_action_31 hAct

end QiushiMatmul
