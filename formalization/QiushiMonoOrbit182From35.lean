import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit35FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o182from35_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o182from35_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 182, basis [272, 84, 32, 10, 1]. -/
def o182W_mono : Submodule F2 Mat3 := spanCodes [272, 84, 32, 10, 1]

private theorem o182from35_QtInv :
    (codeMat 141 : Mat3).transpose⁻¹ = (codeMat 226 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 141 : Mat3).transpose * (codeMat 226 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o182W_le_action_35 :
    o182W_mono ≤ actionW (codeMat 273) (codeMat 141) orbit35W := by
  apply o182from35_spanCodes_le_of_gens [272, 84, 32, 10, 1]
    (actionW (codeMat 273) (codeMat 141) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 96 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 141) (codeMat 96) = codeMat 272 := by
      unfold actionA
      rw [o182from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 226 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o182from35_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 225 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 225 (by decide)
    have hact : actionA (codeMat 273) (codeMat 141) (codeMat 225) = codeMat 84 := by
      unfold actionA
      rw [o182from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 225 * (codeMat 226 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o182from35_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 141) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [o182from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 226 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o182from35_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 28 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 28 (by decide)
    have hact : actionA (codeMat 273) (codeMat 141) (codeMat 28) = codeMat 10 := by
      unfold actionA
      rw [o182from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 28 * (codeMat 226 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o182from35_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 273) (codeMat 141) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [o182from35_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 3 * (codeMat 226 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o182from35_codeMat_mem_actionW_of_witness hw hact

theorem orbit182_lb15_mono : QuotientRankAtLeast o182W_mono 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 141) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 141) hP hQ orbit35W 15
      orbit35_lb15
  exact quotientRankAtLeast_mono o182W_le_action_35 hAct

end QiushiMatmul
