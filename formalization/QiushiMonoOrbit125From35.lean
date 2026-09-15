import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit35FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o125from35_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o125from35_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 125, basis [132, 96, 12, 2, 1]. -/
def o125W_mono : Submodule F2 Mat3 := spanCodes [132, 96, 12, 2, 1]

private theorem o125from35_QtInv :
    (codeMat 313 : Mat3).transpose⁻¹ = (codeMat 313 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 313 : Mat3).transpose * (codeMat 313 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o125W_le_action_35 :
    o125W_mono ≤ actionW (codeMat 401) (codeMat 313) orbit35W := by
  apply o125from35_spanCodes_le_of_gens [132, 96, 12, 2, 1]
    (actionW (codeMat 401) (codeMat 313) orbit35W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 150 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 150 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 150) = codeMat 132 := by
      unfold actionA
      rw [o125from35_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 150 * (codeMat 313 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o125from35_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 232 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 232 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 232) = codeMat 96 := by
      unfold actionA
      rw [o125from35_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 232 * (codeMat 313 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o125from35_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 30 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 30 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 30) = codeMat 12 := by
      unfold actionA
      rw [o125from35_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 30 * (codeMat 313 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o125from35_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 2 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [o125from35_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 2 * (codeMat 313 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o125from35_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ orbit35W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128] 3 (by decide)
    have hact : actionA (codeMat 401) (codeMat 313) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [o125from35_QtInv]
      show (codeMat 401 : Mat3).transpose * codeMat 3 * (codeMat 313 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o125from35_codeMat_mem_actionW_of_witness hw hact

theorem orbit125_lb15_mono : QuotientRankAtLeast o125W_mono 15 := by
  have hP : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 313 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 401) (codeMat 313) orbit35W) 15 :=
    @quotientRankAtLeast_action (codeMat 401) (codeMat 313) hP hQ orbit35W 15
      orbit35_lb15
  exact quotientRankAtLeast_mono o125W_le_action_35 hAct

end QiushiMatmul
