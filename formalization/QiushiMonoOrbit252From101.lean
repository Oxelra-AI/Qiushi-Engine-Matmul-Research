import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit101FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o252from101_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o252from101_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 252, basis [32, 8, 2, 1]. -/
def o252W_mono : Submodule F2 Mat3 := spanCodes [32, 8, 2, 1]

private theorem o252from101_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o252W_le_action_101 :
    o252W_mono ≤ actionW (codeMat 266) (codeMat 161) orbit101W := by
  apply o252from101_spanCodes_le_of_gens [32, 8, 2, 1]
    (actionW (codeMat 266) (codeMat 161) orbit101W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 2 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 2 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 2) = codeMat 32 := by
      unfold actionA
      rw [o252from101_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o252from101_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [o252from101_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o252from101_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 32 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 32) = codeMat 2 := by
      unfold actionA
      rw [o252from101_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o252from101_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit101W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 32, 84] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [o252from101_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o252from101_codeMat_mem_actionW_of_witness hw hact

theorem orbit252_lb15_mono : QuotientRankAtLeast o252W_mono 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) orbit101W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ orbit101W 15
      orbit101_lb15
  exact quotientRankAtLeast_mono o252W_le_action_101 hAct

end QiushiMatmul
