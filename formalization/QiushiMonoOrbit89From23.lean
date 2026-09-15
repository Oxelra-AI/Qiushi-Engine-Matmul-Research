import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit23FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o89from23_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o89from23_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 89, basis [128, 8, 4, 2, 1]. -/
def o89W_mono : Submodule F2 Mat3 := spanCodes [128, 8, 4, 2, 1]

private theorem o89from23_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o89W_le_action_23 :
    o89W_mono ≤ actionW (codeMat 161) (codeMat 266) orbit23W := by
  apply o89from23_spanCodes_le_of_gens [128, 8, 4, 2, 1]
    (actionW (codeMat 161) (codeMat 266) orbit23W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 8 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 8) = codeMat 128 := by
      unfold actionA
      rw [o89from23_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 266 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o89from23_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 128 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 128 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 128) = codeMat 8 := by
      unfold actionA
      rw [o89from23_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 128 * (codeMat 266 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o89from23_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 4 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 4 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 4) = codeMat 4 := by
      unfold actionA
      rw [o89from23_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 4 * (codeMat 266 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o89from23_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [o89from23_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o89from23_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ orbit23W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 4, 8, 80, 128] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [o89from23_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o89from23_codeMat_mem_actionW_of_witness hw hact

theorem orbit89_lb12_mono : QuotientRankAtLeast o89W_mono 12 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) orbit23W) 12 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ orbit23W 12
      orbit23_lb12
  exact quotientRankAtLeast_mono o89W_le_action_23 hAct

end QiushiMatmul
