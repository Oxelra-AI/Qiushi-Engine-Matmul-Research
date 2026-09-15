import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit69Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o193from69_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o193from69_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 193, basis [342, 128, 32, 10, 1]. -/
def o193W_mono : Submodule F2 Mat3 := spanCodes [342, 128, 32, 10, 1]

private theorem o193from69_QtInv :
    (codeMat 98 : Mat3).transpose⁻¹ = (codeMat 140 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 98 : Mat3).transpose * (codeMat 140 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o193W_le_action_69 :
    o193W_mono ≤ actionW (codeMat 84) (codeMat 98) o69W := by
  apply o193from69_spanCodes_le_of_gens [342, 128, 32, 10, 1]
    (actionW (codeMat 84) (codeMat 98) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 206 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 206 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 206) = codeMat 342 := by
      unfold actionA
      rw [o193from69_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 206 * (codeMat 140 : Mat3).transpose = codeMat 342
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o193from69_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [o193from69_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 140 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o193from69_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [o193from69_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 140 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o193from69_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [o193from69_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 140 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o193from69_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 98) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [o193from69_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 140 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o193from69_codeMat_mem_actionW_of_witness hw hact

theorem orbit193_lb15_mono : QuotientRankAtLeast o193W_mono 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 98) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 98) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono o193W_le_action_69 hAct

end QiushiMatmul
