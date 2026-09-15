import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit196Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o320from196_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o320from196_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 320, basis [304, 160, 10, 1]. -/
def o320W_mono : Submodule F2 Mat3 := spanCodes [304, 160, 10, 1]

private theorem o320from196_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o320W_le_action_196 :
    o320W_mono ≤ actionW (codeMat 281) (codeMat 273) o196W := by
  apply o320from196_spanCodes_le_of_gens [304, 160, 10, 1]
    (actionW (codeMat 281) (codeMat 273) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 310 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 310 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 310) = codeMat 304 := by
      unfold actionA
      rw [o320from196_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 310 * (codeMat 273 : Mat3).transpose = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o320from196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 164 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 164) = codeMat 160 := by
      unfold actionA
      rw [o320from196_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 164 * (codeMat 273 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o320from196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 11 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [o320from196_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 11 * (codeMat 273 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o320from196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o320from196_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o320from196_codeMat_mem_actionW_of_witness hw hact

theorem orbit320_lb16_mono : QuotientRankAtLeast o320W_mono 16 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 273) o196W) 16 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 273) hP hQ o196W 16
      step99_orbit196_lb16_unconditional
  exact quotientRankAtLeast_mono o320W_le_action_196 hAct

end QiushiMatmul
