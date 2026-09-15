import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit196Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o311from196_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o311from196_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 311, basis [384, 96, 10, 1]. -/
def o311W_mono : Submodule F2 Mat3 := spanCodes [384, 96, 10, 1]

private theorem o311from196_QtInv :
    (codeMat 498 : Mat3).transpose⁻¹ = (codeMat 206 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 498 : Mat3).transpose * (codeMat 206 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o311W_le_action_196 :
    o311W_mono ≤ actionW (codeMat 460) (codeMat 498) o196W := by
  apply o311from196_spanCodes_le_of_gens [384, 96, 10, 1]
    (actionW (codeMat 460) (codeMat 498) o196W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 1 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 460) (codeMat 498) (codeMat 1) = codeMat 384 := by
      unfold actionA
      rw [o311from196_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 1 * (codeMat 206 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o311from196_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 434 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 434 (by decide)
    have hact : actionA (codeMat 460) (codeMat 498) (codeMat 434) = codeMat 96 := by
      unfold actionA
      rw [o311from196_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 434 * (codeMat 206 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o311from196_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 284 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 284 (by decide)
    have hact : actionA (codeMat 460) (codeMat 498) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [o311from196_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 284 * (codeMat 206 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o311from196_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 32 ∈ o196W :=
      spanContainsCodeCore_implies_mem_spanCodes [278, 132, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 460) (codeMat 498) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [o311from196_QtInv]
      show (codeMat 460 : Mat3).transpose * codeMat 32 * (codeMat 206 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o311from196_codeMat_mem_actionW_of_witness hw hact

theorem orbit311_lb16_mono : QuotientRankAtLeast o311W_mono 16 := by
  have hP : Invertible (codeMat 460 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 498 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 460) (codeMat 498) o196W) 16 :=
    @quotientRankAtLeast_action (codeMat 460) (codeMat 498) hP hQ o196W 16
      step99_orbit196_lb16_unconditional
  exact quotientRankAtLeast_mono o311W_le_action_196 hAct

end QiushiMatmul
