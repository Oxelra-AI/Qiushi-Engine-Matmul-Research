import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit120Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o271from120_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o271from120_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 271, basis [336, 32, 2, 1]. -/
def o271W_mono : Submodule F2 Mat3 := spanCodes [336, 32, 2, 1]

private theorem o271from120_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = (codeMat 277 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * (codeMat 277 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o271W_le_action_120 :
    o271W_mono ≤ actionW (codeMat 281) (codeMat 277) o120W := by
  apply o271from120_spanCodes_le_of_gens [336, 32, 2, 1]
    (actionW (codeMat 281) (codeMat 277) o120W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3
  · subst h0
    have hw : codeMat 274 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 274 (by decide)
    have hact : actionA (codeMat 281) (codeMat 277) (codeMat 274) = codeMat 336 := by
      unfold actionA
      rw [o271from120_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 274 * (codeMat 277 : Mat3).transpose = codeMat 336
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o271from120_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 45 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 45 (by decide)
    have hact : actionA (codeMat 281) (codeMat 277) (codeMat 45) = codeMat 32 := by
      unfold actionA
      rw [o271from120_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 45 * (codeMat 277 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o271from120_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 2 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 277) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [o271from120_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 277 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o271from120_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o120W :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 32, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [o271from120_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 277 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o271from120_codeMat_mem_actionW_of_witness hw hact

theorem orbit271_lb15_mono : QuotientRankAtLeast o271W_mono 15 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 277) o120W) 15 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 277) hP hQ o120W 15
      step99_orbit120_lb15_unconditional
  exact quotientRankAtLeast_mono o271W_le_action_120 hAct

end QiushiMatmul
