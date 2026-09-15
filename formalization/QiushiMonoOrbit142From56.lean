import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiStep99Orbit56Dispatch

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o142from56_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o142from56_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 142, basis [272, 84, 32, 2, 1]. -/
def o142W_mono : Submodule F2 Mat3 := spanCodes [272, 84, 32, 2, 1]

private theorem o142from56_QtInv :
    (codeMat 281 : Mat3).transpose⁻¹ = (codeMat 281 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 281 : Mat3).transpose * (codeMat 281 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o142W_le_action_56 :
    o142W_mono ≤ actionW (codeMat 177) (codeMat 281) o56W := by
  apply o142from56_spanCodes_le_of_gens [272, 84, 32, 2, 1]
    (actionW (codeMat 177) (codeMat 281) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 177) (codeMat 281) (codeMat 416) = codeMat 272 := by
      unfold actionA
      rw [o142from56_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 416 * (codeMat 281 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o142from56_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 92 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 92 (by decide)
    have hact : actionA (codeMat 177) (codeMat 281) (codeMat 92) = codeMat 84 := by
      unfold actionA
      rw [o142from56_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 92 * (codeMat 281 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o142from56_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 177) (codeMat 281) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [o142from56_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 256 * (codeMat 281 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o142from56_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 177) (codeMat 281) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [o142from56_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 2 * (codeMat 281 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o142from56_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 177) (codeMat 281) (codeMat 3) = codeMat 1 := by
      unfold actionA
      rw [o142from56_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 3 * (codeMat 281 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o142from56_codeMat_mem_actionW_of_witness hw hact

theorem orbit142_lb14_mono : QuotientRankAtLeast o142W_mono 14 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 281) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 281) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono o142W_le_action_56 hAct

end QiushiMatmul
