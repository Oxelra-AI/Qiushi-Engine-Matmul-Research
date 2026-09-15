import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit14FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o53from14_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o53from14_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 53, basis [384, 80, 32, 12, 2, 1]. -/
def o53W_mono : Submodule F2 Mat3 := spanCodes [384, 80, 32, 12, 2, 1]

private theorem o53from14_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o53W_le_action_14 :
    o53W_mono ≤ actionW (codeMat 84) (codeMat 84) orbit14W := by
  apply o53from14_spanCodes_le_of_gens [384, 80, 32, 12, 2, 1]
    (actionW (codeMat 84) (codeMat 84) orbit14W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 3 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 3 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 3) = codeMat 384 := by
      unfold actionA
      rw [o53from14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 3 * (codeMat 84 : Mat3).transpose = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o53from14_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 20 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 20) = codeMat 80 := by
      unfold actionA
      rw [o53from14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 20 * (codeMat 84 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o53from14_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [o53from14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o53from14_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 96 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 96) = codeMat 12 := by
      unfold actionA
      rw [o53from14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 96 * (codeMat 84 : Mat3).transpose = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o53from14_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 128 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 128 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 128) = codeMat 2 := by
      unfold actionA
      rw [o53from14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 128 * (codeMat 84 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o53from14_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ orbit14W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 20, 96, 128, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [o53from14_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o53from14_codeMat_mem_actionW_of_witness hw hact

theorem orbit53_lb12_mono : QuotientRankAtLeast o53W_mono 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit14W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit14W 12
      orbit14_lb12
  exact quotientRankAtLeast_mono o53W_le_action_14 hAct

end QiushiMatmul
