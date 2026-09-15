import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiOrbit29FP

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem o148from29_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem o148from29_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

/-- Wang orbit 148, basis [164, 68, 16, 10, 1]. -/
def o148W_mono : Submodule F2 Mat3 := spanCodes [164, 68, 16, 10, 1]

private theorem o148from29_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem o148W_le_action_29 :
    o148W_mono ≤ actionW (codeMat 266) (codeMat 282) orbit29W := by
  apply o148from29_spanCodes_le_of_gens [164, 68, 16, 10, 1]
    (actionW (codeMat 266) (codeMat 282) orbit29W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4
  · subst h0
    have hw : codeMat 228 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 228) = codeMat 164 := by
      unfold actionA
      rw [o148from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o148from29_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [o148from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o148from29_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 3) = codeMat 16 := by
      unfold actionA
      rw [o148from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 267 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o148from29_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 26 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 26 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 26) = codeMat 10 := by
      unfold actionA
      rw [o148from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 26 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o148from29_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit29W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [o148from29_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact o148from29_codeMat_mem_actionW_of_witness hw hact

theorem orbit148_lb15_mono : QuotientRankAtLeast o148W_mono 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 282) orbit29W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 282) hP hQ orbit29W 15
      orbit29_lb15
  exact quotientRankAtLeast_mono o148W_le_action_29 hAct

end QiushiMatmul
