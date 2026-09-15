import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit212Consumer
import QiushiStep99Orbit65Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit57Dispatch
import QiushiWcOrbit79Dispatch
import QiushiWcOrbit84Dispatch
import QiushiWcOrbit50Dispatch
import QiushiWcOrbit70Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc212_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc212_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc212s0_QtInv :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s0_contain :
    (o212SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 107) (codeMat 481) o65W := by
  change spanCodes [258, 132, 96, 16, 10, 1] ≤ actionW (codeMat 107) (codeMat 481) o65W
  apply step109wc212_spanCodes_le_of_gens [258, 132, 96, 16, 10, 1]
    (actionW (codeMat 107) (codeMat 481) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 176 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 176 (by decide)
    have hact : actionA (codeMat 107) (codeMat 481) (codeMat 176) = codeMat 258 := by
      unfold actionA
      rw [step109wc212s0_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 176 * (codeMat 185 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 107) (codeMat 481) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s0_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 160 * (codeMat 185 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 238 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 107) (codeMat 481) (codeMat 238) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s0_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 238 * (codeMat 185 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 107) (codeMat 481) (codeMat 260) = codeMat 16 := by
      unfold actionA
      rw [step109wc212s0_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 260 * (codeMat 185 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 107) (codeMat 481) (codeMat 69) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s0_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 69 * (codeMat 185 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 107) (codeMat 481) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s0_QtInv]
      show (codeMat 107 : Mat3).transpose * codeMat 320 * (codeMat 185 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s0Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 107 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 107) (codeMat 481) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 107) (codeMat 481) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc212s0_contain hAct


private theorem step109wc212s1_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = (codeMat 266 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * (codeMat 266 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s1_contain :
    (o212SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 267) (codeMat 266) o69W := by
  change spanCodes [256, 132, 96, 18, 10, 1] ≤ actionW (codeMat 267) (codeMat 266) o69W
  apply step109wc212_spanCodes_le_of_gens [256, 132, 96, 18, 10, 1]
    (actionW (codeMat 267) (codeMat 266) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc212s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 256 * (codeMat 266 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 96) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 96 * (codeMat 266 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 164 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 164) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 164 * (codeMat 266 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 1) = codeMat 18 := by
      unfold actionA
      rw [step109wc212s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 1 * (codeMat 266 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 26 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 26) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 26 * (codeMat 266 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s1_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 266 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s1Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 266) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 266) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc212s1_contain hAct


private theorem step109wc212s2_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = (codeMat 99 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * (codeMat 99 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s2_contain :
    (o212SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 87) (codeMat 172) o77W := by
  change spanCodes [262, 132, 96, 20, 10, 1] ≤ actionW (codeMat 87) (codeMat 172) o77W
  apply step109wc212_spanCodes_le_of_gens [262, 132, 96, 20, 10, 1]
    (actionW (codeMat 87) (codeMat 172) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 283 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 87) (codeMat 172) (codeMat 283) = codeMat 262 := by
      unfold actionA
      rw [step109wc212s2_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 283 * (codeMat 99 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 484 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 87) (codeMat 172) (codeMat 484) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s2_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 484 * (codeMat 99 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 138 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 138 (by decide)
    have hact : actionA (codeMat 87) (codeMat 172) (codeMat 138) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s2_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 138 * (codeMat 99 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 224 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 224 (by decide)
    have hact : actionA (codeMat 87) (codeMat 172) (codeMat 224) = codeMat 20 := by
      unfold actionA
      rw [step109wc212s2_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 224 * (codeMat 99 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 272 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide)
    have hact : actionA (codeMat 87) (codeMat 172) (codeMat 272) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s2_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 272 * (codeMat 99 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 87) (codeMat 172) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s2_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 128 * (codeMat 99 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s2Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 172) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 172) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc212s2_contain hAct


private theorem step109wc212s3_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = (codeMat 183 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * (codeMat 183 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s3_contain :
    (o212SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 249) (codeMat 419) o76W := by
  change spanCodes [274, 132, 68, 36, 10, 1] ≤ actionW (codeMat 249) (codeMat 419) o76W
  apply step109wc212_spanCodes_le_of_gens [274, 132, 68, 36, 10, 1]
    (actionW (codeMat 249) (codeMat 419) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 240 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 240 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 240) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s3_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 240 * (codeMat 183 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 366) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s3_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 366 * (codeMat 183 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 78) = codeMat 68 := by
      unfold actionA
      rw [step109wc212s3_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 78 * (codeMat 183 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step109wc212s3_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 384 * (codeMat 183 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 68 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 68 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 68) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s3_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 68 * (codeMat 183 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 249) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s3_QtInv]
      show (codeMat 249 : Mat3).transpose * codeMat 1 * (codeMat 183 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s3Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 249 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 249) (codeMat 419) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 249) (codeMat 419) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc212s3_contain hAct


private theorem step109wc212s4_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s4_contain :
    (o212SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 93) (codeMat 482) o69W := by
  change spanCodes [274, 132, 70, 38, 10, 1] ≤ actionW (codeMat 93) (codeMat 482) o69W
  apply step109wc212_spanCodes_le_of_gens [274, 132, 70, 38, 10, 1]
    (actionW (codeMat 93) (codeMat 482) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 430 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 430 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 430) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s4_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 430 * (codeMat 143 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 197 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 197 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 197) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s4_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 197 * (codeMat 143 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 452 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 452) = codeMat 70 := by
      unfold actionA
      rw [step109wc212s4_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 452 * (codeMat 143 : Mat3).transpose = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 368 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 368) = codeMat 38 := by
      unfold actionA
      rw [step109wc212s4_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 368 * (codeMat 143 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s4_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 96 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 93) (codeMat 482) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s4_QtInv]
      show (codeMat 93 : Mat3).transpose * codeMat 256 * (codeMat 143 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s4Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 93 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 93) (codeMat 482) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 93) (codeMat 482) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc212s4_contain hAct

private def step109wc212s5SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem step109wc212s5SrcT_lb : QuotientRankAtLeast step109wc212s5SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : step109wc212s5SrcT ≤ transposeW o77W := by
    unfold step109wc212s5SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 80 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 20, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 20 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 32 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 128, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 128 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 10 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 10, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 10 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o77W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc212s5_QtInv :
    (codeMat 117 : Mat3).transpose⁻¹ = (codeMat 380 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 117 : Mat3).transpose * (codeMat 380 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s5_contain :
    (o212SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 106) (codeMat 117) step109wc212s5SrcT := by
  change spanCodes [274, 132, 80, 48, 10, 1] ≤ actionW (codeMat 106) (codeMat 117) step109wc212s5SrcT
  apply step109wc212_spanCodes_le_of_gens [274, 132, 80, 48, 10, 1]
    (actionW (codeMat 106) (codeMat 117) step109wc212s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 90 ∈ step109wc212s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 90 (by decide)
    have hact : actionA (codeMat 106) (codeMat 117) (codeMat 90) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s5_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 90 * (codeMat 380 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 80 ∈ step109wc212s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 80 (by decide)
    have hact : actionA (codeMat 106) (codeMat 117) (codeMat 80) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s5_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 80 * (codeMat 380 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 362 ∈ step109wc212s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 362 (by decide)
    have hact : actionA (codeMat 106) (codeMat 117) (codeMat 362) = codeMat 80 := by
      unfold actionA
      rw [step109wc212s5_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 362 * (codeMat 380 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ step109wc212s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 106) (codeMat 117) (codeMat 1) = codeMat 48 := by
      unfold actionA
      rw [step109wc212s5_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 1 * (codeMat 380 : Mat3).transpose = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 133 ∈ step109wc212s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 133 (by decide)
    have hact : actionA (codeMat 106) (codeMat 117) (codeMat 133) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s5_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 133 * (codeMat 380 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ step109wc212s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 106) (codeMat 117) (codeMat 320) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s5_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 320 * (codeMat 380 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s5Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 117) step109wc212s5SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 117) hP hQ step109wc212s5SrcT 15
      step109wc212s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc212s5_contain hAct


private theorem step109wc212s6_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s6_contain :
    (o212SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 281) (codeMat 161) o56W := by
  change spanCodes [274, 128, 96, 10, 4, 1] ≤ actionW (codeMat 281) (codeMat 161) o56W
  apply step109wc212_spanCodes_le_of_gens [274, 128, 96, 10, 4, 1]
    (actionW (codeMat 281) (codeMat 161) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 160 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 160) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 160 * (codeMat 161 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc212s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 82 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 82 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 82) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 82 * (codeMat 161 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 13 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 13 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 13) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 13 * (codeMat 161 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc212s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s6_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s6Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨6, by omega⟩) 14 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 161) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 161) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc212s6_contain hAct


private theorem step109wc212s7_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = (codeMat 331 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * (codeMat 331 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s7_contain :
    (o212SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 241) (codeMat 410) o57W_wc := by
  change spanCodes [274, 130, 96, 10, 6, 1] ≤ actionW (codeMat 241) (codeMat 410) o57W_wc
  apply step109wc212_spanCodes_le_of_gens [274, 130, 96, 10, 6, 1]
    (actionW (codeMat 241) (codeMat 410) o57W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 228 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 228 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 228) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 228 * (codeMat 331 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 504 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 504 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 504) = codeMat 130 := by
      unfold actionA
      rw [step109wc212s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 504 * (codeMat 331 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 406 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 406 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 406) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 406 * (codeMat 331 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 133 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 133 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 133) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 133 * (codeMat 331 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 3 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 3) = codeMat 6 := by
      unfold actionA
      rw [step109wc212s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 3 * (codeMat 331 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ o57W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 241) (codeMat 410) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s7_QtInv]
      show (codeMat 241 : Mat3).transpose * codeMat 2 * (codeMat 331 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s7Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨7, by omega⟩) 14 := by
  have hP : Invertible (codeMat 241 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 241) (codeMat 410) o57W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 241) (codeMat 410) hP hQ o57W_wc 14
      step109_orbit57_lb14_wc
  exact quotientRankAtLeast_mono step109wc212s7_contain hAct


private theorem step109wc212s8_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s8_contain :
    (o212SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 465) (codeMat 279) o79W_wc := by
  change spanCodes [260, 132, 96, 22, 10, 1] ≤ actionW (codeMat 465) (codeMat 279) o79W_wc
  apply step109wc212_spanCodes_le_of_gens [260, 132, 96, 22, 10, 1]
    (actionW (codeMat 465) (codeMat 279) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 360 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 360) = codeMat 260 := by
      unfold actionA
      rw [step109wc212s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 360 * (codeMat 279 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 222 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 222 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 222) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 222 * (codeMat 279 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 97 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 97) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 97 * (codeMat 279 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 30 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 30) = codeMat 22 := by
      unfold actionA
      rw [step109wc212s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 30 * (codeMat 279 : Mat3).transpose = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 11 * (codeMat 279 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 465) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s8_QtInv]
      show (codeMat 465 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s8Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 465 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 465) (codeMat 279) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 465) (codeMat 279) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc212s8_contain hAct

private def step109wc212s9SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc212s9SrcT_lb : QuotientRankAtLeast step109wc212s9SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc212s9SrcT ≤ transposeW o56W := by
    unfold step109wc212s9SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 160 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 160, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 160 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 20 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 80, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 80 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o56W
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc212s9_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s9_contain :
    (o212SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 161) (codeMat 275) step109wc212s9SrcT := by
  change spanCodes [274, 132, 64, 32, 10, 1] ≤ actionW (codeMat 161) (codeMat 275) step109wc212s9SrcT
  apply step109wc212_spanCodes_le_of_gens [274, 132, 64, 32, 10, 1]
    (actionW (codeMat 161) (codeMat 275) step109wc212s9SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 227 ∈ step109wc212s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 227 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 227) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 227 * (codeMat 275 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 28 ∈ step109wc212s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 28 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 28) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 28 * (codeMat 275 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 8 ∈ step109wc212s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc212s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 275 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ step109wc212s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc212s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 275 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 67 ∈ step109wc212s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 67 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 67) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 67 * (codeMat 275 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ step109wc212s9SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s9_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s9Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 275) step109wc212s9SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 275) hP hQ step109wc212s9SrcT 14
      step109wc212s9SrcT_lb
  exact quotientRankAtLeast_mono step109wc212s9_contain hAct

private def step109wc212s10SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 66, 34, 8, 1]

private theorem step109wc212s10SrcT_lb : QuotientRankAtLeast step109wc212s10SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step109_orbit57_lb14_wc
  have hle : step109wc212s10SrcT ≤ transposeW o57W_wc := by
    unfold step109wc212s10SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0
      show codeMat 272 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 272, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 272 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 66 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 12, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 12 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 34 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 136, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 136 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 1 ∈ Submodule.map transposeLinearMap o57W_wc
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc212s10_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s10_contain :
    (o212SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 271) (codeMat 423) step109wc212s10SrcT := by
  change spanCodes [274, 132, 66, 34, 10, 1] ≤ actionW (codeMat 271) (codeMat 423) step109wc212s10SrcT
  apply step109wc212_spanCodes_le_of_gens [274, 132, 66, 34, 10, 1]
    (actionW (codeMat 271) (codeMat 423) step109wc212s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 133 ∈ step109wc212s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 133 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 133) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s10_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 133 * (codeMat 181 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 376 ∈ step109wc212s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 376 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 376) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s10_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 376 * (codeMat 181 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 104 ∈ step109wc212s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 104 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 104) = codeMat 66 := by
      unfold actionA
      rw [step109wc212s10_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 104 * (codeMat 181 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 471 ∈ step109wc212s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 471 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 471) = codeMat 34 := by
      unfold actionA
      rw [step109wc212s10_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 471 * (codeMat 181 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 97 ∈ step109wc212s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 97 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 97) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s10_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 97 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ step109wc212s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 66, 34, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 271) (codeMat 423) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s10_QtInv]
      show (codeMat 271 : Mat3).transpose * codeMat 8 * (codeMat 181 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s10Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 271 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 271) (codeMat 423) step109wc212s10SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 271) (codeMat 423) hP hQ step109wc212s10SrcT 14
      step109wc212s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc212s10_contain hAct


private theorem step109wc212s11_QtInv :
    (codeMat 425 : Mat3).transpose⁻¹ = (codeMat 249 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 425 : Mat3).transpose * (codeMat 249 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s11_contain :
    (o212SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 106) (codeMat 425) o79W_wc := by
  change spanCodes [274, 132, 82, 50, 10, 1] ≤ actionW (codeMat 106) (codeMat 425) o79W_wc
  apply step109wc212_spanCodes_le_of_gens [274, 132, 82, 50, 10, 1]
    (actionW (codeMat 106) (codeMat 425) o79W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 180 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 106) (codeMat 425) (codeMat 180) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s11_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 180 * (codeMat 249 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 160 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 106) (codeMat 425) (codeMat 160) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s11_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 160 * (codeMat 249 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 476 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 476 (by decide)
    have hact : actionA (codeMat 106) (codeMat 425) (codeMat 476) = codeMat 82 := by
      unfold actionA
      rw [step109wc212s11_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 476 * (codeMat 249 : Mat3).transpose = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 258 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 106) (codeMat 425) (codeMat 258) = codeMat 50 := by
      unfold actionA
      rw [step109wc212s11_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 258 * (codeMat 249 : Mat3).transpose = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 259 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 259 (by decide)
    have hact : actionA (codeMat 106) (codeMat 425) (codeMat 259) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s11_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 259 * (codeMat 249 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o79W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 106) (codeMat 425) (codeMat 192) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s11_QtInv]
      show (codeMat 106 : Mat3).transpose * codeMat 192 * (codeMat 249 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s11Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 106 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 106) (codeMat 425) o79W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 106) (codeMat 425) hP hQ o79W_wc 14
      step109_orbit79_lb14_wc
  exact quotientRankAtLeast_mono step109wc212s11_contain hAct


private theorem step109wc212s12_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s12_contain :
    (o212SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 123) (codeMat 412) o84W_wc := by
  change spanCodes [274, 132, 84, 52, 10, 1] ≤ actionW (codeMat 123) (codeMat 412) o84W_wc
  apply step109wc212_spanCodes_le_of_gens [274, 132, 84, 52, 10, 1]
    (actionW (codeMat 123) (codeMat 412) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 43 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 43 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 43) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 43 * (codeMat 111 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 374 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 374) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 374 * (codeMat 111 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 212 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 212 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 212) = codeMat 84 := by
      unfold actionA
      rw [step109wc212s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 212 * (codeMat 111 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 387 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 387 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 387) = codeMat 52 := by
      unfold actionA
      rw [step109wc212s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 387 * (codeMat 111 : Mat3).transpose = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 258 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 258) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 258 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 123) (codeMat 412) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s12_QtInv]
      show (codeMat 123 : Mat3).transpose * codeMat 128 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s12Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 123 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 123) (codeMat 412) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 123) (codeMat 412) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc212s12_contain hAct


private theorem step109wc212s13_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s13_contain :
    (o212SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 273) (codeMat 273) o50W_wc := by
  change spanCodes [272, 132, 96, 8, 2, 1] ≤ actionW (codeMat 273) (codeMat 273) o50W_wc
  apply step109wc212_spanCodes_le_of_gens [272, 132, 96, 8, 2, 1]
    (actionW (codeMat 273) (codeMat 273) o50W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 272 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 272 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 272) = codeMat 272 := by
      unfold actionA
      rw [step109wc212s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 272 * (codeMat 273 : Mat3).transpose = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 132 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 132) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 132 * (codeMat 273 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 96) = codeMat 96 := by
      unfold actionA
      rw [step109wc212s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc212s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc212s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o50W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s13Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨13, by omega⟩) 13 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) o50W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ o50W_wc 13
      step109_orbit50_lb13_wc
  exact quotientRankAtLeast_mono step109wc212s13_contain hAct


private theorem step109wc212s14_QtInv :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc212s14_contain :
    (o212SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 158) (codeMat 481) o70W_wc := by
  change spanCodes [274, 132, 86, 54, 10, 1] ≤ actionW (codeMat 158) (codeMat 481) o70W_wc
  apply step109wc212_spanCodes_le_of_gens [274, 132, 86, 54, 10, 1]
    (actionW (codeMat 158) (codeMat 481) o70W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 422 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 422 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 422) = codeMat 274 := by
      unfold actionA
      rw [step109wc212s14_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 422 * (codeMat 185 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 180 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 180) = codeMat 132 := by
      unfold actionA
      rw [step109wc212s14_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 180 * (codeMat 185 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 213 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 213 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 213) = codeMat 86 := by
      unfold actionA
      rw [step109wc212s14_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 213 * (codeMat 185 : Mat3).transpose = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 16) = codeMat 54 := by
      unfold actionA
      rw [step109wc212s14_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 16 * (codeMat 185 : Mat3).transpose = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 96 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc212s14_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 96 * (codeMat 185 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 360 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 360 (by decide)
    have hact : actionA (codeMat 158) (codeMat 481) (codeMat 360) = codeMat 1 := by
      unfold actionA
      rw [step109wc212s14_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 360 * (codeMat 185 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc212_codeMat_mem_actionW_of_witness hw hact

theorem step109wc212s14Dispatch :
    QuotientRankAtLeast (o212SourceU_wc ⟨14, by omega⟩) 13 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 481) o70W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 481) hP hQ o70W_wc 13
      step109_orbit70_lb13_wc
  exact quotientRankAtLeast_mono step109wc212s14_contain hAct

theorem step109wc212_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o212SourceU_wc i) (o212SourceLb_wc i) := by
  fin_cases i
  · exact step109wc212s0Dispatch
  · exact step109wc212s1Dispatch
  · exact step109wc212s2Dispatch
  · exact step109wc212s3Dispatch
  · exact step109wc212s4Dispatch
  · exact step109wc212s5Dispatch
  · exact step109wc212s6Dispatch
  · exact step109wc212s7Dispatch
  · exact step109wc212s8Dispatch
  · exact step109wc212s9Dispatch
  · exact step109wc212s10Dispatch
  · exact step109wc212s11Dispatch
  · exact step109wc212s12Dispatch
  · exact step109wc212s13Dispatch
  · exact step109wc212s14Dispatch

theorem step109_orbit212_lb16_wc : QuotientRankAtLeast o212W_wc 16 :=
  o212Lb16_wc step109wc212_all_dispatch

end QiushiMatmul
