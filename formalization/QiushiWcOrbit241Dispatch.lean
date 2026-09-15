import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit241Consumer
import QiushiStep99Orbit67Dispatch
import QiushiStep99Orbit65Dispatch
import QiushiWcOrbit81Dispatch
import QiushiStep99Orbit77Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit68Dispatch
import QiushiStep99Orbit82Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc241_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc241_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc241s0_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = (codeMat 279 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * (codeMat 279 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s0_contain :
    (o241SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 273) (codeMat 279) o67W := by
  change spanCodes [258, 162, 68, 18, 10, 1] ≤ actionW (codeMat 273) (codeMat 279) o67W
  apply step109wc241_spanCodes_le_of_gens [258, 162, 68, 18, 10, 1]
    (actionW (codeMat 273) (codeMat 279) o67W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 323 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 323) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 323 * (codeMat 279 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 235 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 235 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 235) = codeMat 162 := by
      unfold actionA
      rw [step109wc241s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 235 * (codeMat 279 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 69 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 69) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 69 * (codeMat 279 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 27) = codeMat 18 := by
      unfold actionA
      rw [step109wc241s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 27 * (codeMat 279 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 11 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 11 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 11) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 11 * (codeMat 279 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 1 ∈ o67W :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc241s0_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 279 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s0Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 279) o67W) 15 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 279) hP hQ o67W 15
      step99_orbit67_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc241s0_contain hAct


private theorem step109wc241s1_QtInv :
    (codeMat 226 : Mat3).transpose⁻¹ = (codeMat 141 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 226 : Mat3).transpose * (codeMat 141 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s1_contain :
    (o241SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 99) (codeMat 226) o65W := by
  change spanCodes [256, 160, 68, 17, 8, 2] ≤ actionW (codeMat 99) (codeMat 226) o65W
  apply step109wc241_spanCodes_le_of_gens [256, 160, 68, 17, 8, 2]
    (actionW (codeMat 99) (codeMat 226) o65W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 16 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 16) = codeMat 256 := by
      unfold actionA
      rw [step109wc241s1_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 16 * (codeMat 141 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 170) = codeMat 160 := by
      unfold actionA
      rw [step109wc241s1_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 170 * (codeMat 141 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s1_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 160 * (codeMat 141 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 69 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 69 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 69) = codeMat 17 := by
      unfold actionA
      rw [step109wc241s1_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 69 * (codeMat 141 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 260 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 260) = codeMat 8 := by
      unfold actionA
      rw [step109wc241s1_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 260 * (codeMat 141 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 320 ∈ o65W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 99) (codeMat 226) (codeMat 320) = codeMat 2 := by
      unfold actionA
      rw [step109wc241s1_QtInv]
      show (codeMat 99 : Mat3).transpose * codeMat 320 * (codeMat 141 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s1Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 99 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 226 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 99) (codeMat 226) o65W) 15 :=
    @quotientRankAtLeast_action (codeMat 99) (codeMat 226) hP hQ o65W 15
      step99_orbit65_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc241s1_contain hAct


private theorem step109wc241s2_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = (codeMat 167 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * (codeMat 167 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s2_contain :
    (o241SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 84) (codeMat 167) o81W_wc := by
  change spanCodes [258, 162, 64, 19, 10, 4] ≤ actionW (codeMat 84) (codeMat 167) o81W_wc
  apply step109wc241_spanCodes_le_of_gens [258, 162, 64, 19, 10, 4]
    (actionW (codeMat 84) (codeMat 167) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 323 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 323 (by decide)
    have hact : actionA (codeMat 84) (codeMat 167) (codeMat 323) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 323 * (codeMat 167 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 349 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 84) (codeMat 167) (codeMat 349) = codeMat 162 := by
      unfold actionA
      rw [step109wc241s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 349 * (codeMat 167 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 167) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [step109wc241s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 167 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 84) (codeMat 167) (codeMat 296) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 296 * (codeMat 167 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 84) (codeMat 167) (codeMat 328) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 328 * (codeMat 167 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 84) (codeMat 167) (codeMat 192) = codeMat 4 := by
      unfold actionA
      rw [step109wc241s2_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 192 * (codeMat 167 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s2Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 167) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 167) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc241s2_contain hAct


private theorem step109wc241s3_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = (codeMat 181 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * (codeMat 181 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s3_contain :
    (o241SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 87) (codeMat 423) o81W_wc := by
  change spanCodes [258, 162, 67, 19, 10, 7] ≤ actionW (codeMat 87) (codeMat 423) o81W_wc
  apply step109wc241_spanCodes_le_of_gens [258, 162, 67, 19, 10, 7]
    (actionW (codeMat 87) (codeMat 423) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 191 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 87) (codeMat 423) (codeMat 191) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s3_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 191 * (codeMat 181 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 87) (codeMat 423) (codeMat 21) = codeMat 162 := by
      unfold actionA
      rw [step109wc241s3_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 21 * (codeMat 181 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 329 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 87) (codeMat 423) (codeMat 329) = codeMat 67 := by
      unfold actionA
      rw [step109wc241s3_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 329 * (codeMat 181 : Mat3).transpose = codeMat 67
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 87) (codeMat 423) (codeMat 296) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s3_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 296 * (codeMat 181 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 87) (codeMat 423) (codeMat 328) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s3_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 328 * (codeMat 181 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 87) (codeMat 423) (codeMat 192) = codeMat 7 := by
      unfold actionA
      rw [step109wc241s3_QtInv]
      show (codeMat 87 : Mat3).transpose * codeMat 192 * (codeMat 181 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s3Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 87 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 87) (codeMat 423) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 87) (codeMat 423) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc241s3_contain hAct

private def step109wc241s4SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem step109wc241s4SrcT_lb : QuotientRankAtLeast step109wc241s4SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : step109wc241s4SrcT ≤ transposeW o77W := by
    unfold step109wc241s4SrcT transposeW
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

private theorem step109wc241s4_QtInv :
    (codeMat 461 : Mat3).transpose⁻¹ = (codeMat 234 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 461 : Mat3).transpose * (codeMat 234 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s4_contain :
    (o241SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 172) (codeMat 461) step109wc241s4SrcT := by
  change spanCodes [258, 130, 68, 32, 19, 10] ≤ actionW (codeMat 172) (codeMat 461) step109wc241s4SrcT
  apply step109wc241_spanCodes_le_of_gens [258, 130, 68, 32, 19, 10]
    (actionW (codeMat 172) (codeMat 461) step109wc241s4SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 33 ∈ step109wc241s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 33 (by decide)
    have hact : actionA (codeMat 172) (codeMat 461) (codeMat 33) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s4_QtInv]
      show (codeMat 172 : Mat3).transpose * codeMat 33 * (codeMat 234 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ step109wc241s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 172) (codeMat 461) (codeMat 32) = codeMat 130 := by
      unfold actionA
      rw [step109wc241s4_QtInv]
      show (codeMat 172 : Mat3).transpose * codeMat 32 * (codeMat 234 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 42 ∈ step109wc241s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 42 (by decide)
    have hact : actionA (codeMat 172) (codeMat 461) (codeMat 42) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s4_QtInv]
      show (codeMat 172 : Mat3).transpose * codeMat 42 * (codeMat 234 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 320 ∈ step109wc241s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 320 (by decide)
    have hact : actionA (codeMat 172) (codeMat 461) (codeMat 320) = codeMat 32 := by
      unfold actionA
      rw [step109wc241s4_QtInv]
      show (codeMat 172 : Mat3).transpose * codeMat 320 * (codeMat 234 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 283 ∈ step109wc241s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 172) (codeMat 461) (codeMat 283) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s4_QtInv]
      show (codeMat 172 : Mat3).transpose * codeMat 283 * (codeMat 234 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 484 ∈ step109wc241s4SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 172) (codeMat 461) (codeMat 484) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s4_QtInv]
      show (codeMat 172 : Mat3).transpose * codeMat 484 * (codeMat 234 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s4Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 461 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 172) (codeMat 461) step109wc241s4SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 172) (codeMat 461) hP hQ step109wc241s4SrcT 15
      step109wc241s4SrcT_lb
  exact quotientRankAtLeast_mono step109wc241s4_contain hAct

private def step109wc241s5SrcT : Submodule F2 Mat3 := spanCodes [272, 132, 80, 32, 10, 1]

private theorem step109wc241s5SrcT_lb : QuotientRankAtLeast step109wc241s5SrcT 15 := by
  have ht := quotientRankAtLeast_transpose step99_orbit77_lb15_unconditional
  have hle : step109wc241s5SrcT ≤ transposeW o77W := by
    unfold step109wc241s5SrcT transposeW
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

private theorem step109wc241s5_QtInv :
    (codeMat 489 : Mat3).transpose⁻¹ = (codeMat 241 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 489 : Mat3).transpose * (codeMat 241 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s5_contain :
    (o241SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 183) (codeMat 489) step109wc241s5SrcT := by
  change spanCodes [258, 131, 68, 33, 19, 10] ≤ actionW (codeMat 183) (codeMat 489) step109wc241s5SrcT
  apply step109wc241_spanCodes_le_of_gens [258, 131, 68, 33, 19, 10]
    (actionW (codeMat 183) (codeMat 489) step109wc241s5SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 404 ∈ step109wc241s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 183) (codeMat 489) (codeMat 404) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 404 * (codeMat 241 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 315 ∈ step109wc241s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 315 (by decide)
    have hact : actionA (codeMat 183) (codeMat 489) (codeMat 315) = codeMat 131 := by
      unfold actionA
      rw [step109wc241s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 315 * (codeMat 241 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 462 ∈ step109wc241s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 183) (codeMat 489) (codeMat 462) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 462 * (codeMat 241 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 447 ∈ step109wc241s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 447 (by decide)
    have hact : actionA (codeMat 183) (codeMat 489) (codeMat 447) = codeMat 33 := by
      unfold actionA
      rw [step109wc241s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 447 * (codeMat 241 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 283 ∈ step109wc241s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 283 (by decide)
    have hact : actionA (codeMat 183) (codeMat 489) (codeMat 283) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 283 * (codeMat 241 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 484 ∈ step109wc241s5SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [272, 132, 80, 32, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 183) (codeMat 489) (codeMat 484) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s5_QtInv]
      show (codeMat 183 : Mat3).transpose * codeMat 484 * (codeMat 241 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s5Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 183) (codeMat 489) step109wc241s5SrcT) 15 :=
    @quotientRankAtLeast_action (codeMat 183) (codeMat 489) hP hQ step109wc241s5SrcT 15
      step109wc241s5SrcT_lb
  exact quotientRankAtLeast_mono step109wc241s5_contain hAct


private theorem step109wc241s6_QtInv :
    (codeMat 141 : Mat3).transpose⁻¹ = (codeMat 226 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 141 : Mat3).transpose * (codeMat 226 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s6_contain :
    (o241SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 174) (codeMat 141) o77W := by
  change spanCodes [258, 128, 68, 34, 19, 10] ≤ actionW (codeMat 174) (codeMat 141) o77W
  apply step109wc241_spanCodes_le_of_gens [258, 128, 68, 34, 19, 10]
    (actionW (codeMat 174) (codeMat 141) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 357 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 357 (by decide)
    have hact : actionA (codeMat 174) (codeMat 141) (codeMat 357) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 357 * (codeMat 226 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 260 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 260 (by decide)
    have hact : actionA (codeMat 174) (codeMat 141) (codeMat 260) = codeMat 128 := by
      unfold actionA
      rw [step109wc241s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 260 * (codeMat 226 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 138 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 138 (by decide)
    have hact : actionA (codeMat 174) (codeMat 141) (codeMat 138) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 138 * (codeMat 226 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 356 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 356 (by decide)
    have hact : actionA (codeMat 174) (codeMat 141) (codeMat 356) = codeMat 34 := by
      unfold actionA
      rw [step109wc241s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 356 * (codeMat 226 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 255 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 174) (codeMat 141) (codeMat 255) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 255 * (codeMat 226 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 484 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 174) (codeMat 141) (codeMat 484) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s6_QtInv]
      show (codeMat 174 : Mat3).transpose * codeMat 484 * (codeMat 226 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s6Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 174 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 174) (codeMat 141) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 174) (codeMat 141) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc241s6_contain hAct


private theorem step109wc241s7_QtInv :
    (codeMat 425 : Mat3).transpose⁻¹ = (codeMat 249 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 425 : Mat3).transpose * (codeMat 249 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s7_contain :
    (o241SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 181) (codeMat 425) o77W := by
  change spanCodes [258, 129, 68, 35, 19, 10] ≤ actionW (codeMat 181) (codeMat 425) o77W
  apply step109wc241_spanCodes_le_of_gens [258, 129, 68, 35, 19, 10]
    (actionW (codeMat 181) (codeMat 425) o77W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 148 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 148 (by decide)
    have hact : actionA (codeMat 181) (codeMat 425) (codeMat 148) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s7_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 148 * (codeMat 249 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 507 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 507 (by decide)
    have hact : actionA (codeMat 181) (codeMat 425) (codeMat 507) = codeMat 129 := by
      unfold actionA
      rw [step109wc241s7_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 507 * (codeMat 249 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 181) (codeMat 425) (codeMat 366) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s7_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 366 * (codeMat 249 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 127 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 181) (codeMat 425) (codeMat 127) = codeMat 35 := by
      unfold actionA
      rw [step109wc241s7_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 127 * (codeMat 249 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 255 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 181) (codeMat 425) (codeMat 255) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s7_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 255 * (codeMat 249 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 484 ∈ o77W :=
      spanContainsCodeCore_implies_mem_spanCodes [260, 128, 96, 20, 10, 1] 484 (by decide)
    have hact : actionA (codeMat 181) (codeMat 425) (codeMat 484) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s7_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 484 * (codeMat 249 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s7Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 425 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 181) (codeMat 425) o77W) 15 :=
    @quotientRankAtLeast_action (codeMat 181) (codeMat 425) hP hQ o77W 15
      step99_orbit77_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc241s7_contain hAct


private theorem step109wc241s8_QtInv :
    (codeMat 250 : Mat3).transpose⁻¹ = (codeMat 397 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 250 : Mat3).transpose * (codeMat 397 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s8_contain :
    (o241SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 415) (codeMat 250) o69W := by
  change spanCodes [258, 134, 68, 36, 19, 10] ≤ actionW (codeMat 415) (codeMat 250) o69W
  apply step109wc241_spanCodes_le_of_gens [258, 134, 68, 36, 19, 10]
    (actionW (codeMat 415) (codeMat 250) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 469 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 469 (by decide)
    have hact : actionA (codeMat 415) (codeMat 250) (codeMat 469) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s8_QtInv]
      show (codeMat 415 : Mat3).transpose * codeMat 469 * (codeMat 397 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 378 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 378 (by decide)
    have hact : actionA (codeMat 415) (codeMat 250) (codeMat 378) = codeMat 134 := by
      unfold actionA
      rw [step109wc241s8_QtInv]
      show (codeMat 415 : Mat3).transpose * codeMat 378 * (codeMat 397 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 180 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 180 (by decide)
    have hact : actionA (codeMat 415) (codeMat 250) (codeMat 180) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s8_QtInv]
      show (codeMat 415 : Mat3).transpose * codeMat 180 * (codeMat 397 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 415) (codeMat 250) (codeMat 16) = codeMat 36 := by
      unfold actionA
      rw [step109wc241s8_QtInv]
      show (codeMat 415 : Mat3).transpose * codeMat 16 * (codeMat 397 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 446 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide)
    have hact : actionA (codeMat 415) (codeMat 250) (codeMat 446) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s8_QtInv]
      show (codeMat 415 : Mat3).transpose * codeMat 446 * (codeMat 397 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 113 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide)
    have hact : actionA (codeMat 415) (codeMat 250) (codeMat 113) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s8_QtInv]
      show (codeMat 415 : Mat3).transpose * codeMat 113 * (codeMat 397 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s8Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨8, by omega⟩) 15 := by
  have hP : Invertible (codeMat 415 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 250 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 415) (codeMat 250) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 415) (codeMat 250) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc241s8_contain hAct


private theorem step109wc241s9_QtInv :
    (codeMat 485 : Mat3).transpose⁻¹ = (codeMat 171 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 485 : Mat3).transpose * (codeMat 171 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s9_contain :
    (o241SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 205) (codeMat 485) o81W_wc := by
  change spanCodes [258, 135, 68, 37, 19, 10] ≤ actionW (codeMat 205) (codeMat 485) o81W_wc
  apply step109wc241_spanCodes_le_of_gens [258, 135, 68, 37, 19, 10]
    (actionW (codeMat 205) (codeMat 485) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 31 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 31 (by decide)
    have hact : actionA (codeMat 205) (codeMat 485) (codeMat 31) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s9_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 31 * (codeMat 171 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 20 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 205) (codeMat 485) (codeMat 20) = codeMat 135 := by
      unfold actionA
      rw [step109wc241s9_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 20 * (codeMat 171 : Mat3).transpose = codeMat 135
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 21 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 205) (codeMat 485) (codeMat 21) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s9_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 21 * (codeMat 171 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 488 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 488 (by decide)
    have hact : actionA (codeMat 205) (codeMat 485) (codeMat 488) = codeMat 37 := by
      unfold actionA
      rw [step109wc241s9_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 488 * (codeMat 171 : Mat3).transpose = codeMat 37
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 205) (codeMat 485) (codeMat 296) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s9_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 296 * (codeMat 171 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 205) (codeMat 485) (codeMat 328) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s9_QtInv]
      show (codeMat 205 : Mat3).transpose * codeMat 328 * (codeMat 171 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s9Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨9, by omega⟩) 15 := by
  have hP : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 485 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 205) (codeMat 485) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 205) (codeMat 485) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc241s9_contain hAct


private theorem step109wc241s10_QtInv :
    (codeMat 254 : Mat3).transpose⁻¹ = (codeMat 443 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 254 : Mat3).transpose * (codeMat 443 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s10_contain :
    (o241SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 348) (codeMat 254) o69W := by
  change spanCodes [258, 132, 68, 38, 19, 10] ≤ actionW (codeMat 348) (codeMat 254) o69W
  apply step109wc241_spanCodes_le_of_gens [258, 132, 68, 38, 19, 10]
    (actionW (codeMat 348) (codeMat 254) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 452 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 452 (by decide)
    have hact : actionA (codeMat 348) (codeMat 254) (codeMat 452) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s10_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 452 * (codeMat 443 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 196 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 196 (by decide)
    have hact : actionA (codeMat 348) (codeMat 254) (codeMat 196) = codeMat 132 := by
      unfold actionA
      rw [step109wc241s10_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 196 * (codeMat 443 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 197 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 197 (by decide)
    have hact : actionA (codeMat 348) (codeMat 254) (codeMat 197) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s10_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 197 * (codeMat 443 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 479 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 479 (by decide)
    have hact : actionA (codeMat 348) (codeMat 254) (codeMat 479) = codeMat 38 := by
      unfold actionA
      rw [step109wc241s10_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 479 * (codeMat 443 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 446 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 446 (by decide)
    have hact : actionA (codeMat 348) (codeMat 254) (codeMat 446) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s10_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 446 * (codeMat 443 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 113 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 113 (by decide)
    have hact : actionA (codeMat 348) (codeMat 254) (codeMat 113) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s10_QtInv]
      show (codeMat 348 : Mat3).transpose * codeMat 113 * (codeMat 443 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s10Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨10, by omega⟩) 15 := by
  have hP : Invertible (codeMat 348 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 254 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 348) (codeMat 254) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 348) (codeMat 254) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc241s10_contain hAct


private theorem step109wc241s11_QtInv :
    (codeMat 481 : Mat3).transpose⁻¹ = (codeMat 185 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 481 : Mat3).transpose * (codeMat 185 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s11_contain :
    (o241SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 206) (codeMat 481) o81W_wc := by
  change spanCodes [258, 133, 68, 39, 19, 10] ≤ actionW (codeMat 206) (codeMat 481) o81W_wc
  apply step109wc241_spanCodes_le_of_gens [258, 133, 68, 39, 19, 10]
    (actionW (codeMat 206) (codeMat 481) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 406 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 406 (by decide)
    have hact : actionA (codeMat 206) (codeMat 481) (codeMat 406) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s11_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 406 * (codeMat 185 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 316 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 316 (by decide)
    have hact : actionA (codeMat 206) (codeMat 481) (codeMat 316) = codeMat 133 := by
      unfold actionA
      rw [step109wc241s11_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 316 * (codeMat 185 : Mat3).transpose = codeMat 133
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 349 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 206) (codeMat 481) (codeMat 349) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s11_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 349 * (codeMat 185 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 392 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 392 (by decide)
    have hact : actionA (codeMat 206) (codeMat 481) (codeMat 392) = codeMat 39 := by
      unfold actionA
      rw [step109wc241s11_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 392 * (codeMat 185 : Mat3).transpose = codeMat 39
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 206) (codeMat 481) (codeMat 296) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s11_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 296 * (codeMat 185 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 206) (codeMat 481) (codeMat 328) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s11_QtInv]
      show (codeMat 206 : Mat3).transpose * codeMat 328 * (codeMat 185 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s11Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨11, by omega⟩) 15 := by
  have hP : Invertible (codeMat 206 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 481 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 206) (codeMat 481) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 206) (codeMat 481) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc241s11_contain hAct


private theorem step109wc241s12_QtInv :
    (codeMat 270 : Mat3).transpose⁻¹ = (codeMat 298 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 270 : Mat3).transpose * (codeMat 298 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s12_contain :
    (o241SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 346) (codeMat 270) o68W := by
  change spanCodes [257, 161, 68, 16, 9, 3] ≤ actionW (codeMat 346) (codeMat 270) o68W
  apply step109wc241_spanCodes_le_of_gens [257, 161, 68, 16, 9, 3]
    (actionW (codeMat 346) (codeMat 270) o68W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 383 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 383 (by decide)
    have hact : actionA (codeMat 346) (codeMat 270) (codeMat 383) = codeMat 257 := by
      unfold actionA
      rw [step109wc241s12_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 383 * (codeMat 298 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 94 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 94 (by decide)
    have hact : actionA (codeMat 346) (codeMat 270) (codeMat 94) = codeMat 161 := by
      unfold actionA
      rw [step109wc241s12_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 94 * (codeMat 298 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 191 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 346) (codeMat 270) (codeMat 191) = codeMat 68 := by
      unfold actionA
      rw [step109wc241s12_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 191 * (codeMat 298 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 346) (codeMat 270) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [step109wc241s12_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 1 * (codeMat 298 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 346) (codeMat 270) (codeMat 16) = codeMat 9 := by
      unfold actionA
      rw [step109wc241s12_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 16 * (codeMat 298 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 27 ∈ o68W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 346) (codeMat 270) (codeMat 27) = codeMat 3 := by
      unfold actionA
      rw [step109wc241s12_QtInv]
      show (codeMat 346 : Mat3).transpose * codeMat 27 * (codeMat 298 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s12Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 346 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 270 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 346) (codeMat 270) o68W) 14 :=
    @quotientRankAtLeast_action (codeMat 346) (codeMat 270) hP hQ o68W 14
      step99_orbit68_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc241s12_contain hAct


private theorem step109wc241s13_QtInv :
    (codeMat 372 : Mat3).transpose⁻¹ = (codeMat 93 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 372 : Mat3).transpose * (codeMat 93 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s13_contain :
    (o241SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 86) (codeMat 372) o82W := by
  change spanCodes [258, 162, 65, 19, 10, 5] ≤ actionW (codeMat 86) (codeMat 372) o82W
  apply step109wc241_spanCodes_le_of_gens [258, 162, 65, 19, 10, 5]
    (actionW (codeMat 86) (codeMat 372) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 191 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 191 (by decide)
    have hact : actionA (codeMat 86) (codeMat 372) (codeMat 191) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s13_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 191 * (codeMat 93 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 170 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 170 (by decide)
    have hact : actionA (codeMat 86) (codeMat 372) (codeMat 170) = codeMat 162 := by
      unfold actionA
      rw [step109wc241s13_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 170 * (codeMat 93 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 86) (codeMat 372) (codeMat 292) = codeMat 65 := by
      unfold actionA
      rw [step109wc241s13_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 292 * (codeMat 93 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 400 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 86) (codeMat 372) (codeMat 400) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s13_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 400 * (codeMat 93 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 86) (codeMat 372) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s13_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 160 * (codeMat 93 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 86) (codeMat 372) (codeMat 192) = codeMat 5 := by
      unfold actionA
      rw [step109wc241s13_QtInv]
      show (codeMat 86 : Mat3).transpose * codeMat 192 * (codeMat 93 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s13Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 86 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 372 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 86) (codeMat 372) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 86) (codeMat 372) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc241s13_contain hAct


private theorem step109wc241s14_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc241s14_contain :
    (o241SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 85) (codeMat 84) o82W := by
  change spanCodes [258, 162, 66, 19, 10, 6] ≤ actionW (codeMat 85) (codeMat 84) o82W
  apply step109wc241_spanCodes_le_of_gens [258, 162, 66, 19, 10, 6]
    (actionW (codeMat 85) (codeMat 84) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 193 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 193 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 193) = codeMat 258 := by
      unfold actionA
      rw [step109wc241s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 193 * (codeMat 84 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 10) = codeMat 162 := by
      unfold actionA
      rw [step109wc241s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 10 * (codeMat 84 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 388 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 388 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 388) = codeMat 66 := by
      unfold actionA
      rw [step109wc241s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 388 * (codeMat 84 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 400 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 400) = codeMat 19 := by
      unfold actionA
      rw [step109wc241s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 400 * (codeMat 84 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc241s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 192) = codeMat 6 := by
      unfold actionA
      rw [step109wc241s14_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 192 * (codeMat 84 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc241_codeMat_mem_actionW_of_witness hw hact

theorem step109wc241s14Dispatch :
    QuotientRankAtLeast (o241SourceU_wc ⟨14, by omega⟩) 14 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 84) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 84) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc241s14_contain hAct

theorem step109wc241_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o241SourceU_wc i) (o241SourceLb_wc i) := by
  fin_cases i
  · exact step109wc241s0Dispatch
  · exact step109wc241s1Dispatch
  · exact step109wc241s2Dispatch
  · exact step109wc241s3Dispatch
  · exact step109wc241s4Dispatch
  · exact step109wc241s5Dispatch
  · exact step109wc241s6Dispatch
  · exact step109wc241s7Dispatch
  · exact step109wc241s8Dispatch
  · exact step109wc241s9Dispatch
  · exact step109wc241s10Dispatch
  · exact step109wc241s11Dispatch
  · exact step109wc241s12Dispatch
  · exact step109wc241s13Dispatch
  · exact step109wc241s14Dispatch

theorem step109_orbit241_lb16_wc : QuotientRankAtLeast o241W_wc 16 :=
  o241Lb16_wc step109wc241_all_dispatch

end QiushiMatmul
