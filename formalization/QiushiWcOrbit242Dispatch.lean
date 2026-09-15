import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiWcOrbit242Consumer
import QiushiWcOrbit64Dispatch
import QiushiStep99Orbit69Dispatch
import QiushiStep99Orbit76Dispatch
import QiushiWcOrbit81Dispatch
import QiushiWcOrbit84Dispatch
import QiushiStep99Orbit82Dispatch
import QiushiWcOrbit70Dispatch

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc242_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc242_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc242s0_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = (codeMat 267 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * (codeMat 267 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s0_contain :
    (o242SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 266) (codeMat 282) o64W_wc := by
  change spanCodes [258, 164, 68, 18, 10, 1] ≤ actionW (codeMat 266) (codeMat 282) o64W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 164, 68, 18, 10, 1]
    (actionW (codeMat 266) (codeMat 282) o64W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 280 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 280 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 280) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 280 * (codeMat 267 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 228 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 228) = codeMat 164 := by
      unfold actionA
      rw [step109wc242s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 228 * (codeMat 267 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 160 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 160) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 160 * (codeMat 267 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 27) = codeMat 18 := by
      unfold actionA
      rw [step109wc242s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 27 * (codeMat 267 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 26 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 26 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 26) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 26 * (codeMat 267 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o64W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [step109wc242s0_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 267 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s0Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨0, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 282) o64W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 282) hP hQ o64W_wc 15
      step109_orbit64_lb15_wc
  exact quotientRankAtLeast_mono step109wc242s0_contain hAct


private theorem step109wc242s1_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s1_contain :
    (o242SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 266) (codeMat 273) o69W := by
  change spanCodes [256, 164, 68, 17, 8, 2] ≤ actionW (codeMat 266) (codeMat 273) o69W
  apply step109wc242_spanCodes_le_of_gens [256, 164, 68, 17, 8, 2]
    (actionW (codeMat 266) (codeMat 273) o69W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 256 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 256) = codeMat 256 := by
      unfold actionA
      rw [step109wc242s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 164 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 164 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 164) = codeMat 164 := by
      unfold actionA
      rw [step109wc242s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 164 * (codeMat 273 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 96) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 96 * (codeMat 273 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 10 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 10) = codeMat 17 := by
      unfold actionA
      rw [step109wc242s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 10 * (codeMat 273 : Mat3).transpose = codeMat 17
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [step109wc242s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o69W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 273) (codeMat 16) = codeMat 2 := by
      unfold actionA
      rw [step109wc242s1_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s1Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨1, by omega⟩) 15 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 273) o69W) 15 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 273) hP hQ o69W 15
      step99_orbit69_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc242s1_contain hAct


private theorem step109wc242s2_QtInv :
    (codeMat 370 : Mat3).transpose⁻¹ = (codeMat 207 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 370 : Mat3).transpose * (codeMat 207 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s2_contain :
    (o242SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 111) (codeMat 370) o76W := by
  change spanCodes [258, 160, 64, 19, 10, 4] ≤ actionW (codeMat 111) (codeMat 370) o76W
  apply step109wc242_spanCodes_le_of_gens [258, 160, 64, 19, 10, 4]
    (actionW (codeMat 111) (codeMat 370) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 368 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 368 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 368) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 368 * (codeMat 207 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 238 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 238 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 238) = codeMat 160 := by
      unfold actionA
      rw [step109wc242s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 238 * (codeMat 207 : Mat3).transpose = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 288) = codeMat 64 := by
      unfold actionA
      rw [step109wc242s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 288 * (codeMat 207 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 475 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 475) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 475 * (codeMat 207 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 228) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 228 * (codeMat 207 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 111) (codeMat 370) (codeMat 384) = codeMat 4 := by
      unfold actionA
      rw [step109wc242s2_QtInv]
      show (codeMat 111 : Mat3).transpose * codeMat 384 * (codeMat 207 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s2Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨2, by omega⟩) 15 := by
  have hP : Invertible (codeMat 111 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 370 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 111) (codeMat 370) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 111) (codeMat 370) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc242s2_contain hAct


private theorem step109wc242s3_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = (codeMat 177 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * (codeMat 177 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s3_contain :
    (o242SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 95) (codeMat 417) o81W_wc := by
  change spanCodes [258, 163, 67, 19, 10, 7] ≤ actionW (codeMat 95) (codeMat 417) o81W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 163, 67, 19, 10, 7]
    (actionW (codeMat 95) (codeMat 417) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 310 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 310 (by decide)
    have hact : actionA (codeMat 95) (codeMat 417) (codeMat 310) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 310 * (codeMat 177 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 212 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 212 (by decide)
    have hact : actionA (codeMat 95) (codeMat 417) (codeMat 212) = codeMat 163 := by
      unfold actionA
      rw [step109wc242s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 212 * (codeMat 177 : Mat3).transpose = codeMat 163
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 329 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 329 (by decide)
    have hact : actionA (codeMat 95) (codeMat 417) (codeMat 329) = codeMat 67 := by
      unfold actionA
      rw [step109wc242s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 329 * (codeMat 177 : Mat3).transpose = codeMat 67
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 95) (codeMat 417) (codeMat 96) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 96 * (codeMat 177 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 95) (codeMat 417) (codeMat 328) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 328 * (codeMat 177 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 95) (codeMat 417) (codeMat 192) = codeMat 7 := by
      unfold actionA
      rw [step109wc242s3_QtInv]
      show (codeMat 95 : Mat3).transpose * codeMat 192 * (codeMat 177 : Mat3).transpose = codeMat 7
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s3Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨3, by omega⟩) 15 := by
  have hP : Invertible (codeMat 95 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 95) (codeMat 417) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 95) (codeMat 417) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc242s3_contain hAct


private theorem step109wc242s4_QtInv :
    (codeMat 443 : Mat3).transpose⁻¹ = (codeMat 254 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 443 : Mat3).transpose * (codeMat 254 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s4_contain :
    (o242SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 181) (codeMat 443) o76W := by
  change spanCodes [258, 132, 68, 32, 19, 10] ≤ actionW (codeMat 181) (codeMat 443) o76W
  apply step109wc242_spanCodes_le_of_gens [258, 132, 68, 32, 19, 10]
    (actionW (codeMat 181) (codeMat 443) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 79 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 79 (by decide)
    have hact : actionA (codeMat 181) (codeMat 443) (codeMat 79) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s4_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 79 * (codeMat 254 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 78 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 78 (by decide)
    have hact : actionA (codeMat 181) (codeMat 443) (codeMat 78) = codeMat 132 := by
      unfold actionA
      rw [step109wc242s4_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 78 * (codeMat 254 : Mat3).transpose = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 366 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 366 (by decide)
    have hact : actionA (codeMat 181) (codeMat 443) (codeMat 366) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s4_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 366 * (codeMat 254 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 181) (codeMat 443) (codeMat 384) = codeMat 32 := by
      unfold actionA
      rw [step109wc242s4_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 384 * (codeMat 254 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 228 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 228 (by decide)
    have hact : actionA (codeMat 181) (codeMat 443) (codeMat 228) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s4_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 228 * (codeMat 254 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 181) (codeMat 443) (codeMat 319) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s4_QtInv]
      show (codeMat 181 : Mat3).transpose * codeMat 319 * (codeMat 254 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s4Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨4, by omega⟩) 15 := by
  have hP : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 443 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 181) (codeMat 443) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 181) (codeMat 443) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc242s4_contain hAct


private theorem step109wc242s5_QtInv :
    (codeMat 482 : Mat3).transpose⁻¹ = (codeMat 143 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 482 : Mat3).transpose * (codeMat 143 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s5_contain :
    (o242SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 141) (codeMat 482) o81W_wc := by
  change spanCodes [258, 135, 68, 35, 19, 10] ≤ actionW (codeMat 141) (codeMat 482) o81W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 135, 68, 35, 19, 10]
    (actionW (codeMat 141) (codeMat 482) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 30 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 30 (by decide)
    have hact : actionA (codeMat 141) (codeMat 482) (codeMat 30) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s5_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 30 * (codeMat 143 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 21 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 141) (codeMat 482) (codeMat 21) = codeMat 135 := by
      unfold actionA
      rw [step109wc242s5_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 21 * (codeMat 143 : Mat3).transpose = codeMat 135
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 20 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 20 (by decide)
    have hact : actionA (codeMat 141) (codeMat 482) (codeMat 20) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s5_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 20 * (codeMat 143 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 392 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 392 (by decide)
    have hact : actionA (codeMat 141) (codeMat 482) (codeMat 392) = codeMat 35 := by
      unfold actionA
      rw [step109wc242s5_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 392 * (codeMat 143 : Mat3).transpose = codeMat 35
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 328 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 328 (by decide)
    have hact : actionA (codeMat 141) (codeMat 482) (codeMat 328) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s5_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 328 * (codeMat 143 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 141) (codeMat 482) (codeMat 296) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s5_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 296 * (codeMat 143 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s5Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨5, by omega⟩) 15 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 482 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 482) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 482) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc242s5_contain hAct


private theorem step109wc242s6_QtInv :
    (codeMat 489 : Mat3).transpose⁻¹ = (codeMat 241 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 489 : Mat3).transpose * (codeMat 241 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s6_contain :
    (o242SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 254) (codeMat 489) o76W := by
  change spanCodes [258, 128, 68, 36, 19, 10] ≤ actionW (codeMat 254) (codeMat 489) o76W
  apply step109wc242_spanCodes_le_of_gens [258, 128, 68, 36, 19, 10]
    (actionW (codeMat 254) (codeMat 489) o76W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 404 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 404 (by decide)
    have hact : actionA (codeMat 254) (codeMat 489) (codeMat 404) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s6_QtInv]
      show (codeMat 254 : Mat3).transpose * codeMat 404 * (codeMat 241 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 288 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 288 (by decide)
    have hact : actionA (codeMat 254) (codeMat 489) (codeMat 288) = codeMat 128 := by
      unfold actionA
      rw [step109wc242s6_QtInv]
      show (codeMat 254 : Mat3).transpose * codeMat 288 * (codeMat 241 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 462 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 462 (by decide)
    have hact : actionA (codeMat 254) (codeMat 489) (codeMat 462) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s6_QtInv]
      show (codeMat 254 : Mat3).transpose * codeMat 462 * (codeMat 241 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 384 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 384 (by decide)
    have hact : actionA (codeMat 254) (codeMat 489) (codeMat 384) = codeMat 36 := by
      unfold actionA
      rw [step109wc242s6_QtInv]
      show (codeMat 254 : Mat3).transpose * codeMat 384 * (codeMat 241 : Mat3).transpose = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 319 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 319 (by decide)
    have hact : actionA (codeMat 254) (codeMat 489) (codeMat 319) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s6_QtInv]
      show (codeMat 254 : Mat3).transpose * codeMat 319 * (codeMat 241 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 475 ∈ o76W :=
      spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] 475 (by decide)
    have hact : actionA (codeMat 254) (codeMat 489) (codeMat 475) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s6_QtInv]
      show (codeMat 254 : Mat3).transpose * codeMat 475 * (codeMat 241 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s6Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨6, by omega⟩) 15 := by
  have hP : Invertible (codeMat 254 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 489 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 254) (codeMat 489) o76W) 15 :=
    @quotientRankAtLeast_action (codeMat 254) (codeMat 489) hP hQ o76W 15
      step99_orbit76_lb15_unconditional
  exact quotientRankAtLeast_mono step109wc242s6_contain hAct


private theorem step109wc242s7_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s7_contain :
    (o242SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 214) (codeMat 355) o81W_wc := by
  change spanCodes [258, 131, 68, 39, 19, 10] ≤ actionW (codeMat 214) (codeMat 355) o81W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 131, 68, 39, 19, 10]
    (actionW (codeMat 214) (codeMat 355) o81W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 126 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 126) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s7_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 126 * (codeMat 190 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 297 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 297 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 297) = codeMat 131 := by
      unfold actionA
      rw [step109wc242s7_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 297 * (codeMat 190 : Mat3).transpose = codeMat 131
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 413 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 413 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 413) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s7_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 413 * (codeMat 190 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 160 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 160) = codeMat 39 := by
      unfold actionA
      rw [step109wc242s7_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 160 * (codeMat 190 : Mat3).transpose = codeMat 39
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 296 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 296 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 296) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s7_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 296 * (codeMat 190 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 96 ∈ o81W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [290, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 214) (codeMat 355) (codeMat 96) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s7_QtInv]
      show (codeMat 214 : Mat3).transpose * codeMat 96 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s7Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨7, by omega⟩) 15 := by
  have hP : Invertible (codeMat 214 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 214) (codeMat 355) o81W_wc) 15 :=
    @quotientRankAtLeast_action (codeMat 214) (codeMat 355) hP hQ o81W_wc 15
      step109_orbit81_lb15_wc
  exact quotientRankAtLeast_mono step109wc242s7_contain hAct


private theorem step109wc242s8_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = (codeMat 419 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * (codeMat 419 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s8_contain :
    (o242SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 117) (codeMat 183) o84W_wc := by
  change spanCodes [258, 161, 65, 19, 10, 5] ≤ actionW (codeMat 117) (codeMat 183) o84W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 161, 65, 19, 10, 5]
    (actionW (codeMat 117) (codeMat 183) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 259 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 259 (by decide)
    have hact : actionA (codeMat 117) (codeMat 183) (codeMat 259) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s8_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 259 * (codeMat 419 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 348 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 348 (by decide)
    have hact : actionA (codeMat 117) (codeMat 183) (codeMat 348) = codeMat 161 := by
      unfold actionA
      rw [step109wc242s8_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 348 * (codeMat 419 : Mat3).transpose = codeMat 161
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 117) (codeMat 183) (codeMat 1) = codeMat 65 := by
      unfold actionA
      rw [step109wc242s8_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 1 * (codeMat 419 : Mat3).transpose = codeMat 65
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 127 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 117) (codeMat 183) (codeMat 127) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s8_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 127 * (codeMat 419 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 393 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 393 (by decide)
    have hact : actionA (codeMat 117) (codeMat 183) (codeMat 393) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s8_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 393 * (codeMat 419 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 117) (codeMat 183) (codeMat 128) = codeMat 5 := by
      unfold actionA
      rw [step109wc242s8_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 128 * (codeMat 419 : Mat3).transpose = codeMat 5
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s8Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨8, by omega⟩) 14 := by
  have hP : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 117) (codeMat 183) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 117) (codeMat 183) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc242s8_contain hAct


private theorem step109wc242s9_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s9_contain :
    (o242SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 85) (codeMat 84) o82W := by
  change spanCodes [258, 162, 66, 19, 10, 6] ≤ actionW (codeMat 85) (codeMat 84) o82W
  apply step109wc242_spanCodes_le_of_gens [258, 162, 66, 19, 10, 6]
    (actionW (codeMat 85) (codeMat 84) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 193 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 193 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 193) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s9_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 193 * (codeMat 84 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 10 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 10 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 10) = codeMat 162 := by
      unfold actionA
      rw [step109wc242s9_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 10 * (codeMat 84 : Mat3).transpose = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 388 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 388 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 388) = codeMat 66 := by
      unfold actionA
      rw [step109wc242s9_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 388 * (codeMat 84 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 400 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 400) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s9_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 400 * (codeMat 84 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s9_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 192 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 192 (by decide)
    have hact : actionA (codeMat 85) (codeMat 84) (codeMat 192) = codeMat 6 := by
      unfold actionA
      rw [step109wc242s9_QtInv]
      show (codeMat 85 : Mat3).transpose * codeMat 192 * (codeMat 84 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s9Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨9, by omega⟩) 14 := by
  have hP : Invertible (codeMat 85 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 85) (codeMat 84) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 85) (codeMat 84) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc242s9_contain hAct


private theorem step109wc242s10_QtInv :
    (codeMat 253 : Mat3).transpose⁻¹ = (codeMat 415 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 253 : Mat3).transpose * (codeMat 415 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s10_contain :
    (o242SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 190) (codeMat 253) o84W_wc := by
  change spanCodes [258, 133, 68, 33, 19, 10] ≤ actionW (codeMat 190) (codeMat 253) o84W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 133, 68, 33, 19, 10]
    (actionW (codeMat 190) (codeMat 253) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 245 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 190) (codeMat 253) (codeMat 245) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s10_QtInv]
      show (codeMat 190 : Mat3).transpose * codeMat 245 * (codeMat 415 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 418 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 418 (by decide)
    have hact : actionA (codeMat 190) (codeMat 253) (codeMat 418) = codeMat 133 := by
      unfold actionA
      rw [step109wc242s10_QtInv]
      show (codeMat 190 : Mat3).transpose * codeMat 418 * (codeMat 415 : Mat3).transpose = codeMat 133
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 476 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 476 (by decide)
    have hact : actionA (codeMat 190) (codeMat 253) (codeMat 476) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s10_QtInv]
      show (codeMat 190 : Mat3).transpose * codeMat 476 * (codeMat 415 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 255 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 255 (by decide)
    have hact : actionA (codeMat 190) (codeMat 253) (codeMat 255) = codeMat 33 := by
      unfold actionA
      rw [step109wc242s10_QtInv]
      show (codeMat 190 : Mat3).transpose * codeMat 255 * (codeMat 415 : Mat3).transpose = codeMat 33
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 393 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 393 (by decide)
    have hact : actionA (codeMat 190) (codeMat 253) (codeMat 393) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s10_QtInv]
      show (codeMat 190 : Mat3).transpose * codeMat 393 * (codeMat 415 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 502 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 190) (codeMat 253) (codeMat 502) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s10_QtInv]
      show (codeMat 190 : Mat3).transpose * codeMat 502 * (codeMat 415 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s10Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨10, by omega⟩) 14 := by
  have hP : Invertible (codeMat 190 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 253 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 190) (codeMat 253) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 190) (codeMat 253) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc242s10_contain hAct


private theorem step109wc242s11_QtInv :
    (codeMat 156 : Mat3).transpose⁻¹ = (codeMat 102 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 156 : Mat3).transpose * (codeMat 102 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s11_contain :
    (o242SourceU_wc ⟨11, by omega⟩) ≤ actionW (codeMat 158) (codeMat 156) o82W := by
  change spanCodes [258, 134, 68, 34, 19, 10] ≤ actionW (codeMat 158) (codeMat 156) o82W
  apply step109wc242_spanCodes_le_of_gens [258, 134, 68, 34, 19, 10]
    (actionW (codeMat 158) (codeMat 156) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 497 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 497 (by decide)
    have hact : actionA (codeMat 158) (codeMat 156) (codeMat 497) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s11_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 497 * (codeMat 102 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 126 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 126 (by decide)
    have hact : actionA (codeMat 158) (codeMat 156) (codeMat 126) = codeMat 134 := by
      unfold actionA
      rw [step109wc242s11_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 126 * (codeMat 102 : Mat3).transpose = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 202 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 202 (by decide)
    have hact : actionA (codeMat 158) (codeMat 156) (codeMat 202) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s11_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 202 * (codeMat 102 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 496 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 496 (by decide)
    have hact : actionA (codeMat 158) (codeMat 156) (codeMat 496) = codeMat 34 := by
      unfold actionA
      rw [step109wc242s11_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 496 * (codeMat 102 : Mat3).transpose = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 160 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 160 (by decide)
    have hact : actionA (codeMat 158) (codeMat 156) (codeMat 160) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s11_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 160 * (codeMat 102 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 304 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 304 (by decide)
    have hact : actionA (codeMat 158) (codeMat 156) (codeMat 304) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s11_QtInv]
      show (codeMat 158 : Mat3).transpose * codeMat 304 * (codeMat 102 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s11Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨11, by omega⟩) 14 := by
  have hP : Invertible (codeMat 158 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 156 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 158) (codeMat 156) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 158) (codeMat 156) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc242s11_contain hAct


private theorem step109wc242s12_QtInv :
    (codeMat 110 : Mat3).transpose⁻¹ = (codeMat 444 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 110 : Mat3).transpose * (codeMat 444 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s12_contain :
    (o242SourceU_wc ⟨12, by omega⟩) ≤ actionW (codeMat 239) (codeMat 110) o84W_wc := by
  change spanCodes [258, 129, 68, 37, 19, 10] ≤ actionW (codeMat 239) (codeMat 110) o84W_wc
  apply step109wc242_spanCodes_le_of_gens [258, 129, 68, 37, 19, 10]
    (actionW (codeMat 239) (codeMat 110) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 138 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 138 (by decide)
    have hact : actionA (codeMat 239) (codeMat 110) (codeMat 138) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s12_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 138 * (codeMat 444 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 503 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 503 (by decide)
    have hact : actionA (codeMat 239) (codeMat 110) (codeMat 503) = codeMat 129 := by
      unfold actionA
      rw [step109wc242s12_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 503 * (codeMat 444 : Mat3).transpose = codeMat 129
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 349 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 349 (by decide)
    have hact : actionA (codeMat 239) (codeMat 110) (codeMat 349) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s12_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 349 * (codeMat 444 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 374 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 374 (by decide)
    have hact : actionA (codeMat 239) (codeMat 110) (codeMat 374) = codeMat 37 := by
      unfold actionA
      rw [step109wc242s12_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 374 * (codeMat 444 : Mat3).transpose = codeMat 37
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 502 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 502 (by decide)
    have hact : actionA (codeMat 239) (codeMat 110) (codeMat 502) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s12_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 502 * (codeMat 444 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 127 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 127 (by decide)
    have hact : actionA (codeMat 239) (codeMat 110) (codeMat 127) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s12_QtInv]
      show (codeMat 239 : Mat3).transpose * codeMat 127 * (codeMat 444 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s12Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨12, by omega⟩) 14 := by
  have hP : Invertible (codeMat 239 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 110 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 239) (codeMat 110) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 239) (codeMat 110) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc242s12_contain hAct


private theorem step109wc242s13_QtInv :
    (codeMat 204 : Mat3).transpose⁻¹ = (codeMat 114 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 204 : Mat3).transpose * (codeMat 114 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s13_contain :
    (o242SourceU_wc ⟨13, by omega⟩) ≤ actionW (codeMat 207) (codeMat 204) o82W := by
  change spanCodes [258, 130, 68, 38, 19, 10] ≤ actionW (codeMat 207) (codeMat 204) o82W
  apply step109wc242_spanCodes_le_of_gens [258, 130, 68, 38, 19, 10]
    (actionW (codeMat 207) (codeMat 204) o82W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 97 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 97 (by decide)
    have hact : actionA (codeMat 207) (codeMat 204) (codeMat 97) = codeMat 258 := by
      unfold actionA
      rw [step109wc242s13_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 97 * (codeMat 114 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 292 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 292 (by decide)
    have hact : actionA (codeMat 207) (codeMat 204) (codeMat 292) = codeMat 130 := by
      unfold actionA
      rw [step109wc242s13_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 292 * (codeMat 114 : Mat3).transpose = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 398 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 398 (by decide)
    have hact : actionA (codeMat 207) (codeMat 204) (codeMat 398) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s13_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 398 * (codeMat 114 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 96 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 207) (codeMat 204) (codeMat 96) = codeMat 38 := by
      unfold actionA
      rw [step109wc242s13_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 96 * (codeMat 114 : Mat3).transpose = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 304 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 304 (by decide)
    have hact : actionA (codeMat 207) (codeMat 204) (codeMat 304) = codeMat 19 := by
      unfold actionA
      rw [step109wc242s13_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 304 * (codeMat 114 : Mat3).transpose = codeMat 19
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 400 ∈ o82W :=
      spanContainsCodeCore_implies_mem_spanCodes [292, 160, 96, 20, 10, 1] 400 (by decide)
    have hact : actionA (codeMat 207) (codeMat 204) (codeMat 400) = codeMat 10 := by
      unfold actionA
      rw [step109wc242s13_QtInv]
      show (codeMat 207 : Mat3).transpose * codeMat 400 * (codeMat 114 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s13Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨13, by omega⟩) 14 := by
  have hP : Invertible (codeMat 207 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 204 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 207) (codeMat 204) o82W) 14 :=
    @quotientRankAtLeast_action (codeMat 207) (codeMat 204) hP hQ o82W 14
      step99_orbit82_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc242s13_contain hAct


private theorem step109wc242s14_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = (codeMat 275 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * (codeMat 275 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc242s14_contain :
    (o242SourceU_wc ⟨14, by omega⟩) ≤ actionW (codeMat 267) (codeMat 275) o70W_wc := by
  change spanCodes [257, 164, 68, 16, 9, 3] ≤ actionW (codeMat 267) (codeMat 275) o70W_wc
  apply step109wc242_spanCodes_le_of_gens [257, 164, 68, 16, 9, 3]
    (actionW (codeMat 267) (codeMat 275) o70W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 264 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 267) (codeMat 275) (codeMat 264) = codeMat 257 := by
      unfold actionA
      rw [step109wc242s14_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 264 * (codeMat 275 : Mat3).transpose = codeMat 257
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 196 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 196 (by decide)
    have hact : actionA (codeMat 267) (codeMat 275) (codeMat 196) = codeMat 164 := by
      unfold actionA
      rw [step109wc242s14_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 196 * (codeMat 275 : Mat3).transpose = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 96 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 96 (by decide)
    have hact : actionA (codeMat 267) (codeMat 275) (codeMat 96) = codeMat 68 := by
      unfold actionA
      rw [step109wc242s14_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 96 * (codeMat 275 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 27 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 27 (by decide)
    have hact : actionA (codeMat 267) (codeMat 275) (codeMat 27) = codeMat 16 := by
      unfold actionA
      rw [step109wc242s14_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 27 * (codeMat 275 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 1 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 267) (codeMat 275) (codeMat 1) = codeMat 9 := by
      unfold actionA
      rw [step109wc242s14_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 1 * (codeMat 275 : Mat3).transpose = codeMat 9
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 16 ∈ o70W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 164, 96, 16, 10, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 275) (codeMat 16) = codeMat 3 := by
      unfold actionA
      rw [step109wc242s14_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * (codeMat 275 : Mat3).transpose = codeMat 3
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc242_codeMat_mem_actionW_of_witness hw hact

theorem step109wc242s14Dispatch :
    QuotientRankAtLeast (o242SourceU_wc ⟨14, by omega⟩) 13 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 275) o70W_wc) 13 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 275) hP hQ o70W_wc 13
      step109_orbit70_lb13_wc
  exact quotientRankAtLeast_mono step109wc242s14_contain hAct

theorem step109wc242_all_dispatch (i : Fin 15) :
    QuotientRankAtLeast (o242SourceU_wc i) (o242SourceLb_wc i) := by
  fin_cases i
  · exact step109wc242s0Dispatch
  · exact step109wc242s1Dispatch
  · exact step109wc242s2Dispatch
  · exact step109wc242s3Dispatch
  · exact step109wc242s4Dispatch
  · exact step109wc242s5Dispatch
  · exact step109wc242s6Dispatch
  · exact step109wc242s7Dispatch
  · exact step109wc242s8Dispatch
  · exact step109wc242s9Dispatch
  · exact step109wc242s10Dispatch
  · exact step109wc242s11Dispatch
  · exact step109wc242s12Dispatch
  · exact step109wc242s13Dispatch
  · exact step109wc242s14Dispatch

theorem step109_orbit242_lb16_wc : QuotientRankAtLeast o242W_wc 16 :=
  o242Lb16_wc step109wc242_all_dispatch

end QiushiMatmul
