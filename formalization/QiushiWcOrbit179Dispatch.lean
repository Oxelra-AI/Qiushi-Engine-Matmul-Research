import QiushiCodeSpanCore
import QiushiMonotonicity
import QiushiOrbitTransport
import QiushiTransposeTransport
import QiushiWcOrbit179Consumer
import QiushiWcOrbit84Dispatch
import QiushiStep99Orbit56Dispatch
import QiushiWcOrbit78Dispatch
import QiushiOrbit10FP
import QiushiFlattenSeeds

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

private theorem step109wc179_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc179_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩


private theorem step109wc179s0_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = (codeMat 98 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * (codeMat 98 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s0_contain :
    (o179SourceU_wc ⟨0, by omega⟩) ≤ actionW (codeMat 98) (codeMat 140) o84W_wc := by
  change spanCodes [258, 128, 84, 32, 10, 1] ≤ actionW (codeMat 98) (codeMat 140) o84W_wc
  apply step109wc179_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1]
    (actionW (codeMat 98) (codeMat 140) o84W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 264 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 264 (by decide)
    have hact : actionA (codeMat 98) (codeMat 140) (codeMat 264) = codeMat 258 := by
      unfold actionA
      rw [step109wc179s0_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 264 * (codeMat 98 : Mat3).transpose = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 32 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 32 (by decide)
    have hact : actionA (codeMat 98) (codeMat 140) (codeMat 32) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s0_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 32 * (codeMat 98 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 84 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 84 (by decide)
    have hact : actionA (codeMat 98) (codeMat 140) (codeMat 84) = codeMat 84 := by
      unfold actionA
      rw [step109wc179s0_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 84 * (codeMat 98 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 1 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 98) (codeMat 140) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s0_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 1 * (codeMat 98 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 258 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 258 (by decide)
    have hact : actionA (codeMat 98) (codeMat 140) (codeMat 258) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s0_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 258 * (codeMat 98 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o84W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 98) (codeMat 140) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s0_QtInv]
      show (codeMat 98 : Mat3).transpose * codeMat 128 * (codeMat 98 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s0Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨0, by omega⟩) 14 := by
  have hP : Invertible (codeMat 98 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 98) (codeMat 140) o84W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 98) (codeMat 140) hP hQ o84W_wc 14
      step109_orbit84_lb14_wc
  exact quotientRankAtLeast_mono step109wc179s0_contain hAct

private def step109wc179s1SrcT : Submodule F2 Mat3 := spanCodes [256, 160, 66, 20, 8, 1]

private theorem step109wc179s1SrcT_lb : QuotientRankAtLeast step109wc179s1SrcT 14 := by
  have ht := quotientRankAtLeast_transpose step99_orbit56_lb14_unconditional
  have hle : step109wc179s1SrcT ≤ transposeW o56W := by
    unfold step109wc179s1SrcT transposeW
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

private theorem step109wc179s1_QtInv :
    (codeMat 205 : Mat3).transpose⁻¹ = (codeMat 242 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 205 : Mat3).transpose * (codeMat 242 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s1_contain :
    (o179SourceU_wc ⟨1, by omega⟩) ≤ actionW (codeMat 279) (codeMat 205) step109wc179s1SrcT := by
  change spanCodes [260, 128, 84, 32, 10, 1] ≤ actionW (codeMat 279) (codeMat 205) step109wc179s1SrcT
  apply step109wc179_spanCodes_le_of_gens [260, 128, 84, 32, 10, 1]
    (actionW (codeMat 279) (codeMat 205) step109wc179s1SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 9 ∈ step109wc179s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 9 (by decide)
    have hact : actionA (codeMat 279) (codeMat 205) (codeMat 9) = codeMat 260 := by
      unfold actionA
      rw [step109wc179s1_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 9 * (codeMat 242 : Mat3).transpose = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ step109wc179s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 256 (by decide)
    have hact : actionA (codeMat 279) (codeMat 205) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s1_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 256 * (codeMat 242 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 425 ∈ step109wc179s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 425 (by decide)
    have hact : actionA (codeMat 279) (codeMat 205) (codeMat 425) = codeMat 84 := by
      unfold actionA
      rw [step109wc179s1_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 425 * (codeMat 242 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ step109wc179s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 8 (by decide)
    have hact : actionA (codeMat 279) (codeMat 205) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s1_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 8 * (codeMat 242 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 284 ∈ step109wc179s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 284 (by decide)
    have hact : actionA (codeMat 279) (codeMat 205) (codeMat 284) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s1_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 284 * (codeMat 242 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 511 ∈ step109wc179s1SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 20, 8, 1] 511 (by decide)
    have hact : actionA (codeMat 279) (codeMat 205) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s1_QtInv]
      show (codeMat 279 : Mat3).transpose * codeMat 511 * (codeMat 242 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s1Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨1, by omega⟩) 14 := by
  have hP : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 205 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 279) (codeMat 205) step109wc179s1SrcT) 14 :=
    @quotientRankAtLeast_action (codeMat 279) (codeMat 205) hP hQ step109wc179s1SrcT 14
      step109wc179s1SrcT_lb
  exact quotientRankAtLeast_mono step109wc179s1_contain hAct


private theorem step109wc179s2_QtInv :
    (codeMat 355 : Mat3).transpose⁻¹ = (codeMat 190 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 355 : Mat3).transpose * (codeMat 190 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s2_contain :
    (o179SourceU_wc ⟨2, by omega⟩) ≤ actionW (codeMat 412) (codeMat 355) o78W_wc := by
  change spanCodes [262, 128, 84, 32, 10, 1] ≤ actionW (codeMat 412) (codeMat 355) o78W_wc
  apply step109wc179_spanCodes_le_of_gens [262, 128, 84, 32, 10, 1]
    (actionW (codeMat 412) (codeMat 355) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 505 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 505 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 505) = codeMat 262 := by
      unfold actionA
      rw [step109wc179s2_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 505 * (codeMat 190 : Mat3).transpose = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 1 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 1 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s2_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 1 * (codeMat 190 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 498 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 498 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 498) = codeMat 84 := by
      unfold actionA
      rw [step109wc179s2_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 498 * (codeMat 190 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 390) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s2_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 390 * (codeMat 190 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 268 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 268 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 268) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s2_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 268 * (codeMat 190 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 412) (codeMat 355) (codeMat 365) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s2_QtInv]
      show (codeMat 412 : Mat3).transpose * codeMat 365 * (codeMat 190 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s2Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨2, by omega⟩) 14 := by
  have hP : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 355 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 412) (codeMat 355) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 412) (codeMat 355) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc179s2_contain hAct


private theorem step109wc179s3_QtInv :
    (codeMat 412 : Mat3).transpose⁻¹ = (codeMat 111 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 412 : Mat3).transpose * (codeMat 111 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s3_contain :
    (o179SourceU_wc ⟨3, by omega⟩) ≤ actionW (codeMat 117) (codeMat 412) o78W_wc := by
  change spanCodes [274, 128, 84, 32, 10, 1] ≤ actionW (codeMat 117) (codeMat 412) o78W_wc
  apply step109wc179_spanCodes_le_of_gens [274, 128, 84, 32, 10, 1]
    (actionW (codeMat 117) (codeMat 412) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 371 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 371 (by decide)
    have hact : actionA (codeMat 117) (codeMat 412) (codeMat 371) = codeMat 274 := by
      unfold actionA
      rw [step109wc179s3_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 371 * (codeMat 111 : Mat3).transpose = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 117) (codeMat 412) (codeMat 390) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s3_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 390 * (codeMat 111 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 116 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 116 (by decide)
    have hact : actionA (codeMat 117) (codeMat 412) (codeMat 116) = codeMat 84 := by
      unfold actionA
      rw [step109wc179s3_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 116 * (codeMat 111 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 117) (codeMat 412) (codeMat 365) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s3_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 365 * (codeMat 111 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 274 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 274 (by decide)
    have hact : actionA (codeMat 117) (codeMat 412) (codeMat 274) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s3_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 274 * (codeMat 111 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 128 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 128 (by decide)
    have hact : actionA (codeMat 117) (codeMat 412) (codeMat 128) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s3_QtInv]
      show (codeMat 117 : Mat3).transpose * codeMat 128 * (codeMat 111 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s3Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨3, by omega⟩) 14 := by
  have hP : Invertible (codeMat 117 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 412 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 117) (codeMat 412) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 117) (codeMat 412) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc179s3_contain hAct


private theorem step109wc179s4_QtInv :
    (codeMat 345 : Mat3).transpose⁻¹ = (codeMat 345 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 345 : Mat3).transpose * (codeMat 345 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s4_contain :
    (o179SourceU_wc ⟨4, by omega⟩) ≤ actionW (codeMat 188) (codeMat 345) o56W := by
  change spanCodes [276, 128, 84, 32, 10, 1] ≤ actionW (codeMat 188) (codeMat 345) o56W
  apply step109wc179_spanCodes_le_of_gens [276, 128, 84, 32, 10, 1]
    (actionW (codeMat 188) (codeMat 345) o56W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 416 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 416 (by decide)
    have hact : actionA (codeMat 188) (codeMat 345) (codeMat 416) = codeMat 276 := by
      unfold actionA
      rw [step109wc179s4_QtInv]
      show (codeMat 188 : Mat3).transpose * codeMat 416 * (codeMat 345 : Mat3).transpose = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 188) (codeMat 345) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s4_QtInv]
      show (codeMat 188 : Mat3).transpose * codeMat 2 * (codeMat 345 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 419 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 419 (by decide)
    have hact : actionA (codeMat 188) (codeMat 345) (codeMat 419) = codeMat 84 := by
      unfold actionA
      rw [step109wc179s4_QtInv]
      show (codeMat 188 : Mat3).transpose * codeMat 419 * (codeMat 345 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 256 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 188) (codeMat 345) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s4_QtInv]
      show (codeMat 188 : Mat3).transpose * codeMat 256 * (codeMat 345 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 338 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 338 (by decide)
    have hact : actionA (codeMat 188) (codeMat 345) (codeMat 338) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s4_QtInv]
      show (codeMat 188 : Mat3).transpose * codeMat 338 * (codeMat 345 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 511 ∈ o56W :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 160, 80, 12, 2, 1] 511 (by decide)
    have hact : actionA (codeMat 188) (codeMat 345) (codeMat 511) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s4_QtInv]
      show (codeMat 188 : Mat3).transpose * codeMat 511 * (codeMat 345 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s4Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨4, by omega⟩) 14 := by
  have hP : Invertible (codeMat 188 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 345 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 188) (codeMat 345) o56W) 14 :=
    @quotientRankAtLeast_action (codeMat 188) (codeMat 345) hP hQ o56W 14
      step99_orbit56_lb14_unconditional
  exact quotientRankAtLeast_mono step109wc179s4_contain hAct


private theorem step109wc179s5_QtInv :
    (codeMat 494 : Mat3).transpose⁻¹ = (codeMat 501 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 494 : Mat3).transpose * (codeMat 501 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s5_contain :
    (o179SourceU_wc ⟨5, by omega⟩) ≤ actionW (codeMat 494) (codeMat 494) o78W_wc := by
  change spanCodes [278, 128, 84, 32, 10, 1] ≤ actionW (codeMat 494) (codeMat 494) o78W_wc
  apply step109wc179_spanCodes_le_of_gens [278, 128, 84, 32, 10, 1]
    (actionW (codeMat 494) (codeMat 494) o78W_wc)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5
  · subst h0
    have hw : codeMat 21 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 21 (by decide)
    have hact : actionA (codeMat 494) (codeMat 494) (codeMat 21) = codeMat 278 := by
      unfold actionA
      rw [step109wc179s5_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 21 * (codeMat 501 : Mat3).transpose = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 365 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 365 (by decide)
    have hact : actionA (codeMat 494) (codeMat 494) (codeMat 365) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s5_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 365 * (codeMat 501 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 281 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 281 (by decide)
    have hact : actionA (codeMat 494) (codeMat 494) (codeMat 281) = codeMat 84 := by
      unfold actionA
      rw [step109wc179s5_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 281 * (codeMat 501 : Mat3).transpose = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 504 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 504 (by decide)
    have hact : actionA (codeMat 494) (codeMat 494) (codeMat 504) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s5_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 504 * (codeMat 501 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 245 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 245 (by decide)
    have hact : actionA (codeMat 494) (codeMat 494) (codeMat 245) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s5_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 245 * (codeMat 501 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 390 ∈ o78W_wc :=
      spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 10, 1] 390 (by decide)
    have hact : actionA (codeMat 494) (codeMat 494) (codeMat 390) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s5_QtInv]
      show (codeMat 494 : Mat3).transpose * codeMat 390 * (codeMat 501 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s5Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨5, by omega⟩) 14 := by
  have hP : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 494 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 494) (codeMat 494) o78W_wc) 14 :=
    @quotientRankAtLeast_action (codeMat 494) (codeMat 494) hP hQ o78W_wc 14
      step109_orbit78_lb14_wc
  exact quotientRankAtLeast_mono step109wc179s5_contain hAct


private theorem step109wc179s6_QtInv :
    (codeMat 84 : Mat3).transpose⁻¹ = (codeMat 84 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 84 : Mat3).transpose * (codeMat 84 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s6_contain :
    (o179SourceU_wc ⟨6, by omega⟩) ≤ actionW (codeMat 84) (codeMat 84) orbit10W := by
  change spanCodes [256, 128, 68, 32, 16, 10, 1] ≤ actionW (codeMat 84) (codeMat 84) orbit10W
  apply step109wc179_spanCodes_le_of_gens [256, 128, 68, 32, 16, 10, 1]
    (actionW (codeMat 84) (codeMat 84) orbit10W)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 1 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 1 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 1 * (codeMat 84 : Mat3).transpose = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 2 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 2 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 2) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 2 * (codeMat 84 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 68 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 68 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 68) = codeMat 68 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 68 * (codeMat 84 : Mat3).transpose = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 8 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 8) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 8 * (codeMat 84 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 16 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 16 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 16) = codeMat 16 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 16 * (codeMat 84 : Mat3).transpose = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 160 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 160 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 160) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 160 * (codeMat 84 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 256 ∈ orbit10W :=
      spanContainsCodeCore_implies_mem_spanCodes [1, 2, 8, 16, 68, 160, 256] 256 (by decide)
    have hact : actionA (codeMat 84) (codeMat 84) (codeMat 256) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s6_QtInv]
      show (codeMat 84 : Mat3).transpose * codeMat 256 * (codeMat 84 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s6Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨6, by omega⟩) 12 := by
  have hP : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 84 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 84) (codeMat 84) orbit10W) 12 :=
    @quotientRankAtLeast_action (codeMat 84) (codeMat 84) hP hQ orbit10W 12
      orbit10_lb12
  exact quotientRankAtLeast_mono step109wc179s6_contain hAct


private theorem step109wc179s7_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = (codeMat 161 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * (codeMat 161 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s7_contain :
    (o179SourceU_wc ⟨7, by omega⟩) ≤ actionW (codeMat 273) (codeMat 161) flatW_7 := by
  change spanCodes [128, 80, 32, 8, 4, 2, 1] ≤ actionW (codeMat 273) (codeMat 161) flatW_7
  apply step109wc179_spanCodes_le_of_gens [128, 80, 32, 8, 4, 2, 1]
    (actionW (codeMat 273) (codeMat 161) flatW_7)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 256 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 256) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 256 * (codeMat 161 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 96 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 96) = codeMat 80 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 96 * (codeMat 161 : Mat3).transpose = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 16 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 16) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 16 * (codeMat 161 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 8 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 8) = codeMat 8 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 8 * (codeMat 161 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 2 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 2) = codeMat 4 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 2 * (codeMat 161 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 4 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 4) = codeMat 2 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 4 * (codeMat 161 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ flatW_7 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s7_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * (codeMat 161 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s7Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨7, by omega⟩) 9 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) flatW_7) 9 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ flatW_7 9
      flatSeed_7
  exact quotientRankAtLeast_mono step109wc179s7_contain hAct


private theorem step109wc179s8_QtInv :
    (codeMat 244 : Mat3).transpose⁻¹ = (codeMat 95 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 244 : Mat3).transpose * (codeMat 95 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s8_contain :
    (o179SourceU_wc ⟨8, by omega⟩) ≤ actionW (codeMat 266) (codeMat 244) flatW_12 := by
  change spanCodes [128, 64, 32, 18, 10, 6, 1] ≤ actionW (codeMat 266) (codeMat 244) flatW_12
  apply step109wc179_spanCodes_le_of_gens [128, 64, 32, 18, 10, 6, 1]
    (actionW (codeMat 266) (codeMat 244) flatW_12)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 384 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 384 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 384) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 384 * (codeMat 95 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 256 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 256) = codeMat 64 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 256 * (codeMat 95 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 3 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 3 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 3) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 3 * (codeMat 95 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 54 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 54 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 54) = codeMat 18 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 54 * (codeMat 95 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 52 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 52) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 52 * (codeMat 95 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 40 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 40 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 40) = codeMat 6 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 40 * (codeMat 95 : Mat3).transpose = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 266) (codeMat 244) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s8_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 32 * (codeMat 95 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s8Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨8, by omega⟩) 9 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 244 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 244) flatW_12) 9 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 244) hP hQ flatW_12 9
      flatSeed_12
  exact quotientRankAtLeast_mono step109wc179s8_contain hAct


private theorem step109wc179s9_QtInv :
    (codeMat 212 : Mat3).transpose⁻¹ = (codeMat 86 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 212 : Mat3).transpose * (codeMat 86 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s9_contain :
    (o179SourceU_wc ⟨9, by omega⟩) ≤ actionW (codeMat 458) (codeMat 212) flatW_12 := by
  change spanCodes [128, 66, 32, 18, 10, 4, 1] ≤ actionW (codeMat 458) (codeMat 212) flatW_12
  apply step109wc179_spanCodes_le_of_gens [128, 66, 32, 18, 10, 4, 1]
    (actionW (codeMat 458) (codeMat 212) flatW_12)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 438 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 438 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 438) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 438 * (codeMat 86 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 276 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 276 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 276) = codeMat 66 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 276 * (codeMat 86 : Mat3).transpose = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 1 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 1 * (codeMat 86 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 54 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 54 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 54) = codeMat 18 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 54 * (codeMat 86 : Mat3).transpose = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 52 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 52 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 52) = codeMat 10 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 52 * (codeMat 86 : Mat3).transpose = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 8 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 8) = codeMat 4 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 8 * (codeMat 86 : Mat3).transpose = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 32 ∈ flatW_12 :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 20, 8, 2, 1] 32 (by decide)
    have hact : actionA (codeMat 458) (codeMat 212) (codeMat 32) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s9_QtInv]
      show (codeMat 458 : Mat3).transpose * codeMat 32 * (codeMat 86 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s9Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨9, by omega⟩) 9 := by
  have hP : Invertible (codeMat 458 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 212 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 458) (codeMat 212) flatW_12) 9 :=
    @quotientRankAtLeast_action (codeMat 458) (codeMat 212) hP hQ flatW_12 9
      flatSeed_12
  exact quotientRankAtLeast_mono step109wc179s9_contain hAct

private def step109wc179s10SrcT : Submodule F2 Mat3 := spanCodes [256, 132, 64, 16, 8, 2, 1]

private theorem step109wc179s10SrcT_lb : QuotientRankAtLeast step109wc179s10SrcT 9 := by
  have ht := quotientRankAtLeast_transpose flatSeed_7
  have hle : step109wc179s10SrcT ≤ transposeW flatW_7 := by
    unfold step109wc179s10SrcT transposeW
    apply Submodule.span_le.mpr
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · subst h0
      show codeMat 256 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 256, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 256 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h1
      show codeMat 132 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 96, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 96 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h2
      show codeMat 64 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 4, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 4 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h3
      show codeMat 16 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 16, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 16 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h4
      show codeMat 8 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 2, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 2 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h5
      show codeMat 2 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 8, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 8 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
    · subst h6
      show codeMat 1 ∈ Submodule.map transposeLinearMap flatW_7
      exact ⟨codeMat 1, spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] 1 (by decide), by ext i j; fin_cases i <;> fin_cases j <;> decide⟩
  exact quotientRankAtLeast_mono hle ht

private theorem step109wc179s10_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = (codeMat 273 : Mat3).transpose := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * (codeMat 273 : Mat3).transpose = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem step109wc179s10_contain :
    (o179SourceU_wc ⟨10, by omega⟩) ≤ actionW (codeMat 161) (codeMat 273) step109wc179s10SrcT := by
  change spanCodes [128, 64, 32, 20, 8, 2, 1] ≤ actionW (codeMat 161) (codeMat 273) step109wc179s10SrcT
  apply step109wc179_spanCodes_le_of_gens [128, 64, 32, 20, 8, 2, 1]
    (actionW (codeMat 161) (codeMat 273) step109wc179s10SrcT)
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h0
    have hw : codeMat 16 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 16 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 16) = codeMat 128 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 16 * (codeMat 273 : Mat3).transpose = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h1
    have hw : codeMat 8 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 8 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 8) = codeMat 64 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 8 * (codeMat 273 : Mat3).transpose = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h2
    have hw : codeMat 256 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 256 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 256) = codeMat 32 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 256 * (codeMat 273 : Mat3).transpose = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h3
    have hw : codeMat 132 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 132 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 132) = codeMat 20 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 132 * (codeMat 273 : Mat3).transpose = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h4
    have hw : codeMat 64 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 64 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 64) = codeMat 8 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 64 * (codeMat 273 : Mat3).transpose = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h5
    have hw : codeMat 2 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 2) = codeMat 2 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * (codeMat 273 : Mat3).transpose = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact
  · subst h6
    have hw : codeMat 1 ∈ step109wc179s10SrcT :=
      spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 16, 8, 2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [step109wc179s10_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * (codeMat 273 : Mat3).transpose = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    exact step109wc179_codeMat_mem_actionW_of_witness hw hact

theorem step109wc179s10Dispatch :
    QuotientRankAtLeast (o179SourceU_wc ⟨10, by omega⟩) 9 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) step109wc179s10SrcT) 9 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ step109wc179s10SrcT 9
      step109wc179s10SrcT_lb
  exact quotientRankAtLeast_mono step109wc179s10_contain hAct

theorem step109wc179_all_dispatch (i : Fin 11) :
    QuotientRankAtLeast (o179SourceU_wc i) (o179SourceLb_wc i) := by
  fin_cases i
  · exact step109wc179s0Dispatch
  · exact step109wc179s1Dispatch
  · exact step109wc179s2Dispatch
  · exact step109wc179s3Dispatch
  · exact step109wc179s4Dispatch
  · exact step109wc179s5Dispatch
  · exact step109wc179s6Dispatch
  · exact step109wc179s7Dispatch
  · exact step109wc179s8Dispatch
  · exact step109wc179s9Dispatch
  · exact step109wc179s10Dispatch

theorem step109_orbit179_lb15_wc : QuotientRankAtLeast o179W_wc 15 :=
  o179Lb15_wc step109wc179_all_dispatch

end QiushiMatmul
