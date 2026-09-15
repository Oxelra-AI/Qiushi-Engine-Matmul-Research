import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 202, exact manifest basis [304, 160, 68, 10, 1]. -/
def o202W_wc : Submodule F2 Mat3 := spanCodes [304, 160, 68, 10, 1]

private theorem step109wc202_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc202MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc202_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc202MatrixCodeNat M) = M := by decide

private theorem step109wc202_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc202_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o202SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [288, 160, 68, 16, 10, 1]
  | ⟨1, _⟩ => spanCodes [292, 160, 68, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [294, 160, 68, 22, 10, 1]
  | ⟨3, _⟩ => spanCodes [272, 128, 68, 32, 10, 1]
  | ⟨4, _⟩ => spanCodes [274, 130, 68, 34, 10, 1]
  | ⟨5, _⟩ => spanCodes [276, 132, 68, 36, 10, 1]
  | ⟨6, _⟩ => spanCodes [256, 144, 68, 48, 10, 1]
  | ⟨7, _⟩ => spanCodes [258, 146, 68, 50, 10, 1]
  | ⟨8, _⟩ => spanCodes [262, 150, 68, 54, 10, 1]
  | ⟨9, _⟩ => spanCodes [304, 160, 68, 8, 2, 1]
  | ⟨10, _⟩ => spanCodes [304, 160, 64, 10, 4, 1]
  | ⟨11, _⟩ => spanCodes [304, 160, 66, 10, 6, 1]
  | ⟨12, _⟩ => spanCodes [290, 160, 68, 18, 10, 1]
  | ⟨13, _⟩ => spanCodes [278, 134, 68, 38, 10, 1]
  | ⟨14, _⟩ => spanCodes [260, 148, 68, 52, 10, 1]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o202SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14, 14, 14].getD k 0

def o202Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o202CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [288, 160, 68, 16, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [292, 160, 68, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [294, 160, 68, 22, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [272, 128, 68, 32, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [274, 130, 68, 34, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [276, 132, 68, 36, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 144, 68, 48, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [258, 146, 68, 50, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [262, 150, 68, 54, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [304, 160, 68, 8, 2, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [304, 160, 64, 10, 4, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [304, 160, 66, 10, 6, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [290, 160, 68, 18, 10, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [278, 134, 68, 38, 10, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [260, 148, 68, 52, 10, 1] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o202Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o202CoverB_wc i (step109wc202MatrixCodeNat M) = true

theorem o202CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 15, if o202CoverB_wc i c.val = true then o202Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o202MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o202Cover_wc i M then o202Lambda_wc i else 0 := by
  have h := o202CodeCoverage_wc ⟨step109wc202MatrixCodeNat M, step109wc202_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o202CoverB_wc i (step109wc202MatrixCodeNat M) <;> simp [o202Cover_wc, hb]

theorem o202W_le_source_wc (i : Fin 15) : o202W_wc ≤ o202SourceU_wc i := by
  fin_cases i
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [288, 160, 68, 16, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [288, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [292, 160, 68, 20, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [292, 160, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [294, 160, 68, 22, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [294, 160, 68, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [294, 160, 68, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [272, 128, 68, 32, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [272, 128, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [274, 130, 68, 34, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [274, 130, 68, 34, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 130, 68, 34, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [276, 132, 68, 36, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [276, 132, 68, 36, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 36, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [256, 144, 68, 48, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [256, 144, 68, 48, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [258, 146, 68, 50, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [258, 146, 68, 50, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 146, 68, 50, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [262, 150, 68, 54, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [262, 150, 68, 54, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 150, 68, 54, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [304, 160, 68, 8, 2, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [304, 160, 68, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [304, 160, 64, 10, 4, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [304, 160, 64, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [304, 160, 66, 10, 6, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [304, 160, 66, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 66, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [290, 160, 68, 18, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [290, 160, 68, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [290, 160, 68, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [278, 134, 68, 38, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [278, 134, 68, 38, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 134, 68, 38, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 10, 1] ≤ spanCodes [260, 148, 68, 52, 10, 1]
    apply step109wc202_spanCodes_le_of_gens [304, 160, 68, 10, 1] (spanCodes [260, 148, 68, 52, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 148, 68, 52, 10, 1] n (by fin_cases hn <;> decide)

theorem o202CoverSound_wc (i : Fin 15) (M : Mat3) (h : o202Cover_wc i M) : M ∈ o202SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [288, 160, 68, 16, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 16, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 160, 68, 20, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 20, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [294, 160, 68, 22, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [294, 160, 68, 22, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 68, 32, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 130, 68, 34, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 130, 68, 34, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 68, 36, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 36, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 68, 48, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 146, 68, 50, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 146, 68, 50, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 150, 68, 54, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 150, 68, 54, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 68, 8, 2, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 68, 8, 2, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 64, 10, 4, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 10, 4, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 66, 10, 6, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 66, 10, 6, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [290, 160, 68, 18, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [290, 160, 68, 18, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [278, 134, 68, 38, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 134, 68, 38, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 148, 68, 52, 10, 1]
    unfold o202Cover_wc o202CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 148, 68, 52, 10, 1] (step109wc202MatrixCodeNat M) h
    rwa [step109wc202_codeMat_matrixCode_all] at hspan

private theorem o202Cert_wc : (15 - 1) * 15 < ∑ i : Fin 15, o202Lambda_wc i * o202SourceLb_wc i := by
  simp only [o202Lambda_wc, o202SourceLb_wc]; decide
private theorem o202LambdaSum_wc : 1 ≤ ∑ i : Fin 15, o202Lambda_wc i := by
  simp only [o202Lambda_wc]; decide

theorem o202Lb16_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o202SourceU_wc i) (o202SourceLb_wc i)) :
    QuotientRankAtLeast o202W_wc 16 :=
  quotientRankAtLeast_of_contradiction o202W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o202SourceU_wc o202SourceLb_wc
      o202Lambda_wc 1 15
      o202Cover_wc o202W_le_source_wc hSource
      o202LambdaSum_wc o202CoverSound_wc
      (fun M => o202MatCoverage_wc M) (by omega) o202Cert_wc D)

end QiushiMatmul
