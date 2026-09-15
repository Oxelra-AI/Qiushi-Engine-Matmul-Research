import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 213, exact manifest basis [276, 132, 96, 10, 1]. -/
def o213W_wc : Submodule F2 Mat3 := spanCodes [276, 132, 96, 10, 1]

private theorem step109wc213_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc213MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc213_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc213MatrixCodeNat M) = M := by decide

private theorem step109wc213_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc213_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o213SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [262, 132, 96, 18, 10, 1]
  | ⟨1, _⟩ => spanCodes [256, 132, 96, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [258, 132, 96, 22, 10, 1]
  | ⟨3, _⟩ => spanCodes [276, 132, 68, 36, 10, 1]
  | ⟨4, _⟩ => spanCodes [276, 132, 70, 38, 10, 1]
  | ⟨5, _⟩ => spanCodes [276, 132, 82, 50, 10, 1]
  | ⟨6, _⟩ => spanCodes [272, 128, 96, 10, 4, 1]
  | ⟨7, _⟩ => spanCodes [274, 130, 96, 10, 6, 1]
  | ⟨8, _⟩ => spanCodes [260, 132, 96, 16, 10, 1]
  | ⟨9, _⟩ => spanCodes [276, 132, 64, 32, 10, 1]
  | ⟨10, _⟩ => spanCodes [276, 132, 66, 34, 10, 1]
  | ⟨11, _⟩ => spanCodes [276, 132, 80, 48, 10, 1]
  | ⟨12, _⟩ => spanCodes [276, 132, 84, 52, 10, 1]
  | ⟨13, _⟩ => spanCodes [276, 132, 86, 54, 10, 1]
  | ⟨14, _⟩ => spanCodes [276, 132, 96, 8, 2, 1]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o213SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 14, 14, 14, 14, 14, 14, 14, 14, 13].getD k 0

def o213Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o213CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [262, 132, 96, 18, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 132, 96, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [258, 132, 96, 22, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [276, 132, 68, 36, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [276, 132, 70, 38, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [276, 132, 82, 50, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [272, 128, 96, 10, 4, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [274, 130, 96, 10, 6, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [260, 132, 96, 16, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [276, 132, 64, 32, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [276, 132, 66, 34, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [276, 132, 80, 48, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [276, 132, 84, 52, 10, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [276, 132, 86, 54, 10, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [276, 132, 96, 8, 2, 1] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o213Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o213CoverB_wc i (step109wc213MatrixCodeNat M) = true

theorem o213CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 15, if o213CoverB_wc i c.val = true then o213Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o213MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o213Cover_wc i M then o213Lambda_wc i else 0 := by
  have h := o213CodeCoverage_wc ⟨step109wc213MatrixCodeNat M, step109wc213_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o213CoverB_wc i (step109wc213MatrixCodeNat M) <;> simp [o213Cover_wc, hb]

theorem o213W_le_source_wc (i : Fin 15) : o213W_wc ≤ o213SourceU_wc i := by
  fin_cases i
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [262, 132, 96, 18, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [262, 132, 96, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 132, 96, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [256, 132, 96, 20, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [256, 132, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [258, 132, 96, 22, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [258, 132, 96, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 132, 96, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 68, 36, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 68, 36, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 36, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 70, 38, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 70, 38, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 70, 38, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 82, 50, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 82, 50, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 82, 50, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [272, 128, 96, 10, 4, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [272, 128, 96, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [274, 130, 96, 10, 6, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [274, 130, 96, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 130, 96, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [260, 132, 96, 16, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [260, 132, 96, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 64, 32, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 64, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 64, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 66, 34, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 66, 34, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 66, 34, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 80, 48, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 80, 48, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 80, 48, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 84, 52, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 84, 52, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 52, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 86, 54, 10, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 86, 54, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 86, 54, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [276, 132, 96, 10, 1] ≤ spanCodes [276, 132, 96, 8, 2, 1]
    apply step109wc213_spanCodes_le_of_gens [276, 132, 96, 10, 1] (spanCodes [276, 132, 96, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 96, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o213CoverSound_wc (i : Fin 15) (M : Mat3) (h : o213Cover_wc i M) : M ∈ o213SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [262, 132, 96, 18, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 96, 18, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 96, 20, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 20, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 132, 96, 22, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 132, 96, 22, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 68, 36, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 36, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 70, 38, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 70, 38, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 82, 50, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 82, 50, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 96, 10, 4, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 96, 10, 4, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 130, 96, 10, 6, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 130, 96, 10, 6, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 132, 96, 16, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 16, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 64, 32, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 64, 32, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 66, 34, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 66, 34, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 80, 48, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 80, 48, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 84, 52, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 84, 52, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 86, 54, 10, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 86, 54, 10, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 96, 8, 2, 1]
    unfold o213Cover_wc o213CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 96, 8, 2, 1] (step109wc213MatrixCodeNat M) h
    rwa [step109wc213_codeMat_matrixCode_all] at hspan

private theorem o213Cert_wc : (15 - 1) * 15 < ∑ i : Fin 15, o213Lambda_wc i * o213SourceLb_wc i := by
  simp only [o213Lambda_wc, o213SourceLb_wc]; decide
private theorem o213LambdaSum_wc : 1 ≤ ∑ i : Fin 15, o213Lambda_wc i := by
  simp only [o213Lambda_wc]; decide

theorem o213Lb16_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o213SourceU_wc i) (o213SourceLb_wc i)) :
    QuotientRankAtLeast o213W_wc 16 :=
  quotientRankAtLeast_of_contradiction o213W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o213SourceU_wc o213SourceLb_wc
      o213Lambda_wc 1 15
      o213Cover_wc o213W_le_source_wc hSource
      o213LambdaSum_wc o213CoverSound_wc
      (fun M => o213MatCoverage_wc M) (by omega) o213Cert_wc D)

end QiushiMatmul
