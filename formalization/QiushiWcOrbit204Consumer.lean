import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 204, exact manifest basis [274, 176, 68, 10, 1]. -/
def o204W_wc : Submodule F2 Mat3 := spanCodes [274, 176, 68, 10, 1]

private theorem step109wc204_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc204MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc204_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc204MatrixCodeNat M) = M := by decide

private theorem step109wc204_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc204_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o204SourceU_wc : Fin 13 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [258, 160, 68, 16, 10, 1]
  | ⟨1, _⟩ => spanCodes [260, 166, 68, 22, 10, 1]
  | ⟨2, _⟩ => spanCodes [272, 176, 68, 8, 2, 1]
  | ⟨3, _⟩ => spanCodes [274, 176, 64, 10, 4, 1]
  | ⟨4, _⟩ => spanCodes [274, 144, 68, 32, 10, 1]
  | ⟨5, _⟩ => spanCodes [274, 146, 68, 34, 10, 1]
  | ⟨6, _⟩ => spanCodes [274, 148, 68, 36, 10, 1]
  | ⟨7, _⟩ => spanCodes [274, 150, 68, 38, 10, 1]
  | ⟨8, _⟩ => spanCodes [274, 128, 68, 48, 10, 1]
  | ⟨9, _⟩ => spanCodes [274, 130, 68, 50, 10, 1]
  | ⟨10, _⟩ => spanCodes [274, 132, 68, 52, 10, 1]
  | ⟨11, _⟩ => spanCodes [274, 134, 68, 54, 10, 1]
  | ⟨12, _⟩ => spanCodes [256, 162, 66, 18, 10, 6, 1]
  | ⟨k + 13, h⟩ => absurd h (by omega)

def o204SourceLb_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [15, 15, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 12].getD k 0

def o204Lambda_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o204CoverB_wc : Fin 13 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [258, 160, 68, 16, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [260, 166, 68, 22, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [272, 176, 68, 8, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [274, 176, 64, 10, 4, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [274, 144, 68, 32, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [274, 146, 68, 34, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [274, 148, 68, 36, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [274, 150, 68, 38, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [274, 128, 68, 48, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [274, 130, 68, 50, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [274, 132, 68, 52, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [274, 134, 68, 54, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [256, 162, 66, 18, 10, 6, 1] c
  | ⟨k + 13, h⟩, _ => absurd h (by omega)

def o204Cover_wc (i : Fin 13) (M : Mat3) : Prop :=
  o204CoverB_wc i (step109wc204MatrixCodeNat M) = true

theorem o204CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 13, if o204CoverB_wc i c.val = true then o204Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o204MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 13, if o204Cover_wc i M then o204Lambda_wc i else 0 := by
  have h := o204CodeCoverage_wc ⟨step109wc204MatrixCodeNat M, step109wc204_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o204CoverB_wc i (step109wc204MatrixCodeNat M) <;> simp [o204Cover_wc, hb]

theorem o204W_le_source_wc (i : Fin 13) : o204W_wc ≤ o204SourceU_wc i := by
  fin_cases i
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [258, 160, 68, 16, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [258, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [260, 166, 68, 22, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [260, 166, 68, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 166, 68, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [272, 176, 68, 8, 2, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [272, 176, 68, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 176, 68, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 176, 64, 10, 4, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 176, 64, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 176, 64, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 144, 68, 32, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 144, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 146, 68, 34, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 146, 68, 34, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 146, 68, 34, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 148, 68, 36, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 148, 68, 36, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 148, 68, 36, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 150, 68, 38, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 150, 68, 38, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 150, 68, 38, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 128, 68, 48, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 128, 68, 48, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 128, 68, 48, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 130, 68, 50, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 130, 68, 50, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 130, 68, 50, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 132, 68, 52, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 132, 68, 52, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 132, 68, 52, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [274, 134, 68, 54, 10, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [274, 134, 68, 54, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 134, 68, 54, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [274, 176, 68, 10, 1] ≤ spanCodes [256, 162, 66, 18, 10, 6, 1]
    apply step109wc204_spanCodes_le_of_gens [274, 176, 68, 10, 1] (spanCodes [256, 162, 66, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 162, 66, 18, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o204CoverSound_wc (i : Fin 13) (M : Mat3) (h : o204Cover_wc i M) : M ∈ o204SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [258, 160, 68, 16, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 166, 68, 22, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 166, 68, 22, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 176, 68, 8, 2, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 176, 68, 8, 2, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 176, 64, 10, 4, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 176, 64, 10, 4, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 144, 68, 32, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 144, 68, 32, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 146, 68, 34, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 146, 68, 34, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 148, 68, 36, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 148, 68, 36, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 150, 68, 38, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 150, 68, 38, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 128, 68, 48, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 128, 68, 48, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 130, 68, 50, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 130, 68, 50, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 132, 68, 52, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 132, 68, 52, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 134, 68, 54, 10, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 134, 68, 54, 10, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 162, 66, 18, 10, 6, 1]
    unfold o204Cover_wc o204CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 162, 66, 18, 10, 6, 1] (step109wc204MatrixCodeNat M) h
    rwa [step109wc204_codeMat_matrixCode_all] at hspan

private theorem o204Cert_wc : (13 - 1) * 15 < ∑ i : Fin 13, o204Lambda_wc i * o204SourceLb_wc i := by
  simp only [o204Lambda_wc, o204SourceLb_wc]; decide
private theorem o204LambdaSum_wc : 1 ≤ ∑ i : Fin 13, o204Lambda_wc i := by
  simp only [o204Lambda_wc]; decide

theorem o204Lb16_wc
    (hSource : ∀ i : Fin 13, QuotientRankAtLeast (o204SourceU_wc i) (o204SourceLb_wc i)) :
    QuotientRankAtLeast o204W_wc 16 :=
  quotientRankAtLeast_of_contradiction o204W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o204SourceU_wc o204SourceLb_wc
      o204Lambda_wc 1 15
      o204Cover_wc o204W_le_source_wc hSource
      o204LambdaSum_wc o204CoverSound_wc
      (fun M => o204MatCoverage_wc M) (by omega) o204Cert_wc D)

end QiushiMatmul
