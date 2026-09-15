import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 64, exact manifest basis [258, 160, 68, 16, 10, 1]. -/
def o64W_wc : Submodule F2 Mat3 := spanCodes [258, 160, 68, 16, 10, 1]

private theorem step109wc64_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc64MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc64_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc64MatrixCodeNat M) = M := by decide

private theorem step109wc64_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc64_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o64SourceU_wc : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 160, 68, 16, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [258, 128, 64, 32, 16, 10, 4, 1]
  | ⟨2, _⟩ => spanCodes [258, 130, 66, 34, 16, 10, 6, 1]
  | ⟨3, _⟩ => spanCodes [258, 128, 66, 32, 16, 10, 6, 1]
  | ⟨4, _⟩ => spanCodes [258, 130, 64, 34, 16, 10, 4, 1]
  | ⟨k + 5, h⟩ => absurd h (by omega)

def o64SourceLb_wc : Fin 5 → ℕ
  | ⟨k, _⟩ => [12, 9, 9, 9, 9].getD k 0

def o64Lambda_wc : Fin 5 → ℕ
  | ⟨k, _⟩ => [2, 1, 1, 1, 1].getD k 0

def o64CoverB_wc : Fin 5 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 160, 68, 16, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [258, 128, 64, 32, 16, 10, 4, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [258, 130, 66, 34, 16, 10, 6, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [258, 128, 66, 32, 16, 10, 6, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [258, 130, 64, 34, 16, 10, 4, 1] c
  | ⟨k + 5, h⟩, _ => absurd h (by omega)

def o64Cover_wc (i : Fin 5) (M : Mat3) : Prop :=
  o64CoverB_wc i (step109wc64MatrixCodeNat M) = true

theorem o64CodeCoverage_wc (c : Fin 512) :
    2 ≤ ∑ i : Fin 5, if o64CoverB_wc i c.val = true then o64Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o64MatCoverage_wc (M : Mat3) :
    2 ≤ ∑ i : Fin 5, if o64Cover_wc i M then o64Lambda_wc i else 0 := by
  have h := o64CodeCoverage_wc ⟨step109wc64MatrixCodeNat M, step109wc64_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o64CoverB_wc i (step109wc64MatrixCodeNat M) <;> simp [o64Cover_wc, hb]

theorem o64W_le_source_wc (i : Fin 5) : o64W_wc ≤ o64SourceU_wc i := by
  fin_cases i
  · change spanCodes [258, 160, 68, 16, 10, 1] ≤ spanCodes [256, 160, 68, 16, 8, 2, 1]
    apply step109wc64_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1] (spanCodes [256, 160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 160, 68, 16, 10, 1] ≤ spanCodes [258, 128, 64, 32, 16, 10, 4, 1]
    apply step109wc64_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1] (spanCodes [258, 128, 64, 32, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 32, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 160, 68, 16, 10, 1] ≤ spanCodes [258, 130, 66, 34, 16, 10, 6, 1]
    apply step109wc64_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1] (spanCodes [258, 130, 66, 34, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 66, 34, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 160, 68, 16, 10, 1] ≤ spanCodes [258, 128, 66, 32, 16, 10, 6, 1]
    apply step109wc64_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1] (spanCodes [258, 128, 66, 32, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 160, 68, 16, 10, 1] ≤ spanCodes [258, 130, 64, 34, 16, 10, 4, 1]
    apply step109wc64_spanCodes_le_of_gens [258, 160, 68, 16, 10, 1] (spanCodes [258, 130, 64, 34, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 64, 34, 16, 10, 4, 1] n (by fin_cases hn <;> decide)

theorem o64CoverSound_wc (i : Fin 5) (M : Mat3) (h : o64Cover_wc i M) : M ∈ o64SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 160, 68, 16, 8, 2, 1]
    unfold o64Cover_wc o64CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 8, 2, 1] (step109wc64MatrixCodeNat M) h
    rwa [step109wc64_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 64, 32, 16, 10, 4, 1]
    unfold o64Cover_wc o64CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 32, 16, 10, 4, 1] (step109wc64MatrixCodeNat M) h
    rwa [step109wc64_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 130, 66, 34, 16, 10, 6, 1]
    unfold o64Cover_wc o64CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 66, 34, 16, 10, 6, 1] (step109wc64MatrixCodeNat M) h
    rwa [step109wc64_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 66, 32, 16, 10, 6, 1]
    unfold o64Cover_wc o64CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 6, 1] (step109wc64MatrixCodeNat M) h
    rwa [step109wc64_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 130, 64, 34, 16, 10, 4, 1]
    unfold o64Cover_wc o64CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 64, 34, 16, 10, 4, 1] (step109wc64MatrixCodeNat M) h
    rwa [step109wc64_codeMat_matrixCode_all] at hspan

private theorem o64Cert_wc : (6 - 2) * 14 < ∑ i : Fin 5, o64Lambda_wc i * o64SourceLb_wc i := by
  simp only [o64Lambda_wc, o64SourceLb_wc]; decide
private theorem o64LambdaSum_wc : 2 ≤ ∑ i : Fin 5, o64Lambda_wc i := by
  simp only [o64Lambda_wc]; decide

theorem o64Lb15_wc
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o64SourceU_wc i) (o64SourceLb_wc i)) :
    QuotientRankAtLeast o64W_wc 15 :=
  quotientRankAtLeast_of_contradiction o64W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o64SourceU_wc o64SourceLb_wc
      o64Lambda_wc 2 14
      o64Cover_wc o64W_le_source_wc hSource
      o64LambdaSum_wc o64CoverSound_wc
      (fun M => o64MatCoverage_wc M) (by omega) o64Cert_wc D)

end QiushiMatmul
