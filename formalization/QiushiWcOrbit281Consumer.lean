import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 281, exact manifest basis [256, 16, 10, 1]. -/
def o281W_wc : Submodule F2 Mat3 := spanCodes [256, 16, 10, 1]

private theorem step109wc281_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc281MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc281_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc281MatrixCodeNat M) = M := by decide

private theorem step109wc281_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc281_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o281SourceU_wc : Fin 14 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 68, 16, 10, 1]
  | ⟨1, _⟩ => spanCodes [256, 160, 16, 10, 1]
  | ⟨2, _⟩ => spanCodes [256, 228, 16, 10, 1]
  | ⟨3, _⟩ => spanCodes [256, 32, 16, 10, 1]
  | ⟨4, _⟩ => spanCodes [256, 128, 16, 10, 1]
  | ⟨5, _⟩ => spanCodes [256, 66, 34, 16, 10, 4, 1]
  | ⟨6, _⟩ => spanCodes [256, 130, 64, 16, 10, 6, 1]
  | ⟨7, _⟩ => spanCodes [256, 164, 96, 16, 8, 2, 1]
  | ⟨8, _⟩ => spanCodes [256, 132, 100, 16, 8, 2, 1]
  | ⟨9, _⟩ => spanCodes [256, 134, 70, 36, 16, 10, 1]
  | ⟨10, _⟩ => spanCodes [256, 130, 66, 38, 16, 10, 1]
  | ⟨11, _⟩ => spanCodes [256, 128, 70, 32, 16, 10, 1]
  | ⟨12, _⟩ => spanCodes [256, 194, 34, 16, 10, 6, 1]
  | ⟨13, _⟩ => spanCodes [256, 162, 64, 16, 10, 4, 1]
  | ⟨k + 14, h⟩ => absurd h (by omega)

def o281SourceLb_wc : Fin 14 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 14, 14, 12, 12, 12, 12, 12, 12, 12, 12, 12].getD k 0

def o281Lambda_wc : Fin 14 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o281CoverB_wc : Fin 14 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 68, 16, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 160, 16, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 228, 16, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 32, 16, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 128, 16, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 66, 34, 16, 10, 4, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 130, 64, 16, 10, 6, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 164, 96, 16, 8, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 132, 100, 16, 8, 2, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [256, 134, 70, 36, 16, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [256, 130, 66, 38, 16, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [256, 128, 70, 32, 16, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [256, 194, 34, 16, 10, 6, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [256, 162, 64, 16, 10, 4, 1] c
  | ⟨k + 14, h⟩, _ => absurd h (by omega)

def o281Cover_wc (i : Fin 14) (M : Mat3) : Prop :=
  o281CoverB_wc i (step109wc281MatrixCodeNat M) = true

theorem o281CodeCoverage_wc (c : Fin 512) :
    2 ≤ ∑ i : Fin 14, if o281CoverB_wc i c.val = true then o281Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o281MatCoverage_wc (M : Mat3) :
    2 ≤ ∑ i : Fin 14, if o281Cover_wc i M then o281Lambda_wc i else 0 := by
  have h := o281CodeCoverage_wc ⟨step109wc281MatrixCodeNat M, step109wc281_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o281CoverB_wc i (step109wc281MatrixCodeNat M) <;> simp [o281Cover_wc, hb]

theorem o281W_le_source_wc (i : Fin 14) : o281W_wc ≤ o281SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 68, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 160, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 160, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 228, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 228, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 228, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 32, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 128, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 128, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 66, 34, 16, 10, 4, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 66, 34, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 66, 34, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 130, 64, 16, 10, 6, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 130, 64, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 130, 64, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 164, 96, 16, 8, 2, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 164, 96, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 132, 100, 16, 8, 2, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 132, 100, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 100, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 134, 70, 36, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 134, 70, 36, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 134, 70, 36, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 130, 66, 38, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 130, 66, 38, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 38, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 128, 70, 32, 16, 10, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 128, 70, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 70, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 194, 34, 16, 10, 6, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 194, 34, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 194, 34, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 16, 10, 1] ≤ spanCodes [256, 162, 64, 16, 10, 4, 1]
    apply step109wc281_spanCodes_le_of_gens [256, 16, 10, 1] (spanCodes [256, 162, 64, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 162, 64, 16, 10, 4, 1] n (by fin_cases hn <;> decide)

theorem o281CoverSound_wc (i : Fin 14) (M : Mat3) (h : o281Cover_wc i M) : M ∈ o281SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 68, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 228, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 228, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 32, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 32, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 66, 34, 16, 10, 4, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 66, 34, 16, 10, 4, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 130, 64, 16, 10, 6, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 64, 16, 10, 6, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 164, 96, 16, 8, 2, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 16, 8, 2, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 100, 16, 8, 2, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 100, 16, 8, 2, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 134, 70, 36, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 134, 70, 36, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 130, 66, 38, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 38, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 70, 32, 16, 10, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 70, 32, 16, 10, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 194, 34, 16, 10, 6, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 194, 34, 16, 10, 6, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 162, 64, 16, 10, 4, 1]
    unfold o281Cover_wc o281CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 162, 64, 16, 10, 4, 1] (step109wc281MatrixCodeNat M) h
    rwa [step109wc281_codeMat_matrixCode_all] at hspan

private theorem o281Cert_wc : (14 - 2) * 15 < ∑ i : Fin 14, o281Lambda_wc i * o281SourceLb_wc i := by
  simp only [o281Lambda_wc, o281SourceLb_wc]; decide
private theorem o281LambdaSum_wc : 2 ≤ ∑ i : Fin 14, o281Lambda_wc i := by
  simp only [o281Lambda_wc]; decide

theorem o281Lb16_wc
    (hSource : ∀ i : Fin 14, QuotientRankAtLeast (o281SourceU_wc i) (o281SourceLb_wc i)) :
    QuotientRankAtLeast o281W_wc 16 :=
  quotientRankAtLeast_of_contradiction o281W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o281SourceU_wc o281SourceLb_wc
      o281Lambda_wc 2 15
      o281Cover_wc o281W_le_source_wc hSource
      o281LambdaSum_wc o281CoverSound_wc
      (fun M => o281MatCoverage_wc M) (by omega) o281Cert_wc D)

end QiushiMatmul
