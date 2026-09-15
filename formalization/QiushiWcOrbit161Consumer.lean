import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 161, exact manifest basis [288, 68, 20, 10, 1]. -/
def o161W_wc : Submodule F2 Mat3 := spanCodes [288, 68, 20, 10, 1]

private theorem step109wc161_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc161MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc161_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc161MatrixCodeNat M) = M := by decide

private theorem step109wc161_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc161_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o161SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [258, 68, 34, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [262, 68, 38, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [288, 128, 68, 20, 10, 1]
  | ⟨3, _⟩ => spanCodes [288, 134, 68, 20, 10, 1]
  | ⟨4, _⟩ => spanCodes [288, 160, 68, 20, 10, 1]
  | ⟨5, _⟩ => spanCodes [288, 162, 68, 20, 10, 1]
  | ⟨6, _⟩ => spanCodes [288, 164, 68, 20, 10, 1]
  | ⟨7, _⟩ => spanCodes [288, 166, 68, 20, 10, 1]
  | ⟨8, _⟩ => spanCodes [288, 68, 20, 8, 2, 1]
  | ⟨9, _⟩ => spanCodes [256, 68, 32, 20, 10, 1]
  | ⟨10, _⟩ => spanCodes [260, 68, 36, 20, 10, 1]
  | ⟨11, _⟩ => spanCodes [288, 130, 68, 20, 10, 1]
  | ⟨12, _⟩ => spanCodes [288, 132, 68, 20, 10, 1]
  | ⟨13, _⟩ => spanCodes [288, 64, 16, 10, 4, 1]
  | ⟨14, _⟩ => spanCodes [288, 66, 18, 10, 6, 1]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o161SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14, 14, 12, 12].getD k 0

def o161Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o161CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [258, 68, 34, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 68, 38, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [288, 128, 68, 20, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [288, 134, 68, 20, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [288, 160, 68, 20, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [288, 162, 68, 20, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [288, 164, 68, 20, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [288, 166, 68, 20, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [288, 68, 20, 8, 2, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [256, 68, 32, 20, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [260, 68, 36, 20, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [288, 130, 68, 20, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [288, 132, 68, 20, 10, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [288, 64, 16, 10, 4, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [288, 66, 18, 10, 6, 1] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o161Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o161CoverB_wc i (step109wc161MatrixCodeNat M) = true

theorem o161CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 15, if o161CoverB_wc i c.val = true then o161Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o161MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o161Cover_wc i M then o161Lambda_wc i else 0 := by
  have h := o161CodeCoverage_wc ⟨step109wc161MatrixCodeNat M, step109wc161_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o161CoverB_wc i (step109wc161MatrixCodeNat M) <;> simp [o161Cover_wc, hb]

theorem o161W_le_source_wc (i : Fin 15) : o161W_wc ≤ o161SourceU_wc i := by
  fin_cases i
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [258, 68, 34, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [258, 68, 34, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 68, 34, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [262, 68, 38, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [262, 68, 38, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 68, 38, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 128, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 128, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 134, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 134, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 134, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 160, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 160, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 162, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 162, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 162, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 164, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 164, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 166, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 166, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 166, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 68, 20, 8, 2, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [256, 68, 32, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [256, 68, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [260, 68, 36, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [260, 68, 36, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 68, 36, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 130, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 130, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 130, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 132, 68, 20, 10, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 132, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 132, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 64, 16, 10, 4, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 64, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 64, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 68, 20, 10, 1] ≤ spanCodes [288, 66, 18, 10, 6, 1]
    apply step109wc161_spanCodes_le_of_gens [288, 68, 20, 10, 1] (spanCodes [288, 66, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 66, 18, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o161CoverSound_wc (i : Fin 15) (M : Mat3) (h : o161Cover_wc i M) : M ∈ o161SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [258, 68, 34, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 68, 34, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 68, 38, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 68, 38, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 128, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 128, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 134, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 134, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 162, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 162, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 164, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 164, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 166, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 166, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 68, 20, 8, 2, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 68, 20, 8, 2, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 68, 32, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 32, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 68, 36, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 68, 36, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 130, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 130, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 132, 68, 20, 10, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 132, 68, 20, 10, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 64, 16, 10, 4, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 64, 16, 10, 4, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 66, 18, 10, 6, 1]
    unfold o161Cover_wc o161CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 66, 18, 10, 6, 1] (step109wc161MatrixCodeNat M) h
    rwa [step109wc161_codeMat_matrixCode_all] at hspan

private theorem o161Cert_wc : (15 - 1) * 15 < ∑ i : Fin 15, o161Lambda_wc i * o161SourceLb_wc i := by
  simp only [o161Lambda_wc, o161SourceLb_wc]; decide
private theorem o161LambdaSum_wc : 1 ≤ ∑ i : Fin 15, o161Lambda_wc i := by
  simp only [o161Lambda_wc]; decide

theorem o161Lb16_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o161SourceU_wc i) (o161SourceLb_wc i)) :
    QuotientRankAtLeast o161W_wc 16 :=
  quotientRankAtLeast_of_contradiction o161W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o161SourceU_wc o161SourceLb_wc
      o161Lambda_wc 1 15
      o161Cover_wc o161W_le_source_wc hSource
      o161LambdaSum_wc o161CoverSound_wc
      (fun M => o161MatCoverage_wc M) (by omega) o161Cert_wc D)

end QiushiMatmul
