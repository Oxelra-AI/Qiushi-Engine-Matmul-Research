import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 236, exact manifest basis [262, 136, 96, 20, 1]. -/
def o236W_wc : Submodule F2 Mat3 := spanCodes [262, 136, 96, 20, 1]

private theorem step109wc236_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc236MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc236_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc236MatrixCodeNat M) = M := by decide

private theorem step109wc236_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc236_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o236SourceU_wc : Fin 13 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [262, 130, 96, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [262, 132, 96, 20, 12, 1]
  | ⟨2, _⟩ => spanCodes [262, 136, 66, 34, 20, 1]
  | ⟨3, _⟩ => spanCodes [262, 136, 68, 36, 20, 1]
  | ⟨4, _⟩ => spanCodes [260, 136, 96, 20, 2, 1]
  | ⟨5, _⟩ => spanCodes [258, 136, 96, 16, 4, 1]
  | ⟨6, _⟩ => spanCodes [262, 128, 96, 20, 8, 1]
  | ⟨7, _⟩ => spanCodes [262, 134, 96, 20, 14, 1]
  | ⟨8, _⟩ => spanCodes [262, 136, 64, 32, 20, 1]
  | ⟨9, _⟩ => spanCodes [262, 136, 70, 38, 20, 1]
  | ⟨10, _⟩ => spanCodes [262, 136, 74, 42, 20, 1]
  | ⟨11, _⟩ => spanCodes [262, 136, 76, 44, 20, 1]
  | ⟨12, _⟩ => spanCodes [256, 136, 72, 40, 18, 6, 1]
  | ⟨k + 13, h⟩ => absurd h (by omega)

def o236SourceLb_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 14, 14, 14, 14, 14, 14, 14, 14, 12].getD k 0

def o236Lambda_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o236CoverB_wc : Fin 13 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [262, 130, 96, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 132, 96, 20, 12, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [262, 136, 66, 34, 20, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [262, 136, 68, 36, 20, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [260, 136, 96, 20, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [258, 136, 96, 16, 4, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [262, 128, 96, 20, 8, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [262, 134, 96, 20, 14, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [262, 136, 64, 32, 20, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [262, 136, 70, 38, 20, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [262, 136, 74, 42, 20, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [262, 136, 76, 44, 20, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [256, 136, 72, 40, 18, 6, 1] c
  | ⟨k + 13, h⟩, _ => absurd h (by omega)

def o236Cover_wc (i : Fin 13) (M : Mat3) : Prop :=
  o236CoverB_wc i (step109wc236MatrixCodeNat M) = true

theorem o236CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 13, if o236CoverB_wc i c.val = true then o236Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o236MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 13, if o236Cover_wc i M then o236Lambda_wc i else 0 := by
  have h := o236CodeCoverage_wc ⟨step109wc236MatrixCodeNat M, step109wc236_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o236CoverB_wc i (step109wc236MatrixCodeNat M) <;> simp [o236Cover_wc, hb]

theorem o236W_le_source_wc (i : Fin 13) : o236W_wc ≤ o236SourceU_wc i := by
  fin_cases i
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 130, 96, 20, 10, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 130, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 130, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 132, 96, 20, 12, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 132, 96, 20, 12, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 132, 96, 20, 12, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 136, 66, 34, 20, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 136, 66, 34, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 66, 34, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 136, 68, 36, 20, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 136, 68, 36, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 68, 36, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [260, 136, 96, 20, 2, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [260, 136, 96, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 136, 96, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [258, 136, 96, 16, 4, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [258, 136, 96, 16, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 136, 96, 16, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 128, 96, 20, 8, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 128, 96, 20, 8, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 8, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 134, 96, 20, 14, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 134, 96, 20, 14, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 134, 96, 20, 14, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 136, 64, 32, 20, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 136, 64, 32, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 64, 32, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 136, 70, 38, 20, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 136, 70, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 70, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 136, 74, 42, 20, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 136, 74, 42, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 74, 42, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [262, 136, 76, 44, 20, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [262, 136, 76, 44, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 76, 44, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 136, 96, 20, 1] ≤ spanCodes [256, 136, 72, 40, 18, 6, 1]
    apply step109wc236_spanCodes_le_of_gens [262, 136, 96, 20, 1] (spanCodes [256, 136, 72, 40, 18, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 136, 72, 40, 18, 6, 1] n (by fin_cases hn <;> decide)

theorem o236CoverSound_wc (i : Fin 13) (M : Mat3) (h : o236Cover_wc i M) : M ∈ o236SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [262, 130, 96, 20, 10, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 130, 96, 20, 10, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 132, 96, 20, 12, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 96, 20, 12, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 66, 34, 20, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 66, 34, 20, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 68, 36, 20, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 68, 36, 20, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 136, 96, 20, 2, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 136, 96, 20, 2, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 136, 96, 16, 4, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 136, 96, 16, 4, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 96, 20, 8, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 96, 20, 8, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 134, 96, 20, 14, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 134, 96, 20, 14, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 64, 32, 20, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 64, 32, 20, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 70, 38, 20, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 70, 38, 20, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 74, 42, 20, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 74, 42, 20, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 76, 44, 20, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 76, 44, 20, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 136, 72, 40, 18, 6, 1]
    unfold o236Cover_wc o236CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 136, 72, 40, 18, 6, 1] (step109wc236MatrixCodeNat M) h
    rwa [step109wc236_codeMat_matrixCode_all] at hspan

private theorem o236Cert_wc : (13 - 1) * 15 < ∑ i : Fin 13, o236Lambda_wc i * o236SourceLb_wc i := by
  simp only [o236Lambda_wc, o236SourceLb_wc]; decide
private theorem o236LambdaSum_wc : 1 ≤ ∑ i : Fin 13, o236Lambda_wc i := by
  simp only [o236Lambda_wc]; decide

theorem o236Lb16_wc
    (hSource : ∀ i : Fin 13, QuotientRankAtLeast (o236SourceU_wc i) (o236SourceLb_wc i)) :
    QuotientRankAtLeast o236W_wc 16 :=
  quotientRankAtLeast_of_contradiction o236W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o236SourceU_wc o236SourceLb_wc
      o236Lambda_wc 1 15
      o236Cover_wc o236W_le_source_wc hSource
      o236LambdaSum_wc o236CoverSound_wc
      (fun M => o236MatCoverage_wc M) (by omega) o236Cert_wc D)

end QiushiMatmul
