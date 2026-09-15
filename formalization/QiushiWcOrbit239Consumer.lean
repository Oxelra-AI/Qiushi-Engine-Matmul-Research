import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 239, exact manifest basis [262, 160, 68, 19, 10]. -/
def o239W_wc : Submodule F2 Mat3 := spanCodes [262, 160, 68, 19, 10]

private theorem step109wc239_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc239MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc239_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc239MatrixCodeNat M) = M := by decide

private theorem step109wc239_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc239_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o239SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [262, 160, 68, 18, 10, 1]
  | ⟨1, _⟩ => spanCodes [258, 160, 64, 19, 10, 4]
  | ⟨2, _⟩ => spanCodes [259, 160, 65, 19, 10, 5]
  | ⟨3, _⟩ => spanCodes [256, 160, 66, 19, 10, 6]
  | ⟨4, _⟩ => spanCodes [257, 160, 67, 19, 10, 7]
  | ⟨5, _⟩ => spanCodes [262, 129, 68, 33, 19, 10]
  | ⟨6, _⟩ => spanCodes [262, 131, 68, 35, 19, 10]
  | ⟨7, _⟩ => spanCodes [262, 132, 68, 36, 19, 10]
  | ⟨8, _⟩ => spanCodes [262, 135, 68, 39, 19, 10]
  | ⟨9, _⟩ => spanCodes [260, 160, 68, 17, 8, 2]
  | ⟨10, _⟩ => spanCodes [261, 160, 68, 16, 9, 3]
  | ⟨11, _⟩ => spanCodes [262, 128, 68, 32, 19, 10]
  | ⟨12, _⟩ => spanCodes [262, 130, 68, 34, 19, 10]
  | ⟨13, _⟩ => spanCodes [262, 133, 68, 37, 19, 10]
  | ⟨14, _⟩ => spanCodes [262, 134, 68, 38, 19, 10]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o239SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14, 14, 14].getD k 0

def o239Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o239CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [262, 160, 68, 18, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [258, 160, 64, 19, 10, 4] c
  | ⟨2, _⟩, c => spanContainsCodeCore [259, 160, 65, 19, 10, 5] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 160, 66, 19, 10, 6] c
  | ⟨4, _⟩, c => spanContainsCodeCore [257, 160, 67, 19, 10, 7] c
  | ⟨5, _⟩, c => spanContainsCodeCore [262, 129, 68, 33, 19, 10] c
  | ⟨6, _⟩, c => spanContainsCodeCore [262, 131, 68, 35, 19, 10] c
  | ⟨7, _⟩, c => spanContainsCodeCore [262, 132, 68, 36, 19, 10] c
  | ⟨8, _⟩, c => spanContainsCodeCore [262, 135, 68, 39, 19, 10] c
  | ⟨9, _⟩, c => spanContainsCodeCore [260, 160, 68, 17, 8, 2] c
  | ⟨10, _⟩, c => spanContainsCodeCore [261, 160, 68, 16, 9, 3] c
  | ⟨11, _⟩, c => spanContainsCodeCore [262, 128, 68, 32, 19, 10] c
  | ⟨12, _⟩, c => spanContainsCodeCore [262, 130, 68, 34, 19, 10] c
  | ⟨13, _⟩, c => spanContainsCodeCore [262, 133, 68, 37, 19, 10] c
  | ⟨14, _⟩, c => spanContainsCodeCore [262, 134, 68, 38, 19, 10] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o239Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o239CoverB_wc i (step109wc239MatrixCodeNat M) = true

theorem o239CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 15, if o239CoverB_wc i c.val = true then o239Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o239MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o239Cover_wc i M then o239Lambda_wc i else 0 := by
  have h := o239CodeCoverage_wc ⟨step109wc239MatrixCodeNat M, step109wc239_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o239CoverB_wc i (step109wc239MatrixCodeNat M) <;> simp [o239Cover_wc, hb]

theorem o239W_le_source_wc (i : Fin 15) : o239W_wc ≤ o239SourceU_wc i := by
  fin_cases i
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 160, 68, 18, 10, 1]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 160, 68, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [258, 160, 64, 19, 10, 4]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [258, 160, 64, 19, 10, 4])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 160, 64, 19, 10, 4] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [259, 160, 65, 19, 10, 5]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [259, 160, 65, 19, 10, 5])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [259, 160, 65, 19, 10, 5] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [256, 160, 66, 19, 10, 6]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [256, 160, 66, 19, 10, 6])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 19, 10, 6] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [257, 160, 67, 19, 10, 7]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [257, 160, 67, 19, 10, 7])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 160, 67, 19, 10, 7] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 129, 68, 33, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 129, 68, 33, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 129, 68, 33, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 131, 68, 35, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 131, 68, 35, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 132, 68, 36, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 132, 68, 36, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 132, 68, 36, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 135, 68, 39, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 135, 68, 39, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 135, 68, 39, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [260, 160, 68, 17, 8, 2]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [260, 160, 68, 17, 8, 2])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 17, 8, 2] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [261, 160, 68, 16, 9, 3]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [261, 160, 68, 16, 9, 3])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [261, 160, 68, 16, 9, 3] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 128, 68, 32, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 128, 68, 32, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 130, 68, 34, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 130, 68, 34, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 34, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 133, 68, 37, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 133, 68, 37, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 133, 68, 37, 19, 10] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 19, 10] ≤ spanCodes [262, 134, 68, 38, 19, 10]
    apply step109wc239_spanCodes_le_of_gens [262, 160, 68, 19, 10] (spanCodes [262, 134, 68, 38, 19, 10])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 134, 68, 38, 19, 10] n (by fin_cases hn <;> decide)

theorem o239CoverSound_wc (i : Fin 15) (M : Mat3) (h : o239Cover_wc i M) : M ∈ o239SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [262, 160, 68, 18, 10, 1]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 18, 10, 1] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 160, 64, 19, 10, 4]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 160, 64, 19, 10, 4] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [259, 160, 65, 19, 10, 5]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 160, 65, 19, 10, 5] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 66, 19, 10, 6]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 19, 10, 6] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [257, 160, 67, 19, 10, 7]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 160, 67, 19, 10, 7] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 129, 68, 33, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 129, 68, 33, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 131, 68, 35, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 131, 68, 35, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 132, 68, 36, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 68, 36, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 135, 68, 39, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 135, 68, 39, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 160, 68, 17, 8, 2]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 17, 8, 2] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [261, 160, 68, 16, 9, 3]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [261, 160, 68, 16, 9, 3] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 68, 32, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 130, 68, 34, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 34, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 133, 68, 37, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 133, 68, 37, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 134, 68, 38, 19, 10]
    unfold o239Cover_wc o239CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 134, 68, 38, 19, 10] (step109wc239MatrixCodeNat M) h
    rwa [step109wc239_codeMat_matrixCode_all] at hspan

private theorem o239Cert_wc : (15 - 1) * 15 < ∑ i : Fin 15, o239Lambda_wc i * o239SourceLb_wc i := by
  simp only [o239Lambda_wc, o239SourceLb_wc]; decide
private theorem o239LambdaSum_wc : 1 ≤ ∑ i : Fin 15, o239Lambda_wc i := by
  simp only [o239Lambda_wc]; decide

theorem o239Lb16_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o239SourceU_wc i) (o239SourceLb_wc i)) :
    QuotientRankAtLeast o239W_wc 16 :=
  quotientRankAtLeast_of_contradiction o239W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o239SourceU_wc o239SourceLb_wc
      o239Lambda_wc 1 15
      o239Cover_wc o239W_le_source_wc hSource
      o239LambdaSum_wc o239CoverSound_wc
      (fun M => o239MatCoverage_wc M) (by omega) o239Cert_wc D)

end QiushiMatmul
