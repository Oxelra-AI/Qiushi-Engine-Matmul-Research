import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 322, exact manifest basis [308, 160, 10, 1]. -/
def o322W_wc : Submodule F2 Mat3 := spanCodes [308, 160, 10, 1]

private theorem step109wc322_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc322MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc322_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc322MatrixCodeNat M) = M := by decide

private theorem step109wc322_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc322_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o322SourceU_wc : Fin 14 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [290, 160, 22, 10, 1]
  | ⟨1, _⟩ => spanCodes [274, 134, 38, 10, 1]
  | ⟨2, _⟩ => spanCodes [258, 150, 54, 10, 1]
  | ⟨3, _⟩ => spanCodes [308, 160, 80, 10, 1]
  | ⟨4, _⟩ => spanCodes [308, 160, 98, 10, 1]
  | ⟨5, _⟩ => spanCodes [308, 160, 102, 10, 1]
  | ⟨6, _⟩ => spanCodes [308, 160, 114, 10, 1]
  | ⟨7, _⟩ => spanCodes [308, 160, 116, 10, 1]
  | ⟨8, _⟩ => spanCodes [278, 130, 34, 10, 1]
  | ⟨9, _⟩ => spanCodes [260, 144, 48, 10, 1]
  | ⟨10, _⟩ => spanCodes [288, 160, 70, 20, 10, 1]
  | ⟨11, _⟩ => spanCodes [292, 160, 68, 16, 8, 2, 1]
  | ⟨12, _⟩ => spanCodes [272, 128, 64, 32, 10, 4, 1]
  | ⟨13, _⟩ => spanCodes [256, 146, 66, 50, 10, 6, 1]
  | ⟨k + 14, h⟩ => absurd h (by omega)

def o322SourceLb_wc : Fin 14 → ℕ
  | ⟨k, _⟩ => [16, 16, 16, 16, 16, 16, 16, 16, 15, 15, 15, 12, 12, 12].getD k 0

def o322Lambda_wc : Fin 14 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o322CoverB_wc : Fin 14 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [290, 160, 22, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [274, 134, 38, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [258, 150, 54, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [308, 160, 80, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [308, 160, 98, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [308, 160, 102, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [308, 160, 114, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [308, 160, 116, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [278, 130, 34, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [260, 144, 48, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [288, 160, 70, 20, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [292, 160, 68, 16, 8, 2, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [272, 128, 64, 32, 10, 4, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [256, 146, 66, 50, 10, 6, 1] c
  | ⟨k + 14, h⟩, _ => absurd h (by omega)

def o322Cover_wc (i : Fin 14) (M : Mat3) : Prop :=
  o322CoverB_wc i (step109wc322MatrixCodeNat M) = true

theorem o322CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 14, if o322CoverB_wc i c.val = true then o322Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o322MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 14, if o322Cover_wc i M then o322Lambda_wc i else 0 := by
  have h := o322CodeCoverage_wc ⟨step109wc322MatrixCodeNat M, step109wc322_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o322CoverB_wc i (step109wc322MatrixCodeNat M) <;> simp [o322Cover_wc, hb]

theorem o322W_le_source_wc (i : Fin 14) : o322W_wc ≤ o322SourceU_wc i := by
  fin_cases i
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [290, 160, 22, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [290, 160, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [290, 160, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [274, 134, 38, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [274, 134, 38, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 134, 38, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [258, 150, 54, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [258, 150, 54, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 150, 54, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [308, 160, 80, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [308, 160, 80, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 160, 80, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [308, 160, 98, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [308, 160, 98, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 160, 98, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [308, 160, 102, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [308, 160, 102, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 160, 102, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [308, 160, 114, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [308, 160, 114, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 160, 114, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [308, 160, 116, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [308, 160, 116, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 160, 116, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [278, 130, 34, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [278, 130, 34, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 130, 34, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [260, 144, 48, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [260, 144, 48, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 144, 48, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [288, 160, 70, 20, 10, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [288, 160, 70, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 70, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [292, 160, 68, 16, 8, 2, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [292, 160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [272, 128, 64, 32, 10, 4, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [272, 128, 64, 32, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [308, 160, 10, 1] ≤ spanCodes [256, 146, 66, 50, 10, 6, 1]
    apply step109wc322_spanCodes_le_of_gens [308, 160, 10, 1] (spanCodes [256, 146, 66, 50, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 146, 66, 50, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o322CoverSound_wc (i : Fin 14) (M : Mat3) (h : o322Cover_wc i M) : M ∈ o322SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [290, 160, 22, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [290, 160, 22, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 134, 38, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 134, 38, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 150, 54, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 150, 54, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [308, 160, 80, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [308, 160, 80, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [308, 160, 98, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [308, 160, 98, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [308, 160, 102, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [308, 160, 102, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [308, 160, 114, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [308, 160, 114, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [308, 160, 116, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [308, 160, 116, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [278, 130, 34, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 130, 34, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 144, 48, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 144, 48, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 70, 20, 10, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 70, 20, 10, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 160, 68, 16, 8, 2, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 16, 8, 2, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 64, 32, 10, 4, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 10, 4, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 146, 66, 50, 10, 6, 1]
    unfold o322Cover_wc o322CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 146, 66, 50, 10, 6, 1] (step109wc322MatrixCodeNat M) h
    rwa [step109wc322_codeMat_matrixCode_all] at hspan

private theorem o322Cert_wc : (14 - 1) * 16 < ∑ i : Fin 14, o322Lambda_wc i * o322SourceLb_wc i := by
  simp only [o322Lambda_wc, o322SourceLb_wc]; decide
private theorem o322LambdaSum_wc : 1 ≤ ∑ i : Fin 14, o322Lambda_wc i := by
  simp only [o322Lambda_wc]; decide

theorem o322Lb17_wc
    (hSource : ∀ i : Fin 14, QuotientRankAtLeast (o322SourceU_wc i) (o322SourceLb_wc i)) :
    QuotientRankAtLeast o322W_wc 17 :=
  quotientRankAtLeast_of_contradiction o322W_wc 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o322SourceU_wc o322SourceLb_wc
      o322Lambda_wc 1 16
      o322Cover_wc o322W_le_source_wc hSource
      o322LambdaSum_wc o322CoverSound_wc
      (fun M => o322MatCoverage_wc M) (by omega) o322Cert_wc D)

end QiushiMatmul
