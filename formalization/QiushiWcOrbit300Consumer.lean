import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 300, exact manifest basis [160, 68, 10, 1]. -/
def o300W_wc : Submodule F2 Mat3 := spanCodes [160, 68, 10, 1]

private theorem step109wc300_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc300MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc300_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc300MatrixCodeNat M) = M := by decide

private theorem step109wc300_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc300_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o300SourceU_wc : Fin 10 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [160, 68, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [262, 160, 68, 10, 1]
  | ⟨2, _⟩ => spanCodes [274, 160, 68, 10, 1]
  | ⟨3, _⟩ => spanCodes [160, 68, 16, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 160, 64, 10, 4, 1]
  | ⟨5, _⟩ => spanCodes [272, 160, 66, 10, 6, 1]
  | ⟨6, _⟩ => spanCodes [258, 132, 68, 36, 22, 10, 1]
  | ⟨7, _⟩ => spanCodes [258, 134, 68, 38, 22, 10, 1]
  | ⟨8, _⟩ => spanCodes [258, 128, 68, 32, 22, 10, 1]
  | ⟨9, _⟩ => spanCodes [258, 130, 68, 34, 22, 10, 1]
  | ⟨k + 10, h⟩ => absurd h (by omega)

def o300SourceLb_wc : Fin 10 → ℕ
  | ⟨k, _⟩ => [16, 16, 16, 15, 15, 15, 14, 14, 14, 14].getD k 0

def o300Lambda_wc : Fin 10 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o300CoverB_wc : Fin 10 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [160, 68, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 160, 68, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [274, 160, 68, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [160, 68, 16, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 160, 64, 10, 4, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [272, 160, 66, 10, 6, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [258, 132, 68, 36, 22, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [258, 134, 68, 38, 22, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [258, 128, 68, 32, 22, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [258, 130, 68, 34, 22, 10, 1] c
  | ⟨k + 10, h⟩, _ => absurd h (by omega)

def o300Cover_wc (i : Fin 10) (M : Mat3) : Prop :=
  o300CoverB_wc i (step109wc300MatrixCodeNat M) = true

theorem o300CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 10, if o300CoverB_wc i c.val = true then o300Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o300MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 10, if o300Cover_wc i M then o300Lambda_wc i else 0 := by
  have h := o300CodeCoverage_wc ⟨step109wc300MatrixCodeNat M, step109wc300_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o300CoverB_wc i (step109wc300MatrixCodeNat M) <;> simp [o300Cover_wc, hb]

theorem o300W_le_source_wc (i : Fin 10) : o300W_wc ≤ o300SourceU_wc i := by
  fin_cases i
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [160, 68, 20, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [160, 68, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [262, 160, 68, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [262, 160, 68, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [274, 160, 68, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [274, 160, 68, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 160, 68, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [160, 68, 16, 8, 2, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [256, 160, 64, 10, 4, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [256, 160, 64, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [272, 160, 66, 10, 6, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [272, 160, 66, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 160, 66, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [258, 132, 68, 36, 22, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [258, 132, 68, 36, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 132, 68, 36, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [258, 134, 68, 38, 22, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [258, 134, 68, 38, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 134, 68, 38, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [258, 128, 68, 32, 22, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [258, 128, 68, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 68, 32, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 10, 1] ≤ spanCodes [258, 130, 68, 34, 22, 10, 1]
    apply step109wc300_spanCodes_le_of_gens [160, 68, 10, 1] (spanCodes [258, 130, 68, 34, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 68, 34, 22, 10, 1] n (by fin_cases hn <;> decide)

theorem o300CoverSound_wc (i : Fin 10) (M : Mat3) (h : o300Cover_wc i M) : M ∈ o300SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [160, 68, 20, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [160, 68, 20, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 160, 68, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 160, 68, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 160, 68, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [160, 68, 16, 8, 2, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [160, 68, 16, 8, 2, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 64, 10, 4, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 10, 4, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 160, 66, 10, 6, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 160, 66, 10, 6, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 132, 68, 36, 22, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 132, 68, 36, 22, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 134, 68, 38, 22, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 134, 68, 38, 22, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 68, 32, 22, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 68, 32, 22, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 130, 68, 34, 22, 10, 1]
    unfold o300Cover_wc o300CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 68, 34, 22, 10, 1] (step109wc300MatrixCodeNat M) h
    rwa [step109wc300_codeMat_matrixCode_all] at hspan

private theorem o300Cert_wc : (10 - 1) * 16 < ∑ i : Fin 10, o300Lambda_wc i * o300SourceLb_wc i := by
  simp only [o300Lambda_wc, o300SourceLb_wc]; decide
private theorem o300LambdaSum_wc : 1 ≤ ∑ i : Fin 10, o300Lambda_wc i := by
  simp only [o300Lambda_wc]; decide

theorem o300Lb17_wc
    (hSource : ∀ i : Fin 10, QuotientRankAtLeast (o300SourceU_wc i) (o300SourceLb_wc i)) :
    QuotientRankAtLeast o300W_wc 17 :=
  quotientRankAtLeast_of_contradiction o300W_wc 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o300SourceU_wc o300SourceLb_wc
      o300Lambda_wc 1 16
      o300Cover_wc o300W_le_source_wc hSource
      o300LambdaSum_wc o300CoverSound_wc
      (fun M => o300MatCoverage_wc M) (by omega) o300Cert_wc D)

end QiushiMatmul
