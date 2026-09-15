import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 114, exact manifest basis [256, 160, 8, 2, 1]. -/
def o114W_wc : Submodule F2 Mat3 := spanCodes [256, 160, 8, 2, 1]

private theorem step109wc114_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc114MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc114_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc114MatrixCodeNat M) = M := by decide

private theorem step109wc114_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc114_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o114SourceU_wc : Fin 8 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 160, 116, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [256, 132, 36, 8, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 144, 48, 8, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 160, 68, 16, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 160, 96, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [256, 160, 8, 4, 2, 1]
  | ⟨6, _⟩ => spanCodes [256, 160, 64, 8, 2, 1]
  | ⟨7, _⟩ => spanCodes [256, 128, 68, 32, 20, 8, 2, 1]
  | ⟨k + 8, h⟩ => absurd h (by omega)

def o114SourceLb_wc : Fin 8 → ℕ
  | ⟨k, _⟩ => [13, 12, 12, 12, 12, 11, 11, 9].getD k 0

def o114Lambda_wc : Fin 8 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o114CoverB_wc : Fin 8 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 160, 116, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 132, 36, 8, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 144, 48, 8, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 160, 68, 16, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 160, 96, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 160, 8, 4, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 160, 64, 8, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 128, 68, 32, 20, 8, 2, 1] c
  | ⟨k + 8, h⟩, _ => absurd h (by omega)

def o114Cover_wc (i : Fin 8) (M : Mat3) : Prop :=
  o114CoverB_wc i (step109wc114MatrixCodeNat M) = true

theorem o114CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 8, if o114CoverB_wc i c.val = true then o114Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o114MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 8, if o114Cover_wc i M then o114Lambda_wc i else 0 := by
  have h := o114CodeCoverage_wc ⟨step109wc114MatrixCodeNat M, step109wc114_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o114CoverB_wc i (step109wc114MatrixCodeNat M) <;> simp [o114Cover_wc, hb]

theorem o114W_le_source_wc (i : Fin 8) : o114W_wc ≤ o114SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 160, 116, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 160, 116, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 116, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 132, 36, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 132, 36, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 36, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 144, 48, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 144, 48, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 48, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 160, 68, 16, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 160, 96, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 160, 96, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 160, 8, 4, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 160, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 160, 64, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 160, 64, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 160, 8, 2, 1] ≤ spanCodes [256, 128, 68, 32, 20, 8, 2, 1]
    apply step109wc114_spanCodes_le_of_gens [256, 160, 8, 2, 1] (spanCodes [256, 128, 68, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o114CoverSound_wc (i : Fin 8) (M : Mat3) (h : o114Cover_wc i M) : M ∈ o114SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 160, 116, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 116, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 36, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 36, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 48, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 48, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 68, 16, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 96, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 8, 4, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 8, 4, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 64, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 68, 32, 20, 8, 2, 1]
    unfold o114Cover_wc o114CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 8, 2, 1] (step109wc114MatrixCodeNat M) h
    rwa [step109wc114_codeMat_matrixCode_all] at hspan

private theorem o114Cert_wc : (8 - 1) * 13 < ∑ i : Fin 8, o114Lambda_wc i * o114SourceLb_wc i := by
  simp only [o114Lambda_wc, o114SourceLb_wc]; decide
private theorem o114LambdaSum_wc : 1 ≤ ∑ i : Fin 8, o114Lambda_wc i := by
  simp only [o114Lambda_wc]; decide

theorem o114Lb14_wc
    (hSource : ∀ i : Fin 8, QuotientRankAtLeast (o114SourceU_wc i) (o114SourceLb_wc i)) :
    QuotientRankAtLeast o114W_wc 14 :=
  quotientRankAtLeast_of_contradiction o114W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o114SourceU_wc o114SourceLb_wc
      o114Lambda_wc 1 13
      o114Cover_wc o114W_le_source_wc hSource
      o114LambdaSum_wc o114CoverSound_wc
      (fun M => o114MatCoverage_wc M) (by omega) o114Cert_wc D)

end QiushiMatmul
