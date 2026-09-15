import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 75, exact manifest basis [262, 160, 68, 20, 10, 1]. -/
def o75W_wc : Submodule F2 Mat3 := spanCodes [262, 160, 68, 20, 10, 1]

private theorem step109wc75_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc75MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc75_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc75MatrixCodeNat M) = M := by decide

private theorem step109wc75_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc75_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o75SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [262, 128, 68, 32, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [262, 130, 68, 34, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [262, 132, 68, 36, 20, 10, 1]
  | ⟨3, _⟩ => spanCodes [262, 134, 68, 38, 20, 10, 1]
  | ⟨4, _⟩ => spanCodes [260, 160, 68, 20, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [258, 160, 64, 16, 10, 4, 1]
  | ⟨6, _⟩ => spanCodes [256, 160, 66, 18, 10, 6, 1]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o75SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 12, 12, 12].getD k 0

def o75Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o75CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [262, 128, 68, 32, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 130, 68, 34, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [262, 132, 68, 36, 20, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [262, 134, 68, 38, 20, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [260, 160, 68, 20, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [258, 160, 64, 16, 10, 4, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 160, 66, 18, 10, 6, 1] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o75Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o75CoverB_wc i (step109wc75MatrixCodeNat M) = true

theorem o75CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o75CoverB_wc i c.val = true then o75Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o75MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o75Cover_wc i M then o75Lambda_wc i else 0 := by
  have h := o75CodeCoverage_wc ⟨step109wc75MatrixCodeNat M, step109wc75_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o75CoverB_wc i (step109wc75MatrixCodeNat M) <;> simp [o75Cover_wc, hb]

theorem o75W_le_source_wc (i : Fin 7) : o75W_wc ≤ o75SourceU_wc i := by
  fin_cases i
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [262, 128, 68, 32, 20, 10, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [262, 128, 68, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [262, 130, 68, 34, 20, 10, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [262, 130, 68, 34, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 34, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [262, 132, 68, 36, 20, 10, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [262, 132, 68, 36, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 132, 68, 36, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [262, 134, 68, 38, 20, 10, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [262, 134, 68, 38, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 134, 68, 38, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [260, 160, 68, 20, 8, 2, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [260, 160, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [258, 160, 64, 16, 10, 4, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [258, 160, 64, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 160, 64, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 160, 68, 20, 10, 1] ≤ spanCodes [256, 160, 66, 18, 10, 6, 1]
    apply step109wc75_spanCodes_le_of_gens [262, 160, 68, 20, 10, 1] (spanCodes [256, 160, 66, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 18, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o75CoverSound_wc (i : Fin 7) (M : Mat3) (h : o75Cover_wc i M) : M ∈ o75SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [262, 128, 68, 32, 20, 10, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 20, 10, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 130, 68, 34, 20, 10, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 34, 20, 10, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 132, 68, 36, 20, 10, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 68, 36, 20, 10, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 134, 68, 38, 20, 10, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 134, 68, 38, 20, 10, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 160, 68, 20, 8, 2, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 20, 8, 2, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 160, 64, 16, 10, 4, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 160, 64, 16, 10, 4, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 66, 18, 10, 6, 1]
    unfold o75Cover_wc o75CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 66, 18, 10, 6, 1] (step109wc75MatrixCodeNat M) h
    rwa [step109wc75_codeMat_matrixCode_all] at hspan

private theorem o75Cert_wc : (7 - 1) * 15 < ∑ i : Fin 7, o75Lambda_wc i * o75SourceLb_wc i := by
  simp only [o75Lambda_wc, o75SourceLb_wc]; decide
private theorem o75LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o75Lambda_wc i := by
  simp only [o75Lambda_wc]; decide

theorem o75Lb16_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o75SourceU_wc i) (o75SourceLb_wc i)) :
    QuotientRankAtLeast o75W_wc 16 :=
  quotientRankAtLeast_of_contradiction o75W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o75SourceU_wc o75SourceLb_wc
      o75Lambda_wc 1 15
      o75Cover_wc o75W_le_source_wc hSource
      o75LambdaSum_wc o75CoverSound_wc
      (fun M => o75MatCoverage_wc M) (by omega) o75Cert_wc D)

end QiushiMatmul
