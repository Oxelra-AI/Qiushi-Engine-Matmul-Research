import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 143, exact manifest basis [400, 84, 32, 2, 1]. -/
def o143W_wc : Submodule F2 Mat3 := spanCodes [400, 84, 32, 2, 1]

private theorem step109wc143_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc143MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc143_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc143MatrixCodeNat M) = M := by decide

private theorem step109wc143_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc143_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o143SourceU_wc : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [400, 84, 32, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [392, 76, 32, 24, 2, 1]
  | ⟨2, _⟩ => spanCodes [284, 140, 84, 32, 2, 1]
  | ⟨3, _⟩ => spanCodes [260, 148, 84, 32, 2, 1]
  | ⟨4, _⟩ => spanCodes [272, 128, 80, 32, 4, 2, 1]
  | ⟨5, _⟩ => spanCodes [264, 132, 72, 32, 28, 2, 1]
  | ⟨6, _⟩ => spanCodes [264, 136, 68, 32, 16, 2, 1]
  | ⟨7, _⟩ => spanCodes [268, 136, 64, 32, 20, 2, 1]
  | ⟨8, _⟩ => spanCodes [256, 144, 84, 32, 12, 2, 1]
  | ⟨k + 9, h⟩ => absurd h (by omega)

def o143SourceLb_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [12, 12, 12, 12, 9, 12, 12, 12, 12].getD k 0

def o143Lambda_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o143CoverB_wc : Fin 9 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [400, 84, 32, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [392, 76, 32, 24, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [284, 140, 84, 32, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [260, 148, 84, 32, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [272, 128, 80, 32, 4, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [264, 132, 72, 32, 28, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [264, 136, 68, 32, 16, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [268, 136, 64, 32, 20, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 144, 84, 32, 12, 2, 1] c
  | ⟨k + 9, h⟩, _ => absurd h (by omega)

def o143Cover_wc (i : Fin 9) (M : Mat3) : Prop :=
  o143CoverB_wc i (step109wc143MatrixCodeNat M) = true

theorem o143CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 9, if o143CoverB_wc i c.val = true then o143Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o143MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o143Cover_wc i M then o143Lambda_wc i else 0 := by
  have h := o143CodeCoverage_wc ⟨step109wc143MatrixCodeNat M, step109wc143_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o143CoverB_wc i (step109wc143MatrixCodeNat M) <;> simp [o143Cover_wc, hb]

theorem o143W_le_source_wc (i : Fin 9) : o143W_wc ≤ o143SourceU_wc i := by
  fin_cases i
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [400, 84, 32, 8, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [400, 84, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [400, 84, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [392, 76, 32, 24, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [392, 76, 32, 24, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [392, 76, 32, 24, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [284, 140, 84, 32, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [284, 140, 84, 32, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [284, 140, 84, 32, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [260, 148, 84, 32, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [260, 148, 84, 32, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 148, 84, 32, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [272, 128, 80, 32, 4, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [272, 128, 80, 32, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 32, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [264, 132, 72, 32, 28, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [264, 132, 72, 32, 28, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 132, 72, 32, 28, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [264, 136, 68, 32, 16, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [264, 136, 68, 32, 16, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 136, 68, 32, 16, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [268, 136, 64, 32, 20, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [268, 136, 64, 32, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [268, 136, 64, 32, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [400, 84, 32, 2, 1] ≤ spanCodes [256, 144, 84, 32, 12, 2, 1]
    apply step109wc143_spanCodes_le_of_gens [400, 84, 32, 2, 1] (spanCodes [256, 144, 84, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 84, 32, 12, 2, 1] n (by fin_cases hn <;> decide)

theorem o143CoverSound_wc (i : Fin 9) (M : Mat3) (h : o143Cover_wc i M) : M ∈ o143SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [400, 84, 32, 8, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [400, 84, 32, 8, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [392, 76, 32, 24, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [392, 76, 32, 24, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [284, 140, 84, 32, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [284, 140, 84, 32, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 148, 84, 32, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 148, 84, 32, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 80, 32, 4, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 32, 4, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 132, 72, 32, 28, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 132, 72, 32, 28, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 136, 68, 32, 16, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 136, 68, 32, 16, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [268, 136, 64, 32, 20, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [268, 136, 64, 32, 20, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 84, 32, 12, 2, 1]
    unfold o143Cover_wc o143CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 84, 32, 12, 2, 1] (step109wc143MatrixCodeNat M) h
    rwa [step109wc143_codeMat_matrixCode_all] at hspan

private theorem o143Cert_wc : (9 - 1) * 13 < ∑ i : Fin 9, o143Lambda_wc i * o143SourceLb_wc i := by
  simp only [o143Lambda_wc, o143SourceLb_wc]; decide
private theorem o143LambdaSum_wc : 1 ≤ ∑ i : Fin 9, o143Lambda_wc i := by
  simp only [o143Lambda_wc]; decide

theorem o143Lb14_wc
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o143SourceU_wc i) (o143SourceLb_wc i)) :
    QuotientRankAtLeast o143W_wc 14 :=
  quotientRankAtLeast_of_contradiction o143W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o143SourceU_wc o143SourceLb_wc
      o143Lambda_wc 1 13
      o143Cover_wc o143W_le_source_wc hSource
      o143LambdaSum_wc o143CoverSound_wc
      (fun M => o143MatCoverage_wc M) (by omega) o143Cert_wc D)

end QiushiMatmul
