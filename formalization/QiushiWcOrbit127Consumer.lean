import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 127, exact manifest basis [272, 96, 12, 2, 1]. -/
def o127W_wc : Submodule F2 Mat3 := spanCodes [272, 96, 12, 2, 1]

private theorem step109wc127_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc127MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc127_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc127MatrixCodeNat M) = M := by decide

private theorem step109wc127_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc127_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o127SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [272, 132, 96, 12, 2, 1]
  | ⟨1, _⟩ => spanCodes [272, 164, 96, 12, 2, 1]
  | ⟨2, _⟩ => spanCodes [272, 64, 32, 12, 2, 1]
  | ⟨3, _⟩ => spanCodes [272, 148, 84, 52, 12, 2, 1]
  | ⟨4, _⟩ => spanCodes [272, 128, 80, 48, 12, 2, 1]
  | ⟨5, _⟩ => spanCodes [272, 144, 68, 36, 12, 2, 1]
  | ⟨6, _⟩ => spanCodes [256, 96, 16, 8, 4, 2, 1]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o127SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [14, 14, 13, 12, 12, 12, 9].getD k 0

def o127Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o127CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [272, 132, 96, 12, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [272, 164, 96, 12, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [272, 64, 32, 12, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [272, 148, 84, 52, 12, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [272, 128, 80, 48, 12, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [272, 144, 68, 36, 12, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 96, 16, 8, 4, 2, 1] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o127Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o127CoverB_wc i (step109wc127MatrixCodeNat M) = true

theorem o127CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o127CoverB_wc i c.val = true then o127Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o127MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o127Cover_wc i M then o127Lambda_wc i else 0 := by
  have h := o127CodeCoverage_wc ⟨step109wc127MatrixCodeNat M, step109wc127_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o127CoverB_wc i (step109wc127MatrixCodeNat M) <;> simp [o127Cover_wc, hb]

theorem o127W_le_source_wc (i : Fin 7) : o127W_wc ≤ o127SourceU_wc i := by
  fin_cases i
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [272, 132, 96, 12, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [272, 132, 96, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [272, 164, 96, 12, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [272, 164, 96, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 164, 96, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [272, 64, 32, 12, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [272, 64, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [272, 148, 84, 52, 12, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [272, 148, 84, 52, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 148, 84, 52, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [272, 128, 80, 48, 12, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [272, 128, 80, 48, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 48, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [272, 144, 68, 36, 12, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [272, 144, 68, 36, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 36, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 96, 12, 2, 1] ≤ spanCodes [256, 96, 16, 8, 4, 2, 1]
    apply step109wc127_spanCodes_le_of_gens [272, 96, 12, 2, 1] (spanCodes [256, 96, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o127CoverSound_wc (i : Fin 7) (M : Mat3) (h : o127Cover_wc i M) : M ∈ o127SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [272, 132, 96, 12, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 96, 12, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 164, 96, 12, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 164, 96, 12, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 64, 32, 12, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 12, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 148, 84, 52, 12, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 148, 84, 52, 12, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 80, 48, 12, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 80, 48, 12, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 144, 68, 36, 12, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 36, 12, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 96, 16, 8, 4, 2, 1]
    unfold o127Cover_wc o127CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 8, 4, 2, 1] (step109wc127MatrixCodeNat M) h
    rwa [step109wc127_codeMat_matrixCode_all] at hspan

private theorem o127Cert_wc : (7 - 1) * 14 < ∑ i : Fin 7, o127Lambda_wc i * o127SourceLb_wc i := by
  simp only [o127Lambda_wc, o127SourceLb_wc]; decide
private theorem o127LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o127Lambda_wc i := by
  simp only [o127Lambda_wc]; decide

theorem o127Lb15_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o127SourceU_wc i) (o127SourceLb_wc i)) :
    QuotientRankAtLeast o127W_wc 15 :=
  quotientRankAtLeast_of_contradiction o127W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o127SourceU_wc o127SourceLb_wc
      o127Lambda_wc 1 14
      o127Cover_wc o127W_le_source_wc hSource
      o127LambdaSum_wc o127CoverSound_wc
      (fun M => o127MatCoverage_wc M) (by omega) o127Cert_wc D)

end QiushiMatmul
