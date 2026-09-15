import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 214, exact manifest basis [278, 132, 96, 10, 1]. -/
def o214W_wc : Submodule F2 Mat3 := spanCodes [278, 132, 96, 10, 1]

private theorem step109wc214_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc214MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc214_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc214MatrixCodeNat M) = M := by decide

private theorem step109wc214_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc214_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o214SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [278, 132, 80, 48, 10, 1]
  | ⟨1, _⟩ => spanCodes [274, 128, 96, 10, 4, 1]
  | ⟨2, _⟩ => spanCodes [278, 132, 84, 52, 10, 1]
  | ⟨3, _⟩ => spanCodes [260, 132, 96, 16, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [272, 130, 66, 34, 10, 6, 1]
  | ⟨5, _⟩ => spanCodes [258, 132, 70, 38, 20, 10, 1]
  | ⟨6, _⟩ => spanCodes [256, 132, 64, 32, 22, 10, 1]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o214SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [15, 14, 14, 12, 12, 12, 12].getD k 0

def o214Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o214CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [278, 132, 80, 48, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [274, 128, 96, 10, 4, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [278, 132, 84, 52, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [260, 132, 96, 16, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [272, 130, 66, 34, 10, 6, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [258, 132, 70, 38, 20, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 132, 64, 32, 22, 10, 1] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o214Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o214CoverB_wc i (step109wc214MatrixCodeNat M) = true

theorem o214CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o214CoverB_wc i c.val = true then o214Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o214MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o214Cover_wc i M then o214Lambda_wc i else 0 := by
  have h := o214CodeCoverage_wc ⟨step109wc214MatrixCodeNat M, step109wc214_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o214CoverB_wc i (step109wc214MatrixCodeNat M) <;> simp [o214Cover_wc, hb]

theorem o214W_le_source_wc (i : Fin 7) : o214W_wc ≤ o214SourceU_wc i := by
  fin_cases i
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [278, 132, 80, 48, 10, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [278, 132, 80, 48, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 132, 80, 48, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [274, 128, 96, 10, 4, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [274, 128, 96, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 128, 96, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [278, 132, 84, 52, 10, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [278, 132, 84, 52, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 132, 84, 52, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [260, 132, 96, 16, 8, 2, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [260, 132, 96, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [272, 130, 66, 34, 10, 6, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [272, 130, 66, 34, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 130, 66, 34, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [258, 132, 70, 38, 20, 10, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [258, 132, 70, 38, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 132, 70, 38, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [278, 132, 96, 10, 1] ≤ spanCodes [256, 132, 64, 32, 22, 10, 1]
    apply step109wc214_spanCodes_le_of_gens [278, 132, 96, 10, 1] (spanCodes [256, 132, 64, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 22, 10, 1] n (by fin_cases hn <;> decide)

theorem o214CoverSound_wc (i : Fin 7) (M : Mat3) (h : o214Cover_wc i M) : M ∈ o214SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [278, 132, 80, 48, 10, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 80, 48, 10, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 128, 96, 10, 4, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 128, 96, 10, 4, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [278, 132, 84, 52, 10, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 132, 84, 52, 10, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 132, 96, 16, 8, 2, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 16, 8, 2, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 130, 66, 34, 10, 6, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 130, 66, 34, 10, 6, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 132, 70, 38, 20, 10, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 132, 70, 38, 20, 10, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 64, 32, 22, 10, 1]
    unfold o214Cover_wc o214CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 22, 10, 1] (step109wc214MatrixCodeNat M) h
    rwa [step109wc214_codeMat_matrixCode_all] at hspan

private theorem o214Cert_wc : (7 - 1) * 15 < ∑ i : Fin 7, o214Lambda_wc i * o214SourceLb_wc i := by
  simp only [o214Lambda_wc, o214SourceLb_wc]; decide
private theorem o214LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o214Lambda_wc i := by
  simp only [o214Lambda_wc]; decide

theorem o214Lb16_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o214SourceU_wc i) (o214SourceLb_wc i)) :
    QuotientRankAtLeast o214W_wc 16 :=
  quotientRankAtLeast_of_contradiction o214W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o214SourceU_wc o214SourceLb_wc
      o214Lambda_wc 1 15
      o214Cover_wc o214W_le_source_wc hSource
      o214LambdaSum_wc o214CoverSound_wc
      (fun M => o214MatCoverage_wc M) (by omega) o214Cert_wc D)

end QiushiMatmul
