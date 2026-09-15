import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 197, exact manifest basis [324, 132, 32, 10, 1]. -/
def o197W_wc : Submodule F2 Mat3 := spanCodes [324, 132, 32, 10, 1]

private theorem step109wc197_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc197MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc197_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc197MatrixCodeNat M) = M := by decide

private theorem step109wc197_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc197_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o197SourceU_wc : Fin 13 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [262, 132, 66, 32, 10, 1]
  | ⟨1, _⟩ => spanCodes [258, 132, 70, 32, 10, 1]
  | ⟨2, _⟩ => spanCodes [276, 132, 80, 32, 10, 1]
  | ⟨3, _⟩ => spanCodes [272, 132, 84, 32, 10, 1]
  | ⟨4, _⟩ => spanCodes [324, 132, 32, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [322, 130, 32, 10, 6, 1]
  | ⟨6, _⟩ => spanCodes [260, 132, 64, 32, 10, 1]
  | ⟨7, _⟩ => spanCodes [256, 132, 68, 32, 18, 10, 1]
  | ⟨8, _⟩ => spanCodes [274, 128, 82, 32, 10, 4, 1]
  | ⟨9, _⟩ => spanCodes [256, 132, 68, 32, 20, 8, 2, 1]
  | ⟨10, _⟩ => spanCodes [256, 130, 66, 32, 16, 10, 6, 1]
  | ⟨11, _⟩ => spanCodes [258, 128, 66, 32, 16, 10, 4, 1]
  | ⟨12, _⟩ => spanCodes [320, 128, 32, 16, 8, 4, 2, 1]
  | ⟨k + 13, h⟩ => absurd h (by omega)

def o197SourceLb_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 12, 12, 12, 12, 12, 9, 9, 9, 3].getD k 0

def o197Lambda_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [2, 2, 3, 3, 1, 1, 4, 2, 1, 1, 1, 1, 2].getD k 0

def o197CoverB_wc : Fin 13 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [262, 132, 66, 32, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [258, 132, 70, 32, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [276, 132, 80, 32, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [272, 132, 84, 32, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [324, 132, 32, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [322, 130, 32, 10, 6, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [260, 132, 64, 32, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 132, 68, 32, 18, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [274, 128, 82, 32, 10, 4, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [256, 132, 68, 32, 20, 8, 2, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [256, 130, 66, 32, 16, 10, 6, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [258, 128, 66, 32, 16, 10, 4, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [320, 128, 32, 16, 8, 4, 2, 1] c
  | ⟨k + 13, h⟩, _ => absurd h (by omega)

def o197Cover_wc (i : Fin 13) (M : Mat3) : Prop :=
  o197CoverB_wc i (step109wc197MatrixCodeNat M) = true

theorem o197CodeCoverage_wc (c : Fin 512) :
    4 ≤ ∑ i : Fin 13, if o197CoverB_wc i c.val = true then o197Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o197MatCoverage_wc (M : Mat3) :
    4 ≤ ∑ i : Fin 13, if o197Cover_wc i M then o197Lambda_wc i else 0 := by
  have h := o197CodeCoverage_wc ⟨step109wc197MatrixCodeNat M, step109wc197_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o197CoverB_wc i (step109wc197MatrixCodeNat M) <;> simp [o197Cover_wc, hb]

theorem o197W_le_source_wc (i : Fin 13) : o197W_wc ≤ o197SourceU_wc i := by
  fin_cases i
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [262, 132, 66, 32, 10, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [262, 132, 66, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 132, 66, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [258, 132, 70, 32, 10, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [258, 132, 70, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 132, 70, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [276, 132, 80, 32, 10, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [276, 132, 80, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 80, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [272, 132, 84, 32, 10, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [272, 132, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [324, 132, 32, 8, 2, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [324, 132, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [324, 132, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [322, 130, 32, 10, 6, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [322, 130, 32, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [322, 130, 32, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [260, 132, 64, 32, 10, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [260, 132, 64, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [256, 132, 68, 32, 18, 10, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [256, 132, 68, 32, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [274, 128, 82, 32, 10, 4, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [274, 128, 82, 32, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 128, 82, 32, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [256, 132, 68, 32, 20, 8, 2, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [256, 132, 68, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [256, 130, 66, 32, 16, 10, 6, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [256, 130, 66, 32, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 32, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [258, 128, 66, 32, 16, 10, 4, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [258, 128, 66, 32, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [324, 132, 32, 10, 1] ≤ spanCodes [320, 128, 32, 16, 8, 4, 2, 1]
    apply step109wc197_spanCodes_le_of_gens [324, 132, 32, 10, 1] (spanCodes [320, 128, 32, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [320, 128, 32, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o197CoverSound_wc (i : Fin 13) (M : Mat3) (h : o197Cover_wc i M) : M ∈ o197SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [262, 132, 66, 32, 10, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 132, 66, 32, 10, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 132, 70, 32, 10, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 132, 70, 32, 10, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 80, 32, 10, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 80, 32, 10, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 132, 84, 32, 10, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 84, 32, 10, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [324, 132, 32, 8, 2, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [324, 132, 32, 8, 2, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [322, 130, 32, 10, 6, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 130, 32, 10, 6, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 132, 64, 32, 10, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 64, 32, 10, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 68, 32, 18, 10, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 18, 10, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 128, 82, 32, 10, 4, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 128, 82, 32, 10, 4, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 68, 32, 20, 8, 2, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 32, 20, 8, 2, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 130, 66, 32, 16, 10, 6, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 32, 16, 10, 6, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 66, 32, 16, 10, 4, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 4, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [320, 128, 32, 16, 8, 4, 2, 1]
    unfold o197Cover_wc o197CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [320, 128, 32, 16, 8, 4, 2, 1] (step109wc197MatrixCodeNat M) h
    rwa [step109wc197_codeMat_matrixCode_all] at hspan

private theorem o197Cert_wc : (24 - 4) * 14 < ∑ i : Fin 13, o197Lambda_wc i * o197SourceLb_wc i := by
  simp only [o197Lambda_wc, o197SourceLb_wc]; decide
private theorem o197LambdaSum_wc : 4 ≤ ∑ i : Fin 13, o197Lambda_wc i := by
  simp only [o197Lambda_wc]; decide

theorem o197Lb15_wc
    (hSource : ∀ i : Fin 13, QuotientRankAtLeast (o197SourceU_wc i) (o197SourceLb_wc i)) :
    QuotientRankAtLeast o197W_wc 15 :=
  quotientRankAtLeast_of_contradiction o197W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o197SourceU_wc o197SourceLb_wc
      o197Lambda_wc 4 14
      o197Cover_wc o197W_le_source_wc hSource
      o197LambdaSum_wc o197CoverSound_wc
      (fun M => o197MatCoverage_wc M) (by omega) o197Cert_wc D)

end QiushiMatmul
