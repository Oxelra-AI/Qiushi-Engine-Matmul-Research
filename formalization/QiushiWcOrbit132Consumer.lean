import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 132, exact manifest basis [304, 160, 12, 2, 1]. -/
def o132W_wc : Submodule F2 Mat3 := spanCodes [304, 160, 12, 2, 1]

private theorem step109wc132_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc132MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc132_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc132MatrixCodeNat M) = M := by decide

private theorem step109wc132_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc132_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o132SourceU_wc : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [276, 132, 36, 12, 2, 1]
  | ⟨1, _⟩ => spanCodes [260, 148, 52, 12, 2, 1]
  | ⟨2, _⟩ => spanCodes [304, 160, 80, 12, 2, 1]
  | ⟨3, _⟩ => spanCodes [304, 160, 84, 12, 2, 1]
  | ⟨4, _⟩ => spanCodes [304, 160, 100, 12, 2, 1]
  | ⟨5, _⟩ => spanCodes [304, 160, 112, 12, 2, 1]
  | ⟨6, _⟩ => spanCodes [272, 128, 64, 32, 12, 2, 1]
  | ⟨7, _⟩ => spanCodes [256, 144, 68, 48, 12, 2, 1]
  | ⟨8, _⟩ => spanCodes [288, 160, 16, 8, 4, 2, 1]
  | ⟨k + 9, h⟩ => absurd h (by omega)

def o132SourceLb_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 14, 14, 12, 12, 9].getD k 0

def o132Lambda_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o132CoverB_wc : Fin 9 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [276, 132, 36, 12, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [260, 148, 52, 12, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [304, 160, 80, 12, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [304, 160, 84, 12, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [304, 160, 100, 12, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [304, 160, 112, 12, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [272, 128, 64, 32, 12, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 144, 68, 48, 12, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [288, 160, 16, 8, 4, 2, 1] c
  | ⟨k + 9, h⟩, _ => absurd h (by omega)

def o132Cover_wc (i : Fin 9) (M : Mat3) : Prop :=
  o132CoverB_wc i (step109wc132MatrixCodeNat M) = true

theorem o132CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 9, if o132CoverB_wc i c.val = true then o132Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o132MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o132Cover_wc i M then o132Lambda_wc i else 0 := by
  have h := o132CodeCoverage_wc ⟨step109wc132MatrixCodeNat M, step109wc132_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o132CoverB_wc i (step109wc132MatrixCodeNat M) <;> simp [o132Cover_wc, hb]

theorem o132W_le_source_wc (i : Fin 9) : o132W_wc ≤ o132SourceU_wc i := by
  fin_cases i
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [276, 132, 36, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [276, 132, 36, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 36, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [260, 148, 52, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [260, 148, 52, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 148, 52, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [304, 160, 80, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [304, 160, 80, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 80, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [304, 160, 84, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [304, 160, 84, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 84, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [304, 160, 100, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [304, 160, 100, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 100, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [304, 160, 112, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [304, 160, 112, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 112, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [272, 128, 64, 32, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [272, 128, 64, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [256, 144, 68, 48, 12, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [256, 144, 68, 48, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 12, 2, 1] ≤ spanCodes [288, 160, 16, 8, 4, 2, 1]
    apply step109wc132_spanCodes_le_of_gens [304, 160, 12, 2, 1] (spanCodes [288, 160, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o132CoverSound_wc (i : Fin 9) (M : Mat3) (h : o132Cover_wc i M) : M ∈ o132SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [276, 132, 36, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 36, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 148, 52, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 148, 52, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 80, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 80, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 84, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 84, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 100, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 100, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 112, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 112, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 64, 32, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 64, 32, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 68, 48, 12, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 12, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 16, 8, 4, 2, 1]
    unfold o132Cover_wc o132CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 16, 8, 4, 2, 1] (step109wc132MatrixCodeNat M) h
    rwa [step109wc132_codeMat_matrixCode_all] at hspan

private theorem o132Cert_wc : (9 - 1) * 14 < ∑ i : Fin 9, o132Lambda_wc i * o132SourceLb_wc i := by
  simp only [o132Lambda_wc, o132SourceLb_wc]; decide
private theorem o132LambdaSum_wc : 1 ≤ ∑ i : Fin 9, o132Lambda_wc i := by
  simp only [o132Lambda_wc]; decide

theorem o132Lb15_wc
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o132SourceU_wc i) (o132SourceLb_wc i)) :
    QuotientRankAtLeast o132W_wc 15 :=
  quotientRankAtLeast_of_contradiction o132W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o132SourceU_wc o132SourceLb_wc
      o132Lambda_wc 1 14
      o132Cover_wc o132W_le_source_wc hSource
      o132LambdaSum_wc o132CoverSound_wc
      (fun M => o132MatCoverage_wc M) (by omega) o132Cert_wc D)

end QiushiMatmul
