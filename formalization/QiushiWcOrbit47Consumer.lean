import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 47, exact manifest basis [304, 160, 68, 8, 2, 1]. -/
def o47W_wc : Submodule F2 Mat3 := spanCodes [304, 160, 68, 8, 2, 1]

private theorem step109wc47_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc47MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc47_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc47MatrixCodeNat M) = M := by decide

private theorem step109wc47_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc47_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o47SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [288, 160, 68, 16, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [292, 160, 68, 20, 8, 2, 1]
  | ⟨2, _⟩ => spanCodes [272, 128, 68, 32, 8, 2, 1]
  | ⟨3, _⟩ => spanCodes [276, 132, 68, 36, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 144, 68, 48, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [260, 148, 68, 52, 8, 2, 1]
  | ⟨6, _⟩ => spanCodes [304, 160, 64, 8, 4, 2, 1]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o47SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [12, 12, 12, 12, 12, 12, 9].getD k 0

def o47Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o47CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [288, 160, 68, 16, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [292, 160, 68, 20, 8, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [272, 128, 68, 32, 8, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [276, 132, 68, 36, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 144, 68, 48, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [260, 148, 68, 52, 8, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [304, 160, 64, 8, 4, 2, 1] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o47Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o47CoverB_wc i (step109wc47MatrixCodeNat M) = true

theorem o47CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o47CoverB_wc i c.val = true then o47Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o47MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o47Cover_wc i M then o47Lambda_wc i else 0 := by
  have h := o47CodeCoverage_wc ⟨step109wc47MatrixCodeNat M, step109wc47_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o47CoverB_wc i (step109wc47MatrixCodeNat M) <;> simp [o47Cover_wc, hb]

theorem o47W_le_source_wc (i : Fin 7) : o47W_wc ≤ o47SourceU_wc i := by
  fin_cases i
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [288, 160, 68, 16, 8, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [288, 160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [292, 160, 68, 20, 8, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [292, 160, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [272, 128, 68, 32, 8, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [272, 128, 68, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [276, 132, 68, 36, 8, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [276, 132, 68, 36, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 36, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [256, 144, 68, 48, 8, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [256, 144, 68, 48, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [260, 148, 68, 52, 8, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [260, 148, 68, 52, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 148, 68, 52, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [304, 160, 68, 8, 2, 1] ≤ spanCodes [304, 160, 64, 8, 4, 2, 1]
    apply step109wc47_spanCodes_le_of_gens [304, 160, 68, 8, 2, 1] (spanCodes [304, 160, 64, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o47CoverSound_wc (i : Fin 7) (M : Mat3) (h : o47Cover_wc i M) : M ∈ o47SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [288, 160, 68, 16, 8, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 16, 8, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 160, 68, 20, 8, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 20, 8, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 68, 32, 8, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 8, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 68, 36, 8, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 68, 36, 8, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 68, 48, 8, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 8, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 148, 68, 52, 8, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 148, 68, 52, 8, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [304, 160, 64, 8, 4, 2, 1]
    unfold o47Cover_wc o47CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [304, 160, 64, 8, 4, 2, 1] (step109wc47MatrixCodeNat M) h
    rwa [step109wc47_codeMat_matrixCode_all] at hspan

private theorem o47Cert_wc : (7 - 1) * 13 < ∑ i : Fin 7, o47Lambda_wc i * o47SourceLb_wc i := by
  simp only [o47Lambda_wc, o47SourceLb_wc]; decide
private theorem o47LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o47Lambda_wc i := by
  simp only [o47Lambda_wc]; decide

theorem o47Lb14_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o47SourceU_wc i) (o47SourceLb_wc i)) :
    QuotientRankAtLeast o47W_wc 14 :=
  quotientRankAtLeast_of_contradiction o47W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o47SourceU_wc o47SourceLb_wc
      o47Lambda_wc 1 13
      o47Cover_wc o47W_le_source_wc hSource
      o47LambdaSum_wc o47CoverSound_wc
      (fun M => o47MatCoverage_wc M) (by omega) o47Cert_wc D)

end QiushiMatmul
