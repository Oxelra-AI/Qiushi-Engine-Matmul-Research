import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 96, exact manifest basis [68, 20, 8, 2, 1]. -/
def o96W_wc : Submodule F2 Mat3 := spanCodes [68, 20, 8, 2, 1]

private theorem step109wc96_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc96MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc96_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc96MatrixCodeNat M) = M := by decide

private theorem step109wc96_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc96_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o96SourceU_wc : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [68, 32, 20, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [68, 36, 20, 8, 2, 1]
  | ⟨2, _⟩ => spanCodes [128, 68, 20, 8, 2, 1]
  | ⟨3, _⟩ => spanCodes [132, 68, 20, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [288, 68, 20, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [292, 68, 20, 8, 2, 1]
  | ⟨6, _⟩ => spanCodes [384, 68, 20, 8, 2, 1]
  | ⟨7, _⟩ => spanCodes [388, 68, 20, 8, 2, 1]
  | ⟨8, _⟩ => spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
  | ⟨k + 9, h⟩ => absurd h (by omega)

def o96SourceLb_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 14, 14, 14, 14, 6].getD k 0

def o96Lambda_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o96CoverB_wc : Fin 9 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [68, 32, 20, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [68, 36, 20, 8, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [128, 68, 20, 8, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [132, 68, 20, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [288, 68, 20, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [292, 68, 20, 8, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [384, 68, 20, 8, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [388, 68, 20, 8, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 160, 64, 16, 8, 4, 2, 1] c
  | ⟨k + 9, h⟩, _ => absurd h (by omega)

def o96Cover_wc (i : Fin 9) (M : Mat3) : Prop :=
  o96CoverB_wc i (step109wc96MatrixCodeNat M) = true

theorem o96CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 9, if o96CoverB_wc i c.val = true then o96Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o96MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o96Cover_wc i M then o96Lambda_wc i else 0 := by
  have h := o96CodeCoverage_wc ⟨step109wc96MatrixCodeNat M, step109wc96_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o96CoverB_wc i (step109wc96MatrixCodeNat M) <;> simp [o96Cover_wc, hb]

theorem o96W_le_source_wc (i : Fin 9) : o96W_wc ≤ o96SourceU_wc i := by
  fin_cases i
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [68, 32, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [68, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [68, 36, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [68, 36, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [68, 36, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [128, 68, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [128, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [132, 68, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [132, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [288, 68, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [288, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [292, 68, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [292, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [384, 68, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [384, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [388, 68, 20, 8, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [388, 68, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [388, 68, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 20, 8, 2, 1] ≤ spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
    apply step109wc96_spanCodes_le_of_gens [68, 20, 8, 2, 1] (spanCodes [256, 160, 64, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o96CoverSound_wc (i : Fin 9) (M : Mat3) (h : o96Cover_wc i M) : M ∈ o96SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [68, 32, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [68, 36, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 36, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 68, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 68, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [132, 68, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [132, 68, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 68, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 68, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 68, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 68, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 68, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 68, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [388, 68, 20, 8, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [388, 68, 20, 8, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
    unfold o96Cover_wc o96CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] (step109wc96MatrixCodeNat M) h
    rwa [step109wc96_codeMat_matrixCode_all] at hspan

private theorem o96Cert_wc : (9 - 1) * 15 < ∑ i : Fin 9, o96Lambda_wc i * o96SourceLb_wc i := by
  simp only [o96Lambda_wc, o96SourceLb_wc]; decide
private theorem o96LambdaSum_wc : 1 ≤ ∑ i : Fin 9, o96Lambda_wc i := by
  simp only [o96Lambda_wc]; decide

theorem o96Lb16_wc
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o96SourceU_wc i) (o96SourceLb_wc i)) :
    QuotientRankAtLeast o96W_wc 16 :=
  quotientRankAtLeast_of_contradiction o96W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o96SourceU_wc o96SourceLb_wc
      o96Lambda_wc 1 15
      o96Cover_wc o96W_le_source_wc hSource
      o96LambdaSum_wc o96CoverSound_wc
      (fun M => o96MatCoverage_wc M) (by omega) o96Cert_wc D)

end QiushiMatmul
