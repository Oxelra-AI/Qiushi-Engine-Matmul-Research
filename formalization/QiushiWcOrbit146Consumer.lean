import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 146, exact manifest basis [280, 160, 84, 2, 1]. -/
def o146W_wc : Submodule F2 Mat3 := spanCodes [280, 160, 84, 2, 1]

private theorem step109wc146_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc146MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc146_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc146MatrixCodeNat M) = M := by decide

private theorem step109wc146_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc146_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o146SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [276, 160, 84, 12, 2, 1]
  | ⟨1, _⟩ => spanCodes [280, 132, 84, 36, 2, 1]
  | ⟨2, _⟩ => spanCodes [280, 136, 84, 40, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 160, 68, 16, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [260, 140, 72, 44, 28, 2, 1]
  | ⟨5, _⟩ => spanCodes [268, 128, 64, 32, 20, 2, 1]
  | ⟨6, _⟩ => spanCodes [280, 152, 80, 56, 4, 2, 1]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o146SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 12, 12, 12, 9].getD k 0

def o146Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o146CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [276, 160, 84, 12, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [280, 132, 84, 36, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [280, 136, 84, 40, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 160, 68, 16, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [260, 140, 72, 44, 28, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [268, 128, 64, 32, 20, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [280, 152, 80, 56, 4, 2, 1] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o146Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o146CoverB_wc i (step109wc146MatrixCodeNat M) = true

theorem o146CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o146CoverB_wc i c.val = true then o146Lambda_wc i else 0 := by
  revert c
  decide +kernel

theorem o146MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o146Cover_wc i M then o146Lambda_wc i else 0 := by
  have h := o146CodeCoverage_wc ⟨step109wc146MatrixCodeNat M, step109wc146_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o146CoverB_wc i (step109wc146MatrixCodeNat M) <;> simp [o146Cover_wc, hb]

theorem o146W_le_source_wc (i : Fin 7) : o146W_wc ≤ o146SourceU_wc i := by
  fin_cases i
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [276, 160, 84, 12, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [276, 160, 84, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 160, 84, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [280, 132, 84, 36, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [280, 132, 84, 36, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [280, 132, 84, 36, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [280, 136, 84, 40, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [280, 136, 84, 40, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [280, 136, 84, 40, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [256, 160, 68, 16, 8, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [256, 160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [260, 140, 72, 44, 28, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [260, 140, 72, 44, 28, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 140, 72, 44, 28, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [268, 128, 64, 32, 20, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [268, 128, 64, 32, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [268, 128, 64, 32, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [280, 160, 84, 2, 1] ≤ spanCodes [280, 152, 80, 56, 4, 2, 1]
    apply step109wc146_spanCodes_le_of_gens [280, 160, 84, 2, 1] (spanCodes [280, 152, 80, 56, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [280, 152, 80, 56, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o146CoverSound_wc (i : Fin 7) (M : Mat3) (h : o146Cover_wc i M) : M ∈ o146SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [276, 160, 84, 12, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 160, 84, 12, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [280, 132, 84, 36, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [280, 132, 84, 36, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [280, 136, 84, 40, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [280, 136, 84, 40, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 68, 16, 8, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 8, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 140, 72, 44, 28, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 140, 72, 44, 28, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [268, 128, 64, 32, 20, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [268, 128, 64, 32, 20, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [280, 152, 80, 56, 4, 2, 1]
    unfold o146Cover_wc o146CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [280, 152, 80, 56, 4, 2, 1] (step109wc146MatrixCodeNat M) h
    rwa [step109wc146_codeMat_matrixCode_all] at hspan

private theorem o146Cert_wc : (7 - 1) * 14 < ∑ i : Fin 7, o146Lambda_wc i * o146SourceLb_wc i := by
  simp only [o146Lambda_wc, o146SourceLb_wc]; decide
private theorem o146LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o146Lambda_wc i := by
  simp only [o146Lambda_wc]; decide

theorem o146Lb15_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o146SourceU_wc i) (o146SourceLb_wc i)) :
    QuotientRankAtLeast o146W_wc 15 :=
  quotientRankAtLeast_of_contradiction o146W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o146SourceU_wc o146SourceLb_wc
      o146Lambda_wc 1 14
      o146Cover_wc o146W_le_source_wc hSource
      o146LambdaSum_wc o146CoverSound_wc
      (fun M => o146MatCoverage_wc M) (by omega) o146Cert_wc D)

end QiushiMatmul
