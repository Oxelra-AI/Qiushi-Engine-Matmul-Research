import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 164, exact manifest basis [256, 96, 20, 10, 1]. -/
def o164W_wc : Submodule F2 Mat3 := spanCodes [256, 96, 20, 10, 1]

private theorem step109wc164_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc164MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc164_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc164MatrixCodeNat M) = M := by decide

private theorem step109wc164_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc164_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o164SourceU_wc : Fin 13 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 70, 38, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [256, 130, 96, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [256, 132, 96, 20, 10, 1]
  | ⟨3, _⟩ => spanCodes [256, 162, 96, 20, 10, 1]
  | ⟨4, _⟩ => spanCodes [256, 164, 96, 20, 10, 1]
  | ⟨5, _⟩ => spanCodes [256, 66, 34, 20, 10, 1]
  | ⟨6, _⟩ => spanCodes [256, 68, 36, 20, 10, 1]
  | ⟨7, _⟩ => spanCodes [256, 128, 96, 20, 10, 1]
  | ⟨8, _⟩ => spanCodes [256, 134, 96, 20, 10, 1]
  | ⟨9, _⟩ => spanCodes [256, 96, 20, 8, 2, 1]
  | ⟨10, _⟩ => spanCodes [256, 96, 16, 10, 4, 1]
  | ⟨11, _⟩ => spanCodes [256, 64, 32, 20, 10, 1]
  | ⟨12, _⟩ => spanCodes [256, 160, 96, 18, 10, 6, 1]
  | ⟨k + 13, h⟩ => absurd h (by omega)

def o164SourceLb_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 14, 14, 14, 14, 13, 13, 12, 12].getD k 0

def o164Lambda_wc : Fin 13 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o164CoverB_wc : Fin 13 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 70, 38, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 130, 96, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 132, 96, 20, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 162, 96, 20, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 164, 96, 20, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 66, 34, 20, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 68, 36, 20, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 128, 96, 20, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 134, 96, 20, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [256, 96, 20, 8, 2, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [256, 96, 16, 10, 4, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [256, 64, 32, 20, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [256, 160, 96, 18, 10, 6, 1] c
  | ⟨k + 13, h⟩, _ => absurd h (by omega)

def o164Cover_wc (i : Fin 13) (M : Mat3) : Prop :=
  o164CoverB_wc i (step109wc164MatrixCodeNat M) = true

theorem o164CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 13, if o164CoverB_wc i c.val = true then o164Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o164MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 13, if o164Cover_wc i M then o164Lambda_wc i else 0 := by
  have h := o164CodeCoverage_wc ⟨step109wc164MatrixCodeNat M, step109wc164_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o164CoverB_wc i (step109wc164MatrixCodeNat M) <;> simp [o164Cover_wc, hb]

theorem o164W_le_source_wc (i : Fin 13) : o164W_wc ≤ o164SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 70, 38, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 70, 38, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 70, 38, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 130, 96, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 130, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 130, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 132, 96, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 132, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 162, 96, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 162, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 162, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 164, 96, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 164, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 66, 34, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 66, 34, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 66, 34, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 68, 36, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 68, 36, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 36, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 128, 96, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 128, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 134, 96, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 134, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 134, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 96, 20, 8, 2, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 96, 16, 10, 4, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 96, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 64, 32, 20, 10, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 64, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 64, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 20, 10, 1] ≤ spanCodes [256, 160, 96, 18, 10, 6, 1]
    apply step109wc164_spanCodes_le_of_gens [256, 96, 20, 10, 1] (spanCodes [256, 160, 96, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 18, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o164CoverSound_wc (i : Fin 13) (M : Mat3) (h : o164Cover_wc i M) : M ∈ o164SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 70, 38, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 70, 38, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 130, 96, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 96, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 96, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 162, 96, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 162, 96, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 164, 96, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 66, 34, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 66, 34, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 68, 36, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 36, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 96, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 134, 96, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 134, 96, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 96, 20, 8, 2, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 96, 20, 8, 2, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 96, 16, 10, 4, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 96, 16, 10, 4, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 64, 32, 20, 10, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 64, 32, 20, 10, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 96, 18, 10, 6, 1]
    unfold o164Cover_wc o164CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 18, 10, 6, 1] (step109wc164MatrixCodeNat M) h
    rwa [step109wc164_codeMat_matrixCode_all] at hspan

private theorem o164Cert_wc : (13 - 1) * 15 < ∑ i : Fin 13, o164Lambda_wc i * o164SourceLb_wc i := by
  simp only [o164Lambda_wc, o164SourceLb_wc]; decide
private theorem o164LambdaSum_wc : 1 ≤ ∑ i : Fin 13, o164Lambda_wc i := by
  simp only [o164Lambda_wc]; decide

theorem o164Lb16_wc
    (hSource : ∀ i : Fin 13, QuotientRankAtLeast (o164SourceU_wc i) (o164SourceLb_wc i)) :
    QuotientRankAtLeast o164W_wc 16 :=
  quotientRankAtLeast_of_contradiction o164W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o164SourceU_wc o164SourceLb_wc
      o164Lambda_wc 1 15
      o164Cover_wc o164W_le_source_wc hSource
      o164LambdaSum_wc o164CoverSound_wc
      (fun M => o164MatCoverage_wc M) (by omega) o164Cert_wc D)

end QiushiMatmul
