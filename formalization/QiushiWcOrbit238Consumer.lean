import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 238, exact manifest basis [294, 136, 96, 20, 1]. -/
def o238W_wc : Submodule F2 Mat3 := spanCodes [294, 136, 96, 20, 1]

private theorem step109wc238_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc238MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc238_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc238MatrixCodeNat M) = M := by decide

private theorem step109wc238_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc238_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o238SourceU_wc : Fin 12 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 136, 70, 38, 20, 1]
  | ⟨1, _⟩ => spanCodes [266, 136, 76, 44, 20, 1]
  | ⟨2, _⟩ => spanCodes [292, 136, 96, 20, 2, 1]
  | ⟨3, _⟩ => spanCodes [290, 136, 96, 16, 4, 1]
  | ⟨4, _⟩ => spanCodes [294, 128, 96, 20, 8, 1]
  | ⟨5, _⟩ => spanCodes [294, 134, 96, 20, 14, 1]
  | ⟨6, _⟩ => spanCodes [262, 136, 64, 32, 20, 1]
  | ⟨7, _⟩ => spanCodes [258, 136, 68, 36, 20, 1]
  | ⟨8, _⟩ => spanCodes [268, 136, 74, 42, 20, 1]
  | ⟨9, _⟩ => spanCodes [264, 136, 78, 46, 20, 1]
  | ⟨10, _⟩ => spanCodes [288, 130, 96, 18, 10, 6, 1]
  | ⟨11, _⟩ => spanCodes [260, 130, 66, 34, 20, 10, 1]
  | ⟨k + 12, h⟩ => absurd h (by omega)

def o238SourceLb_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [15, 15, 14, 14, 14, 14, 14, 14, 14, 14, 12, 12].getD k 0

def o238Lambda_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o238CoverB_wc : Fin 12 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 136, 70, 38, 20, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [266, 136, 76, 44, 20, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [292, 136, 96, 20, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [290, 136, 96, 16, 4, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [294, 128, 96, 20, 8, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [294, 134, 96, 20, 14, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [262, 136, 64, 32, 20, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [258, 136, 68, 36, 20, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [268, 136, 74, 42, 20, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [264, 136, 78, 46, 20, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [288, 130, 96, 18, 10, 6, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [260, 130, 66, 34, 20, 10, 1] c
  | ⟨k + 12, h⟩, _ => absurd h (by omega)

def o238Cover_wc (i : Fin 12) (M : Mat3) : Prop :=
  o238CoverB_wc i (step109wc238MatrixCodeNat M) = true

theorem o238CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 12, if o238CoverB_wc i c.val = true then o238Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o238MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 12, if o238Cover_wc i M then o238Lambda_wc i else 0 := by
  have h := o238CodeCoverage_wc ⟨step109wc238MatrixCodeNat M, step109wc238_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o238CoverB_wc i (step109wc238MatrixCodeNat M) <;> simp [o238Cover_wc, hb]

theorem o238W_le_source_wc (i : Fin 12) : o238W_wc ≤ o238SourceU_wc i := by
  fin_cases i
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [256, 136, 70, 38, 20, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [256, 136, 70, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 136, 70, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [266, 136, 76, 44, 20, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [266, 136, 76, 44, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [266, 136, 76, 44, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [292, 136, 96, 20, 2, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [292, 136, 96, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 136, 96, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [290, 136, 96, 16, 4, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [290, 136, 96, 16, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [290, 136, 96, 16, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [294, 128, 96, 20, 8, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [294, 128, 96, 20, 8, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [294, 128, 96, 20, 8, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [294, 134, 96, 20, 14, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [294, 134, 96, 20, 14, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [294, 134, 96, 20, 14, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [262, 136, 64, 32, 20, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [262, 136, 64, 32, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 136, 64, 32, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [258, 136, 68, 36, 20, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [258, 136, 68, 36, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 136, 68, 36, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [268, 136, 74, 42, 20, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [268, 136, 74, 42, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [268, 136, 74, 42, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [264, 136, 78, 46, 20, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [264, 136, 78, 46, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 136, 78, 46, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [288, 130, 96, 18, 10, 6, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [288, 130, 96, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 130, 96, 18, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [294, 136, 96, 20, 1] ≤ spanCodes [260, 130, 66, 34, 20, 10, 1]
    apply step109wc238_spanCodes_le_of_gens [294, 136, 96, 20, 1] (spanCodes [260, 130, 66, 34, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 130, 66, 34, 20, 10, 1] n (by fin_cases hn <;> decide)

theorem o238CoverSound_wc (i : Fin 12) (M : Mat3) (h : o238Cover_wc i M) : M ∈ o238SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 136, 70, 38, 20, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 136, 70, 38, 20, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [266, 136, 76, 44, 20, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 76, 44, 20, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 136, 96, 20, 2, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 136, 96, 20, 2, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [290, 136, 96, 16, 4, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [290, 136, 96, 16, 4, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [294, 128, 96, 20, 8, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [294, 128, 96, 20, 8, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [294, 134, 96, 20, 14, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [294, 134, 96, 20, 14, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 136, 64, 32, 20, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 136, 64, 32, 20, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 136, 68, 36, 20, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 136, 68, 36, 20, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [268, 136, 74, 42, 20, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [268, 136, 74, 42, 20, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 136, 78, 46, 20, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 136, 78, 46, 20, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 130, 96, 18, 10, 6, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 130, 96, 18, 10, 6, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 130, 66, 34, 20, 10, 1]
    unfold o238Cover_wc o238CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 130, 66, 34, 20, 10, 1] (step109wc238MatrixCodeNat M) h
    rwa [step109wc238_codeMat_matrixCode_all] at hspan

private theorem o238Cert_wc : (12 - 1) * 15 < ∑ i : Fin 12, o238Lambda_wc i * o238SourceLb_wc i := by
  simp only [o238Lambda_wc, o238SourceLb_wc]; decide
private theorem o238LambdaSum_wc : 1 ≤ ∑ i : Fin 12, o238Lambda_wc i := by
  simp only [o238Lambda_wc]; decide

theorem o238Lb16_wc
    (hSource : ∀ i : Fin 12, QuotientRankAtLeast (o238SourceU_wc i) (o238SourceLb_wc i)) :
    QuotientRankAtLeast o238W_wc 16 :=
  quotientRankAtLeast_of_contradiction o238W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o238SourceU_wc o238SourceLb_wc
      o238Lambda_wc 1 15
      o238Cover_wc o238W_le_source_wc hSource
      o238LambdaSum_wc o238CoverSound_wc
      (fun M => o238MatCoverage_wc M) (by omega) o238Cert_wc D)

end QiushiMatmul
