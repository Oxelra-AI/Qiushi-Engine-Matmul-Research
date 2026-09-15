import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 147, exact manifest basis [160, 68, 16, 10, 1]. -/
def o147W_wc : Submodule F2 Mat3 := spanCodes [160, 68, 16, 10, 1]

private theorem step109wc147_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc147MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc147_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc147MatrixCodeNat M) = M := by decide

private theorem step109wc147_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc147_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o147SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [160, 68, 16, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [258, 160, 68, 16, 10, 1]
  | ⟨2, _⟩ => spanCodes [260, 160, 68, 16, 10, 1]
  | ⟨3, _⟩ => spanCodes [262, 160, 68, 16, 10, 1]
  | ⟨4, _⟩ => spanCodes [288, 160, 68, 16, 10, 1]
  | ⟨5, _⟩ => spanCodes [290, 160, 68, 16, 10, 1]
  | ⟨6, _⟩ => spanCodes [292, 160, 68, 16, 10, 1]
  | ⟨7, _⟩ => spanCodes [294, 160, 68, 16, 10, 1]
  | ⟨8, _⟩ => spanCodes [256, 160, 68, 16, 10, 1]
  | ⟨9, _⟩ => spanCodes [160, 64, 16, 10, 4, 1]
  | ⟨10, _⟩ => spanCodes [160, 66, 16, 10, 6, 1]
  | ⟨11, _⟩ => spanCodes [128, 68, 32, 16, 10, 1]
  | ⟨12, _⟩ => spanCodes [130, 68, 34, 16, 10, 1]
  | ⟨13, _⟩ => spanCodes [132, 68, 36, 16, 10, 1]
  | ⟨14, _⟩ => spanCodes [134, 68, 38, 16, 10, 1]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o147SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 14, 13, 13, 13, 13, 13, 13].getD k 0

def o147Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o147CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [160, 68, 16, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [258, 160, 68, 16, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [260, 160, 68, 16, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [262, 160, 68, 16, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [288, 160, 68, 16, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [290, 160, 68, 16, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [292, 160, 68, 16, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [294, 160, 68, 16, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 160, 68, 16, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [160, 64, 16, 10, 4, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [160, 66, 16, 10, 6, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [128, 68, 32, 16, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [130, 68, 34, 16, 10, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [132, 68, 36, 16, 10, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [134, 68, 38, 16, 10, 1] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o147Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o147CoverB_wc i (step109wc147MatrixCodeNat M) = true

theorem o147CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 15, if o147CoverB_wc i c.val = true then o147Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o147MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o147Cover_wc i M then o147Lambda_wc i else 0 := by
  have h := o147CodeCoverage_wc ⟨step109wc147MatrixCodeNat M, step109wc147_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o147CoverB_wc i (step109wc147MatrixCodeNat M) <;> simp [o147Cover_wc, hb]

theorem o147W_le_source_wc (i : Fin 15) : o147W_wc ≤ o147SourceU_wc i := by
  fin_cases i
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [160, 68, 16, 8, 2, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [160, 68, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [160, 68, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [258, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [258, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [260, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [260, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [262, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [262, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [288, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [288, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [290, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [290, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [290, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [292, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [292, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [294, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [294, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [294, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [256, 160, 68, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [256, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [160, 64, 16, 10, 4, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [160, 64, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [160, 64, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [160, 66, 16, 10, 6, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [160, 66, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [160, 66, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [128, 68, 32, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [128, 68, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [130, 68, 34, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [130, 68, 34, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [130, 68, 34, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [132, 68, 36, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [132, 68, 36, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 68, 36, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [160, 68, 16, 10, 1] ≤ spanCodes [134, 68, 38, 16, 10, 1]
    apply step109wc147_spanCodes_le_of_gens [160, 68, 16, 10, 1] (spanCodes [134, 68, 38, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [134, 68, 38, 16, 10, 1] n (by fin_cases hn <;> decide)

theorem o147CoverSound_wc (i : Fin 15) (M : Mat3) (h : o147Cover_wc i M) : M ∈ o147SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [160, 68, 16, 8, 2, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [160, 68, 16, 8, 2, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [290, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [290, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [294, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [294, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 68, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [160, 64, 16, 10, 4, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [160, 64, 16, 10, 4, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [160, 66, 16, 10, 6, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [160, 66, 16, 10, 6, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 68, 32, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [130, 68, 34, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [130, 68, 34, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [132, 68, 36, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [132, 68, 36, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [134, 68, 38, 16, 10, 1]
    unfold o147Cover_wc o147CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [134, 68, 38, 16, 10, 1] (step109wc147MatrixCodeNat M) h
    rwa [step109wc147_codeMat_matrixCode_all] at hspan

private theorem o147Cert_wc : (15 - 1) * 15 < ∑ i : Fin 15, o147Lambda_wc i * o147SourceLb_wc i := by
  simp only [o147Lambda_wc, o147SourceLb_wc]; decide
private theorem o147LambdaSum_wc : 1 ≤ ∑ i : Fin 15, o147Lambda_wc i := by
  simp only [o147Lambda_wc]; decide

theorem o147Lb16_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o147SourceU_wc i) (o147SourceLb_wc i)) :
    QuotientRankAtLeast o147W_wc 16 :=
  quotientRankAtLeast_of_contradiction o147W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o147SourceU_wc o147SourceLb_wc
      o147Lambda_wc 1 15
      o147Cover_wc o147W_le_source_wc hSource
      o147LambdaSum_wc o147CoverSound_wc
      (fun M => o147MatCoverage_wc M) (by omega) o147Cert_wc D)

end QiushiMatmul
