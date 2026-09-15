import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 235, exact manifest basis [326, 136, 38, 20, 1]. -/
def o235W_wc : Submodule F2 Mat3 := spanCodes [326, 136, 38, 20, 1]

private theorem step109wc235_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc235MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc235_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc235MatrixCodeNat M) = M := by decide

private theorem step109wc235_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc235_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o235SourceU_wc : Fin 12 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [326, 130, 38, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [258, 136, 68, 38, 20, 1]
  | ⟨2, _⟩ => spanCodes [256, 136, 70, 38, 20, 1]
  | ⟨3, _⟩ => spanCodes [266, 136, 76, 38, 20, 1]
  | ⟨4, _⟩ => spanCodes [264, 136, 78, 38, 20, 1]
  | ⟨5, _⟩ => spanCodes [322, 136, 34, 16, 4, 1]
  | ⟨6, _⟩ => spanCodes [320, 136, 32, 18, 6, 1]
  | ⟨7, _⟩ => spanCodes [326, 132, 38, 20, 12, 1]
  | ⟨8, _⟩ => spanCodes [326, 134, 38, 20, 14, 1]
  | ⟨9, _⟩ => spanCodes [270, 136, 72, 38, 20, 1]
  | ⟨10, _⟩ => spanCodes [260, 136, 64, 36, 20, 2, 1]
  | ⟨11, _⟩ => spanCodes [260, 128, 66, 38, 20, 8, 1]
  | ⟨k + 12, h⟩ => absurd h (by omega)

def o235SourceLb_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 14, 14, 14, 14, 14, 12, 12].getD k 0

def o235Lambda_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o235CoverB_wc : Fin 12 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [326, 130, 38, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [258, 136, 68, 38, 20, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 136, 70, 38, 20, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [266, 136, 76, 38, 20, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [264, 136, 78, 38, 20, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [322, 136, 34, 16, 4, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [320, 136, 32, 18, 6, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [326, 132, 38, 20, 12, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [326, 134, 38, 20, 14, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [270, 136, 72, 38, 20, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [260, 136, 64, 36, 20, 2, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [260, 128, 66, 38, 20, 8, 1] c
  | ⟨k + 12, h⟩, _ => absurd h (by omega)

def o235Cover_wc (i : Fin 12) (M : Mat3) : Prop :=
  o235CoverB_wc i (step109wc235MatrixCodeNat M) = true

theorem o235CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 12, if o235CoverB_wc i c.val = true then o235Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o235MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 12, if o235Cover_wc i M then o235Lambda_wc i else 0 := by
  have h := o235CodeCoverage_wc ⟨step109wc235MatrixCodeNat M, step109wc235_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o235CoverB_wc i (step109wc235MatrixCodeNat M) <;> simp [o235Cover_wc, hb]

theorem o235W_le_source_wc (i : Fin 12) : o235W_wc ≤ o235SourceU_wc i := by
  fin_cases i
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [326, 130, 38, 20, 10, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [326, 130, 38, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [326, 130, 38, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [258, 136, 68, 38, 20, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [258, 136, 68, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 136, 68, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [256, 136, 70, 38, 20, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [256, 136, 70, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 136, 70, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [266, 136, 76, 38, 20, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [266, 136, 76, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [266, 136, 76, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [264, 136, 78, 38, 20, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [264, 136, 78, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 136, 78, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [322, 136, 34, 16, 4, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [322, 136, 34, 16, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [322, 136, 34, 16, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [320, 136, 32, 18, 6, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [320, 136, 32, 18, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [320, 136, 32, 18, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [326, 132, 38, 20, 12, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [326, 132, 38, 20, 12, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [326, 132, 38, 20, 12, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [326, 134, 38, 20, 14, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [326, 134, 38, 20, 14, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [326, 134, 38, 20, 14, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [270, 136, 72, 38, 20, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [270, 136, 72, 38, 20, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [270, 136, 72, 38, 20, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [260, 136, 64, 36, 20, 2, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [260, 136, 64, 36, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 136, 64, 36, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [326, 136, 38, 20, 1] ≤ spanCodes [260, 128, 66, 38, 20, 8, 1]
    apply step109wc235_spanCodes_le_of_gens [326, 136, 38, 20, 1] (spanCodes [260, 128, 66, 38, 20, 8, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 128, 66, 38, 20, 8, 1] n (by fin_cases hn <;> decide)

theorem o235CoverSound_wc (i : Fin 12) (M : Mat3) (h : o235Cover_wc i M) : M ∈ o235SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [326, 130, 38, 20, 10, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [326, 130, 38, 20, 10, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 136, 68, 38, 20, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 136, 68, 38, 20, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 136, 70, 38, 20, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 136, 70, 38, 20, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [266, 136, 76, 38, 20, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 136, 76, 38, 20, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 136, 78, 38, 20, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 136, 78, 38, 20, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [322, 136, 34, 16, 4, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 136, 34, 16, 4, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [320, 136, 32, 18, 6, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [320, 136, 32, 18, 6, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [326, 132, 38, 20, 12, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [326, 132, 38, 20, 12, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [326, 134, 38, 20, 14, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [326, 134, 38, 20, 14, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [270, 136, 72, 38, 20, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [270, 136, 72, 38, 20, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 136, 64, 36, 20, 2, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 136, 64, 36, 20, 2, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 128, 66, 38, 20, 8, 1]
    unfold o235Cover_wc o235CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 66, 38, 20, 8, 1] (step109wc235MatrixCodeNat M) h
    rwa [step109wc235_codeMat_matrixCode_all] at hspan

private theorem o235Cert_wc : (12 - 1) * 15 < ∑ i : Fin 12, o235Lambda_wc i * o235SourceLb_wc i := by
  simp only [o235Lambda_wc, o235SourceLb_wc]; decide
private theorem o235LambdaSum_wc : 1 ≤ ∑ i : Fin 12, o235Lambda_wc i := by
  simp only [o235Lambda_wc]; decide

theorem o235Lb16_wc
    (hSource : ∀ i : Fin 12, QuotientRankAtLeast (o235SourceU_wc i) (o235SourceLb_wc i)) :
    QuotientRankAtLeast o235W_wc 16 :=
  quotientRankAtLeast_of_contradiction o235W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o235SourceU_wc o235SourceLb_wc
      o235Lambda_wc 1 15
      o235Cover_wc o235W_le_source_wc hSource
      o235LambdaSum_wc o235CoverSound_wc
      (fun M => o235MatCoverage_wc M) (by omega) o235Cert_wc D)

end QiushiMatmul
