import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 179, exact manifest basis [128, 84, 32, 10, 1]. -/
def o179W_wc : Submodule F2 Mat3 := spanCodes [128, 84, 32, 10, 1]

private theorem step109wc179_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc179MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc179_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc179MatrixCodeNat M) = M := by decide

private theorem step109wc179_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc179_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o179SourceU_wc : Fin 11 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [258, 128, 84, 32, 10, 1]
  | ⟨1, _⟩ => spanCodes [260, 128, 84, 32, 10, 1]
  | ⟨2, _⟩ => spanCodes [262, 128, 84, 32, 10, 1]
  | ⟨3, _⟩ => spanCodes [274, 128, 84, 32, 10, 1]
  | ⟨4, _⟩ => spanCodes [276, 128, 84, 32, 10, 1]
  | ⟨5, _⟩ => spanCodes [278, 128, 84, 32, 10, 1]
  | ⟨6, _⟩ => spanCodes [256, 128, 68, 32, 16, 10, 1]
  | ⟨7, _⟩ => spanCodes [128, 80, 32, 8, 4, 2, 1]
  | ⟨8, _⟩ => spanCodes [128, 64, 32, 18, 10, 6, 1]
  | ⟨9, _⟩ => spanCodes [128, 66, 32, 18, 10, 4, 1]
  | ⟨10, _⟩ => spanCodes [128, 64, 32, 20, 8, 2, 1]
  | ⟨k + 11, h⟩ => absurd h (by omega)

def o179SourceLb_wc : Fin 11 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 14, 14, 12, 9, 9, 9, 9].getD k 0

def o179Lambda_wc : Fin 11 → ℕ
  | ⟨k, _⟩ => [2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1].getD k 0

def o179CoverB_wc : Fin 11 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [258, 128, 84, 32, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [260, 128, 84, 32, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [262, 128, 84, 32, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [274, 128, 84, 32, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [276, 128, 84, 32, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [278, 128, 84, 32, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 128, 68, 32, 16, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [128, 80, 32, 8, 4, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [128, 64, 32, 18, 10, 6, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [128, 66, 32, 18, 10, 4, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [128, 64, 32, 20, 8, 2, 1] c
  | ⟨k + 11, h⟩, _ => absurd h (by omega)

def o179Cover_wc (i : Fin 11) (M : Mat3) : Prop :=
  o179CoverB_wc i (step109wc179MatrixCodeNat M) = true

theorem o179CodeCoverage_wc (c : Fin 512) :
    2 ≤ ∑ i : Fin 11, if o179CoverB_wc i c.val = true then o179Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o179MatCoverage_wc (M : Mat3) :
    2 ≤ ∑ i : Fin 11, if o179Cover_wc i M then o179Lambda_wc i else 0 := by
  have h := o179CodeCoverage_wc ⟨step109wc179MatrixCodeNat M, step109wc179_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o179CoverB_wc i (step109wc179MatrixCodeNat M) <;> simp [o179Cover_wc, hb]

theorem o179W_le_source_wc (i : Fin 11) : o179W_wc ≤ o179SourceU_wc i := by
  fin_cases i
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 84, 32, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [258, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [260, 128, 84, 32, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [260, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [262, 128, 84, 32, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [262, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [274, 128, 84, 32, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [274, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [276, 128, 84, 32, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [276, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [278, 128, 84, 32, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [278, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [256, 128, 68, 32, 16, 10, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [256, 128, 68, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [128, 80, 32, 8, 4, 2, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [128, 80, 32, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [128, 64, 32, 18, 10, 6, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [128, 64, 32, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 18, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [128, 66, 32, 18, 10, 4, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [128, 66, 32, 18, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 66, 32, 18, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 84, 32, 10, 1] ≤ spanCodes [128, 64, 32, 20, 8, 2, 1]
    apply step109wc179_spanCodes_le_of_gens [128, 84, 32, 10, 1] (spanCodes [128, 64, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o179CoverSound_wc (i : Fin 11) (M : Mat3) (h : o179Cover_wc i M) : M ∈ o179SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [258, 128, 84, 32, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 84, 32, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 128, 84, 32, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 84, 32, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 84, 32, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 84, 32, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 128, 84, 32, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 128, 84, 32, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 128, 84, 32, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 128, 84, 32, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [278, 128, 84, 32, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 128, 84, 32, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 68, 32, 16, 10, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 16, 10, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 80, 32, 8, 4, 2, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 80, 32, 8, 4, 2, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 64, 32, 18, 10, 6, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 18, 10, 6, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 66, 32, 18, 10, 4, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 66, 32, 18, 10, 4, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 64, 32, 20, 8, 2, 1]
    unfold o179Cover_wc o179CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 64, 32, 20, 8, 2, 1] (step109wc179MatrixCodeNat M) h
    rwa [step109wc179_codeMat_matrixCode_all] at hspan

private theorem o179Cert_wc : (18 - 2) * 14 < ∑ i : Fin 11, o179Lambda_wc i * o179SourceLb_wc i := by
  simp only [o179Lambda_wc, o179SourceLb_wc]; decide
private theorem o179LambdaSum_wc : 2 ≤ ∑ i : Fin 11, o179Lambda_wc i := by
  simp only [o179Lambda_wc]; decide

theorem o179Lb15_wc
    (hSource : ∀ i : Fin 11, QuotientRankAtLeast (o179SourceU_wc i) (o179SourceLb_wc i)) :
    QuotientRankAtLeast o179W_wc 15 :=
  quotientRankAtLeast_of_contradiction o179W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o179SourceU_wc o179SourceLb_wc
      o179Lambda_wc 2 14
      o179Cover_wc o179W_le_source_wc hSource
      o179LambdaSum_wc o179CoverSound_wc
      (fun M => o179MatCoverage_wc M) (by omega) o179Cert_wc D)

end QiushiMatmul
