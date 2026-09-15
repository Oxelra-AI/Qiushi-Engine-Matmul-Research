import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 128, exact manifest basis [384, 96, 12, 2, 1]. -/
def o128W_wc : Submodule F2 Mat3 := spanCodes [384, 96, 12, 2, 1]

private theorem step109wc128_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc128MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc128_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc128MatrixCodeNat M) = M := by decide

private theorem step109wc128_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc128_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o128SourceU_wc : Fin 12 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [260, 132, 96, 12, 2, 1]
  | ⟨1, _⟩ => spanCodes [292, 164, 96, 12, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 128, 96, 20, 12, 2, 1]
  | ⟨3, _⟩ => spanCodes [276, 148, 84, 52, 12, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 128, 80, 48, 12, 2, 1]
  | ⟨5, _⟩ => spanCodes [272, 144, 64, 32, 12, 2, 1]
  | ⟨6, _⟩ => spanCodes [288, 160, 96, 16, 12, 2, 1]
  | ⟨7, _⟩ => spanCodes [272, 144, 68, 36, 12, 2, 1]
  | ⟨8, _⟩ => spanCodes [276, 148, 64, 32, 12, 2, 1]
  | ⟨9, _⟩ => spanCodes [384, 96, 8, 4, 2, 1]
  | ⟨10, _⟩ => spanCodes [384, 80, 48, 8, 4, 2, 1]
  | ⟨11, _⟩ => spanCodes [384, 64, 32, 16, 8, 4, 2, 1]
  | ⟨k + 12, h⟩ => absurd h (by omega)

def o128SourceLb_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [14, 14, 12, 12, 12, 12, 12, 12, 12, 11, 9, 3].getD k 0

def o128Lambda_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [3, 3, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1].getD k 0

def o128CoverB_wc : Fin 12 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [260, 132, 96, 12, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [292, 164, 96, 12, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 128, 96, 20, 12, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [276, 148, 84, 52, 12, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 128, 80, 48, 12, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [272, 144, 64, 32, 12, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [288, 160, 96, 16, 12, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [272, 144, 68, 36, 12, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [276, 148, 64, 32, 12, 2, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [384, 96, 8, 4, 2, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [384, 80, 48, 8, 4, 2, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [384, 64, 32, 16, 8, 4, 2, 1] c
  | ⟨k + 12, h⟩, _ => absurd h (by omega)

def o128Cover_wc (i : Fin 12) (M : Mat3) : Prop :=
  o128CoverB_wc i (step109wc128MatrixCodeNat M) = true

theorem o128CodeCoverage_wc (c : Fin 512) :
    3 ≤ ∑ i : Fin 12, if o128CoverB_wc i c.val = true then o128Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o128MatCoverage_wc (M : Mat3) :
    3 ≤ ∑ i : Fin 12, if o128Cover_wc i M then o128Lambda_wc i else 0 := by
  have h := o128CodeCoverage_wc ⟨step109wc128MatrixCodeNat M, step109wc128_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o128CoverB_wc i (step109wc128MatrixCodeNat M) <;> simp [o128Cover_wc, hb]

theorem o128W_le_source_wc (i : Fin 12) : o128W_wc ≤ o128SourceU_wc i := by
  fin_cases i
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [260, 132, 96, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [260, 132, 96, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [292, 164, 96, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [292, 164, 96, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 164, 96, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [256, 128, 96, 20, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [256, 128, 96, 20, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 20, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [276, 148, 84, 52, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [276, 148, 84, 52, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 148, 84, 52, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [256, 128, 80, 48, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [256, 128, 80, 48, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 48, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [272, 144, 64, 32, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [272, 144, 64, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 144, 64, 32, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [288, 160, 96, 16, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [288, 160, 96, 16, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 16, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [272, 144, 68, 36, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [272, 144, 68, 36, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 36, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [276, 148, 64, 32, 12, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [276, 148, 64, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 148, 64, 32, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [384, 96, 8, 4, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [384, 96, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [384, 80, 48, 8, 4, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [384, 80, 48, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 80, 48, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 12, 2, 1] ≤ spanCodes [384, 64, 32, 16, 8, 4, 2, 1]
    apply step109wc128_spanCodes_le_of_gens [384, 96, 12, 2, 1] (spanCodes [384, 64, 32, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 64, 32, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o128CoverSound_wc (i : Fin 12) (M : Mat3) (h : o128Cover_wc i M) : M ∈ o128SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [260, 132, 96, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 164, 96, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 164, 96, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 96, 20, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 20, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 148, 84, 52, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 148, 84, 52, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 80, 48, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 48, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 144, 64, 32, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 64, 32, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 96, 16, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 16, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 144, 68, 36, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 36, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 148, 64, 32, 12, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 148, 64, 32, 12, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 96, 8, 4, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 4, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 80, 48, 8, 4, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 80, 48, 8, 4, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 64, 32, 16, 8, 4, 2, 1]
    unfold o128Cover_wc o128CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 64, 32, 16, 8, 4, 2, 1] (step109wc128MatrixCodeNat M) h
    rwa [step109wc128_codeMat_matrixCode_all] at hspan

private theorem o128Cert_wc : (19 - 3) * 14 < ∑ i : Fin 12, o128Lambda_wc i * o128SourceLb_wc i := by
  simp only [o128Lambda_wc, o128SourceLb_wc]; decide
private theorem o128LambdaSum_wc : 3 ≤ ∑ i : Fin 12, o128Lambda_wc i := by
  simp only [o128Lambda_wc]; decide

theorem o128Lb15_wc
    (hSource : ∀ i : Fin 12, QuotientRankAtLeast (o128SourceU_wc i) (o128SourceLb_wc i)) :
    QuotientRankAtLeast o128W_wc 15 :=
  quotientRankAtLeast_of_contradiction o128W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o128SourceU_wc o128SourceLb_wc
      o128Lambda_wc 3 14
      o128Cover_wc o128W_le_source_wc hSource
      o128LambdaSum_wc o128CoverSound_wc
      (fun M => o128MatCoverage_wc M) (by omega) o128Cert_wc D)

end QiushiMatmul
