import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 140, exact manifest basis [256, 84, 32, 2, 1]. -/
def o140W_wc : Submodule F2 Mat3 := spanCodes [256, 84, 32, 2, 1]

private theorem step109wc140_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc140MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc140_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc140MatrixCodeNat M) = M := by decide

private theorem step109wc140_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc140_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o140SourceU_wc : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 84, 32, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [256, 76, 32, 24, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 140, 84, 32, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 148, 84, 32, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 128, 80, 32, 4, 2, 1]
  | ⟨5, _⟩ => spanCodes [256, 132, 72, 32, 28, 2, 1]
  | ⟨6, _⟩ => spanCodes [256, 136, 68, 32, 16, 2, 1]
  | ⟨7, _⟩ => spanCodes [256, 136, 64, 32, 20, 2, 1]
  | ⟨8, _⟩ => spanCodes [256, 144, 84, 32, 12, 2, 1]
  | ⟨k + 9, h⟩ => absurd h (by omega)

def o140SourceLb_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [12, 12, 12, 12, 9, 12, 12, 12, 12].getD k 0

def o140Lambda_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o140CoverB_wc : Fin 9 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 84, 32, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 76, 32, 24, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 140, 84, 32, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 148, 84, 32, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 128, 80, 32, 4, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 132, 72, 32, 28, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 136, 68, 32, 16, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 136, 64, 32, 20, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 144, 84, 32, 12, 2, 1] c
  | ⟨k + 9, h⟩, _ => absurd h (by omega)

def o140Cover_wc (i : Fin 9) (M : Mat3) : Prop :=
  o140CoverB_wc i (step109wc140MatrixCodeNat M) = true

theorem o140CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 9, if o140CoverB_wc i c.val = true then o140Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o140MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o140Cover_wc i M then o140Lambda_wc i else 0 := by
  have h := o140CodeCoverage_wc ⟨step109wc140MatrixCodeNat M, step109wc140_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o140CoverB_wc i (step109wc140MatrixCodeNat M) <;> simp [o140Cover_wc, hb]

theorem o140W_le_source_wc (i : Fin 9) : o140W_wc ≤ o140SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 84, 32, 8, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 84, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 84, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 76, 32, 24, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 76, 32, 24, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 76, 32, 24, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 140, 84, 32, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 140, 84, 32, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 140, 84, 32, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 148, 84, 32, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 148, 84, 32, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 148, 84, 32, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 128, 80, 32, 4, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 128, 80, 32, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 32, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 132, 72, 32, 28, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 132, 72, 32, 28, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 72, 32, 28, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 136, 68, 32, 16, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 136, 68, 32, 16, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 136, 68, 32, 16, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 136, 64, 32, 20, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 136, 64, 32, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 136, 64, 32, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 84, 32, 2, 1] ≤ spanCodes [256, 144, 84, 32, 12, 2, 1]
    apply step109wc140_spanCodes_le_of_gens [256, 84, 32, 2, 1] (spanCodes [256, 144, 84, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 84, 32, 12, 2, 1] n (by fin_cases hn <;> decide)

theorem o140CoverSound_wc (i : Fin 9) (M : Mat3) (h : o140Cover_wc i M) : M ∈ o140SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 84, 32, 8, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 84, 32, 8, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 76, 32, 24, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 76, 32, 24, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 140, 84, 32, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 140, 84, 32, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 148, 84, 32, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 148, 84, 32, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 80, 32, 4, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 32, 4, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 72, 32, 28, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 72, 32, 28, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 136, 68, 32, 16, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 136, 68, 32, 16, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 136, 64, 32, 20, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 136, 64, 32, 20, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 84, 32, 12, 2, 1]
    unfold o140Cover_wc o140CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 84, 32, 12, 2, 1] (step109wc140MatrixCodeNat M) h
    rwa [step109wc140_codeMat_matrixCode_all] at hspan

private theorem o140Cert_wc : (9 - 1) * 13 < ∑ i : Fin 9, o140Lambda_wc i * o140SourceLb_wc i := by
  simp only [o140Lambda_wc, o140SourceLb_wc]; decide
private theorem o140LambdaSum_wc : 1 ≤ ∑ i : Fin 9, o140Lambda_wc i := by
  simp only [o140Lambda_wc]; decide

theorem o140Lb14_wc
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o140SourceU_wc i) (o140SourceLb_wc i)) :
    QuotientRankAtLeast o140W_wc 14 :=
  quotientRankAtLeast_of_contradiction o140W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o140SourceU_wc o140SourceLb_wc
      o140Lambda_wc 1 13
      o140Cover_wc o140W_le_source_wc hSource
      o140LambdaSum_wc o140CoverSound_wc
      (fun M => o140MatCoverage_wc M) (by omega) o140Cert_wc D)

end QiushiMatmul
