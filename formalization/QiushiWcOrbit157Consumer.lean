import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 157, exact manifest basis [128, 32, 20, 10, 1]. -/
def o157W_wc : Submodule F2 Mat3 := spanCodes [128, 32, 20, 10, 1]

private theorem step109wc157_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc157MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc157_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc157MatrixCodeNat M) = M := by decide

private theorem step109wc157_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc157_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o157SourceU_wc : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [128, 68, 32, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [262, 128, 32, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [322, 128, 32, 20, 10, 1]
  | ⟨3, _⟩ => spanCodes [128, 32, 20, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [128, 32, 16, 10, 4, 1]
  | ⟨5, _⟩ => spanCodes [128, 32, 18, 10, 6, 1]
  | ⟨6, _⟩ => spanCodes [258, 128, 66, 32, 20, 10, 1]
  | ⟨7, _⟩ => spanCodes [260, 128, 64, 32, 20, 10, 1]
  | ⟨8, _⟩ => spanCodes [256, 128, 70, 32, 20, 10, 1]
  | ⟨k + 9, h⟩ => absurd h (by omega)

def o157SourceLb_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 12, 12, 12, 12, 12, 12].getD k 0

def o157Lambda_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o157CoverB_wc : Fin 9 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [128, 68, 32, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 128, 32, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [322, 128, 32, 20, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [128, 32, 20, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [128, 32, 16, 10, 4, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [128, 32, 18, 10, 6, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [258, 128, 66, 32, 20, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [260, 128, 64, 32, 20, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 128, 70, 32, 20, 10, 1] c
  | ⟨k + 9, h⟩, _ => absurd h (by omega)

def o157Cover_wc (i : Fin 9) (M : Mat3) : Prop :=
  o157CoverB_wc i (step109wc157MatrixCodeNat M) = true

theorem o157CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 9, if o157CoverB_wc i c.val = true then o157Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o157MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o157Cover_wc i M then o157Lambda_wc i else 0 := by
  have h := o157CodeCoverage_wc ⟨step109wc157MatrixCodeNat M, step109wc157_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o157CoverB_wc i (step109wc157MatrixCodeNat M) <;> simp [o157Cover_wc, hb]

theorem o157W_le_source_wc (i : Fin 9) : o157W_wc ≤ o157SourceU_wc i := by
  fin_cases i
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [128, 68, 32, 20, 10, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [128, 68, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [262, 128, 32, 20, 10, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [262, 128, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [322, 128, 32, 20, 10, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [322, 128, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [322, 128, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [128, 32, 20, 8, 2, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [128, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [128, 32, 16, 10, 4, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [128, 32, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 32, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [128, 32, 18, 10, 6, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [128, 32, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 32, 18, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [258, 128, 66, 32, 20, 10, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [258, 128, 66, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [260, 128, 64, 32, 20, 10, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [260, 128, 64, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 128, 64, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [128, 32, 20, 10, 1] ≤ spanCodes [256, 128, 70, 32, 20, 10, 1]
    apply step109wc157_spanCodes_le_of_gens [128, 32, 20, 10, 1] (spanCodes [256, 128, 70, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 70, 32, 20, 10, 1] n (by fin_cases hn <;> decide)

theorem o157CoverSound_wc (i : Fin 9) (M : Mat3) (h : o157Cover_wc i M) : M ∈ o157SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [128, 68, 32, 20, 10, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 68, 32, 20, 10, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 32, 20, 10, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 32, 20, 10, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [322, 128, 32, 20, 10, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 128, 32, 20, 10, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 32, 20, 8, 2, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 32, 20, 8, 2, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 32, 16, 10, 4, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 32, 16, 10, 4, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 32, 18, 10, 6, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 32, 18, 10, 6, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 66, 32, 20, 10, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 20, 10, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 128, 64, 32, 20, 10, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 64, 32, 20, 10, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 70, 32, 20, 10, 1]
    unfold o157Cover_wc o157CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 70, 32, 20, 10, 1] (step109wc157MatrixCodeNat M) h
    rwa [step109wc157_codeMat_matrixCode_all] at hspan

private theorem o157Cert_wc : (9 - 1) * 14 < ∑ i : Fin 9, o157Lambda_wc i * o157SourceLb_wc i := by
  simp only [o157Lambda_wc, o157SourceLb_wc]; decide
private theorem o157LambdaSum_wc : 1 ≤ ∑ i : Fin 9, o157Lambda_wc i := by
  simp only [o157Lambda_wc]; decide

theorem o157Lb15_wc
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o157SourceU_wc i) (o157SourceLb_wc i)) :
    QuotientRankAtLeast o157W_wc 15 :=
  quotientRankAtLeast_of_contradiction o157W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o157SourceU_wc o157SourceLb_wc
      o157Lambda_wc 1 14
      o157Cover_wc o157W_le_source_wc hSource
      o157LambdaSum_wc o157CoverSound_wc
      (fun M => o157MatCoverage_wc M) (by omega) o157Cert_wc D)

end QiushiMatmul
