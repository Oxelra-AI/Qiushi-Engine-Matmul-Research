import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 111, exact manifest basis [256, 96, 8, 2, 1]. -/
def o111W_wc : Submodule F2 Mat3 := spanCodes [256, 96, 8, 2, 1]

private theorem step109wc111_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc111MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc111_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc111MatrixCodeNat M) = M := by decide

private theorem step109wc111_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc111_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o111SourceU_wc : Fin 8 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 96, 8, 4, 2, 1]
  | ⟨1, _⟩ => spanCodes [256, 68, 36, 20, 8, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 132, 96, 20, 8, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 128, 96, 20, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 132, 96, 16, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [256, 164, 96, 20, 8, 2, 1]
  | ⟨6, _⟩ => spanCodes [256, 160, 96, 20, 8, 2, 1]
  | ⟨7, _⟩ => spanCodes [256, 64, 32, 20, 8, 2, 1]
  | ⟨k + 8, h⟩ => absurd h (by omega)

def o111SourceLb_wc : Fin 8 → ℕ
  | ⟨k, _⟩ => [12, 12, 12, 12, 12, 12, 12, 9].getD k 0

def o111Lambda_wc : Fin 8 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o111CoverB_wc : Fin 8 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 96, 8, 4, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 68, 36, 20, 8, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 132, 96, 20, 8, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 128, 96, 20, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 132, 96, 16, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 164, 96, 20, 8, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 160, 96, 20, 8, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 64, 32, 20, 8, 2, 1] c
  | ⟨k + 8, h⟩, _ => absurd h (by omega)

def o111Cover_wc (i : Fin 8) (M : Mat3) : Prop :=
  o111CoverB_wc i (step109wc111MatrixCodeNat M) = true

theorem o111CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 8, if o111CoverB_wc i c.val = true then o111Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o111MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 8, if o111Cover_wc i M then o111Lambda_wc i else 0 := by
  have h := o111CodeCoverage_wc ⟨step109wc111MatrixCodeNat M, step109wc111_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o111CoverB_wc i (step109wc111MatrixCodeNat M) <;> simp [o111Cover_wc, hb]

theorem o111W_le_source_wc (i : Fin 8) : o111W_wc ≤ o111SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 96, 8, 4, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 96, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 68, 36, 20, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 68, 36, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 36, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 132, 96, 20, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 132, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 128, 96, 20, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 128, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 132, 96, 16, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 132, 96, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 164, 96, 20, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 164, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 160, 96, 20, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 160, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 96, 8, 2, 1] ≤ spanCodes [256, 64, 32, 20, 8, 2, 1]
    apply step109wc111_spanCodes_le_of_gens [256, 96, 8, 2, 1] (spanCodes [256, 64, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 64, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o111CoverSound_wc (i : Fin 8) (M : Mat3) (h : o111Cover_wc i M) : M ∈ o111SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 96, 8, 4, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 4, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 68, 36, 20, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 36, 20, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 96, 20, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 20, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 96, 20, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 20, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 96, 16, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 96, 16, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 164, 96, 20, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 96, 20, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 96, 20, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 96, 20, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 64, 32, 20, 8, 2, 1]
    unfold o111Cover_wc o111CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 64, 32, 20, 8, 2, 1] (step109wc111MatrixCodeNat M) h
    rwa [step109wc111_codeMat_matrixCode_all] at hspan

private theorem o111Cert_wc : (8 - 1) * 13 < ∑ i : Fin 8, o111Lambda_wc i * o111SourceLb_wc i := by
  simp only [o111Lambda_wc, o111SourceLb_wc]; decide
private theorem o111LambdaSum_wc : 1 ≤ ∑ i : Fin 8, o111Lambda_wc i := by
  simp only [o111Lambda_wc]; decide

theorem o111Lb14_wc
    (hSource : ∀ i : Fin 8, QuotientRankAtLeast (o111SourceU_wc i) (o111SourceLb_wc i)) :
    QuotientRankAtLeast o111W_wc 14 :=
  quotientRankAtLeast_of_contradiction o111W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o111SourceU_wc o111SourceLb_wc
      o111Lambda_wc 1 13
      o111Cover_wc o111W_le_source_wc hSource
      o111LambdaSum_wc o111CoverSound_wc
      (fun M => o111MatCoverage_wc M) (by omega) o111Cert_wc D)

end QiushiMatmul
