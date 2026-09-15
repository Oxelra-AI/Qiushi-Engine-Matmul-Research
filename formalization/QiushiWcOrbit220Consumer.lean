import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 220, exact manifest basis [334, 192, 36, 16, 1]. -/
def o220W_wc : Submodule F2 Mat3 := spanCodes [334, 192, 36, 16, 1]

private theorem step109wc220_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc220MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc220_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc220MatrixCodeNat M) = M := by decide

private theorem step109wc220_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc220_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o220SourceU_wc : Fin 6 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [258, 140, 76, 36, 16, 1]
  | ⟨1, _⟩ => spanCodes [326, 192, 36, 16, 8, 1]
  | ⟨2, _⟩ => spanCodes [264, 128, 64, 34, 16, 6, 1]
  | ⟨3, _⟩ => spanCodes [264, 130, 66, 32, 16, 4, 1]
  | ⟨4, _⟩ => spanCodes [256, 132, 68, 36, 16, 10, 1]
  | ⟨5, _⟩ => spanCodes [260, 132, 68, 36, 16, 12, 2, 1]
  | ⟨k + 6, h⟩ => absurd h (by omega)

def o220SourceLb_wc : Fin 6 → ℕ
  | ⟨k, _⟩ => [14, 12, 12, 12, 12, 9].getD k 0

def o220Lambda_wc : Fin 6 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1].getD k 0

def o220CoverB_wc : Fin 6 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [258, 140, 76, 36, 16, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [326, 192, 36, 16, 8, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [264, 128, 64, 34, 16, 6, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [264, 130, 66, 32, 16, 4, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 132, 68, 36, 16, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [260, 132, 68, 36, 16, 12, 2, 1] c
  | ⟨k + 6, h⟩, _ => absurd h (by omega)

def o220Cover_wc (i : Fin 6) (M : Mat3) : Prop :=
  o220CoverB_wc i (step109wc220MatrixCodeNat M) = true

theorem o220CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 6, if o220CoverB_wc i c.val = true then o220Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o220MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 6, if o220Cover_wc i M then o220Lambda_wc i else 0 := by
  have h := o220CodeCoverage_wc ⟨step109wc220MatrixCodeNat M, step109wc220_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o220CoverB_wc i (step109wc220MatrixCodeNat M) <;> simp [o220Cover_wc, hb]

theorem o220W_le_source_wc (i : Fin 6) : o220W_wc ≤ o220SourceU_wc i := by
  fin_cases i
  · change spanCodes [334, 192, 36, 16, 1] ≤ spanCodes [258, 140, 76, 36, 16, 1]
    apply step109wc220_spanCodes_le_of_gens [334, 192, 36, 16, 1] (spanCodes [258, 140, 76, 36, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 140, 76, 36, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [334, 192, 36, 16, 1] ≤ spanCodes [326, 192, 36, 16, 8, 1]
    apply step109wc220_spanCodes_le_of_gens [334, 192, 36, 16, 1] (spanCodes [326, 192, 36, 16, 8, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [326, 192, 36, 16, 8, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [334, 192, 36, 16, 1] ≤ spanCodes [264, 128, 64, 34, 16, 6, 1]
    apply step109wc220_spanCodes_le_of_gens [334, 192, 36, 16, 1] (spanCodes [264, 128, 64, 34, 16, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 128, 64, 34, 16, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [334, 192, 36, 16, 1] ≤ spanCodes [264, 130, 66, 32, 16, 4, 1]
    apply step109wc220_spanCodes_le_of_gens [334, 192, 36, 16, 1] (spanCodes [264, 130, 66, 32, 16, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 130, 66, 32, 16, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [334, 192, 36, 16, 1] ≤ spanCodes [256, 132, 68, 36, 16, 10, 1]
    apply step109wc220_spanCodes_le_of_gens [334, 192, 36, 16, 1] (spanCodes [256, 132, 68, 36, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [334, 192, 36, 16, 1] ≤ spanCodes [260, 132, 68, 36, 16, 12, 2, 1]
    apply step109wc220_spanCodes_le_of_gens [334, 192, 36, 16, 1] (spanCodes [260, 132, 68, 36, 16, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 36, 16, 12, 2, 1] n (by fin_cases hn <;> decide)

theorem o220CoverSound_wc (i : Fin 6) (M : Mat3) (h : o220Cover_wc i M) : M ∈ o220SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [258, 140, 76, 36, 16, 1]
    unfold o220Cover_wc o220CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 140, 76, 36, 16, 1] (step109wc220MatrixCodeNat M) h
    rwa [step109wc220_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [326, 192, 36, 16, 8, 1]
    unfold o220Cover_wc o220CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [326, 192, 36, 16, 8, 1] (step109wc220MatrixCodeNat M) h
    rwa [step109wc220_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 128, 64, 34, 16, 6, 1]
    unfold o220Cover_wc o220CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 128, 64, 34, 16, 6, 1] (step109wc220MatrixCodeNat M) h
    rwa [step109wc220_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 130, 66, 32, 16, 4, 1]
    unfold o220Cover_wc o220CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 130, 66, 32, 16, 4, 1] (step109wc220MatrixCodeNat M) h
    rwa [step109wc220_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 68, 36, 16, 10, 1]
    unfold o220Cover_wc o220CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 68, 36, 16, 10, 1] (step109wc220MatrixCodeNat M) h
    rwa [step109wc220_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 132, 68, 36, 16, 12, 2, 1]
    unfold o220Cover_wc o220CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 68, 36, 16, 12, 2, 1] (step109wc220MatrixCodeNat M) h
    rwa [step109wc220_codeMat_matrixCode_all] at hspan

private theorem o220Cert_wc : (6 - 1) * 14 < ∑ i : Fin 6, o220Lambda_wc i * o220SourceLb_wc i := by
  simp only [o220Lambda_wc, o220SourceLb_wc]; decide
private theorem o220LambdaSum_wc : 1 ≤ ∑ i : Fin 6, o220Lambda_wc i := by
  simp only [o220Lambda_wc]; decide

theorem o220Lb15_wc
    (hSource : ∀ i : Fin 6, QuotientRankAtLeast (o220SourceU_wc i) (o220SourceLb_wc i)) :
    QuotientRankAtLeast o220W_wc 15 :=
  quotientRankAtLeast_of_contradiction o220W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o220SourceU_wc o220SourceLb_wc
      o220Lambda_wc 1 14
      o220Cover_wc o220W_le_source_wc hSource
      o220LambdaSum_wc o220CoverSound_wc
      (fun M => o220MatCoverage_wc M) (by omega) o220Cert_wc D)

end QiushiMatmul
