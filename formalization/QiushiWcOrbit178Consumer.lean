import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 178, exact manifest basis [272, 68, 32, 10, 1]. -/
def o178W_wc : Submodule F2 Mat3 := spanCodes [272, 68, 32, 10, 1]

private theorem step109wc178_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc178MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc178_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc178MatrixCodeNat M) = M := by decide

private theorem step109wc178_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc178_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o178SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [272, 68, 32, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [272, 64, 32, 10, 4, 1]
  | ⟨2, _⟩ => spanCodes [262, 68, 32, 22, 10, 1]
  | ⟨3, _⟩ => spanCodes [272, 128, 68, 32, 10, 1]
  | ⟨4, _⟩ => spanCodes [272, 130, 68, 32, 10, 1]
  | ⟨5, _⟩ => spanCodes [272, 132, 68, 32, 10, 1]
  | ⟨6, _⟩ => spanCodes [272, 144, 68, 32, 10, 1]
  | ⟨7, _⟩ => spanCodes [272, 146, 68, 32, 10, 1]
  | ⟨8, _⟩ => spanCodes [272, 148, 68, 32, 10, 1]
  | ⟨9, _⟩ => spanCodes [258, 68, 32, 18, 10, 1]
  | ⟨10, _⟩ => spanCodes [260, 68, 32, 20, 10, 1]
  | ⟨11, _⟩ => spanCodes [272, 134, 68, 32, 10, 1]
  | ⟨12, _⟩ => spanCodes [272, 150, 68, 32, 10, 1]
  | ⟨13, _⟩ => spanCodes [272, 66, 32, 10, 6, 1]
  | ⟨14, _⟩ => spanCodes [256, 68, 32, 16, 10, 1]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o178SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14, 13, 12].getD k 0

def o178Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o178CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [272, 68, 32, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [272, 64, 32, 10, 4, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [262, 68, 32, 22, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [272, 128, 68, 32, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [272, 130, 68, 32, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [272, 132, 68, 32, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [272, 144, 68, 32, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [272, 146, 68, 32, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [272, 148, 68, 32, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [258, 68, 32, 18, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [260, 68, 32, 20, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [272, 134, 68, 32, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [272, 150, 68, 32, 10, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [272, 66, 32, 10, 6, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [256, 68, 32, 16, 10, 1] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o178Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o178CoverB_wc i (step109wc178MatrixCodeNat M) = true

theorem o178CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 15, if o178CoverB_wc i c.val = true then o178Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o178MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 15, if o178Cover_wc i M then o178Lambda_wc i else 0 := by
  have h := o178CodeCoverage_wc ⟨step109wc178MatrixCodeNat M, step109wc178_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o178CoverB_wc i (step109wc178MatrixCodeNat M) <;> simp [o178Cover_wc, hb]

theorem o178W_le_source_wc (i : Fin 15) : o178W_wc ≤ o178SourceU_wc i := by
  fin_cases i
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 68, 32, 8, 2, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 68, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 68, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 64, 32, 10, 4, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 64, 32, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [262, 68, 32, 22, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [262, 68, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 68, 32, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 128, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 128, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 130, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 130, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 130, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 132, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 132, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 144, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 144, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 146, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 146, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 146, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 148, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 148, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 148, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [258, 68, 32, 18, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [258, 68, 32, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [260, 68, 32, 20, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [260, 68, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 68, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 134, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 134, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 134, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 150, 68, 32, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 150, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 150, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [272, 66, 32, 10, 6, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [272, 66, 32, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 66, 32, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [272, 68, 32, 10, 1] ≤ spanCodes [256, 68, 32, 16, 10, 1]
    apply step109wc178_spanCodes_le_of_gens [272, 68, 32, 10, 1] (spanCodes [256, 68, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 68, 32, 16, 10, 1] n (by fin_cases hn <;> decide)

theorem o178CoverSound_wc (i : Fin 15) (M : Mat3) (h : o178Cover_wc i M) : M ∈ o178SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [272, 68, 32, 8, 2, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 68, 32, 8, 2, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 64, 32, 10, 4, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 64, 32, 10, 4, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 68, 32, 22, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 68, 32, 22, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 130, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 130, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 132, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 144, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 146, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 146, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 148, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 148, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 68, 32, 18, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 18, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 68, 32, 20, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 68, 32, 20, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 134, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 134, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 150, 68, 32, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 150, 68, 32, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 66, 32, 10, 6, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 66, 32, 10, 6, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 68, 32, 16, 10, 1]
    unfold o178Cover_wc o178CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 68, 32, 16, 10, 1] (step109wc178MatrixCodeNat M) h
    rwa [step109wc178_codeMat_matrixCode_all] at hspan

private theorem o178Cert_wc : (15 - 1) * 15 < ∑ i : Fin 15, o178Lambda_wc i * o178SourceLb_wc i := by
  simp only [o178Lambda_wc, o178SourceLb_wc]; decide
private theorem o178LambdaSum_wc : 1 ≤ ∑ i : Fin 15, o178Lambda_wc i := by
  simp only [o178Lambda_wc]; decide

theorem o178Lb16_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o178SourceU_wc i) (o178SourceLb_wc i)) :
    QuotientRankAtLeast o178W_wc 16 :=
  quotientRankAtLeast_of_contradiction o178W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o178SourceU_wc o178SourceLb_wc
      o178Lambda_wc 1 15
      o178Cover_wc o178W_le_source_wc hSource
      o178LambdaSum_wc o178CoverSound_wc
      (fun M => o178MatCoverage_wc M) (by omega) o178Cert_wc D)

end QiushiMatmul
