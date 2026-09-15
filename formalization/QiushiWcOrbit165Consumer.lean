import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 165, exact manifest basis [288, 96, 20, 10, 1]. -/
def o165W_wc : Submodule F2 Mat3 := spanCodes [288, 96, 20, 10, 1]

private theorem step109wc165_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc165MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc165_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc165MatrixCodeNat M) = M := by decide

private theorem step109wc165_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc165_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o165SourceU_wc : Fin 15 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [260, 68, 36, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [262, 70, 38, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [288, 128, 96, 20, 10, 1]
  | ⟨3, _⟩ => spanCodes [288, 130, 96, 20, 10, 1]
  | ⟨4, _⟩ => spanCodes [288, 132, 96, 20, 10, 1]
  | ⟨5, _⟩ => spanCodes [288, 134, 96, 20, 10, 1]
  | ⟨6, _⟩ => spanCodes [288, 162, 96, 20, 10, 1]
  | ⟨7, _⟩ => spanCodes [288, 164, 96, 20, 10, 1]
  | ⟨8, _⟩ => spanCodes [288, 96, 16, 10, 4, 1]
  | ⟨9, _⟩ => spanCodes [288, 96, 18, 10, 6, 1]
  | ⟨10, _⟩ => spanCodes [256, 64, 32, 20, 10, 1]
  | ⟨11, _⟩ => spanCodes [258, 66, 34, 20, 10, 1]
  | ⟨12, _⟩ => spanCodes [288, 160, 96, 20, 8, 2, 1]
  | ⟨13, _⟩ => spanCodes [288, 164, 96, 20, 8, 2, 1]
  | ⟨14, _⟩ => spanCodes [288, 160, 96, 18, 10, 6, 1]
  | ⟨k + 15, h⟩ => absurd h (by omega)

def o165SourceLb_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 14, 14, 14, 14, 12, 12, 12, 12, 12, 12, 9].getD k 0

def o165Lambda_wc : Fin 15 → ℕ
  | ⟨k, _⟩ => [2, 2, 2, 2, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1].getD k 0

def o165CoverB_wc : Fin 15 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [260, 68, 36, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 70, 38, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [288, 128, 96, 20, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [288, 130, 96, 20, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [288, 132, 96, 20, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [288, 134, 96, 20, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [288, 162, 96, 20, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [288, 164, 96, 20, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [288, 96, 16, 10, 4, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [288, 96, 18, 10, 6, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [256, 64, 32, 20, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [258, 66, 34, 20, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [288, 160, 96, 20, 8, 2, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [288, 164, 96, 20, 8, 2, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [288, 160, 96, 18, 10, 6, 1] c
  | ⟨k + 15, h⟩, _ => absurd h (by omega)

def o165Cover_wc (i : Fin 15) (M : Mat3) : Prop :=
  o165CoverB_wc i (step109wc165MatrixCodeNat M) = true

theorem o165CodeCoverage_wc (c : Fin 512) :
    2 ≤ ∑ i : Fin 15, if o165CoverB_wc i c.val = true then o165Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o165MatCoverage_wc (M : Mat3) :
    2 ≤ ∑ i : Fin 15, if o165Cover_wc i M then o165Lambda_wc i else 0 := by
  have h := o165CodeCoverage_wc ⟨step109wc165MatrixCodeNat M, step109wc165_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o165CoverB_wc i (step109wc165MatrixCodeNat M) <;> simp [o165Cover_wc, hb]

theorem o165W_le_source_wc (i : Fin 15) : o165W_wc ≤ o165SourceU_wc i := by
  fin_cases i
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [260, 68, 36, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [260, 68, 36, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 68, 36, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [262, 70, 38, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [262, 70, 38, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 70, 38, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 128, 96, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 128, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 130, 96, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 130, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 130, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 132, 96, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 132, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 132, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 134, 96, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 134, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 134, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 162, 96, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 162, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 162, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 164, 96, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 164, 96, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 164, 96, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 96, 16, 10, 4, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 96, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 96, 16, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 96, 18, 10, 6, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 96, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 96, 18, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [256, 64, 32, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [256, 64, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 64, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [258, 66, 34, 20, 10, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [258, 66, 34, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 66, 34, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 160, 96, 20, 8, 2, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 160, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 164, 96, 20, 8, 2, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 164, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 164, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [288, 96, 20, 10, 1] ≤ spanCodes [288, 160, 96, 18, 10, 6, 1]
    apply step109wc165_spanCodes_le_of_gens [288, 96, 20, 10, 1] (spanCodes [288, 160, 96, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 18, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o165CoverSound_wc (i : Fin 15) (M : Mat3) (h : o165Cover_wc i M) : M ∈ o165SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [260, 68, 36, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 68, 36, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 70, 38, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 70, 38, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 128, 96, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 128, 96, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 130, 96, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 130, 96, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 132, 96, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 132, 96, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 134, 96, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 134, 96, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 162, 96, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 162, 96, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 164, 96, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 164, 96, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 96, 16, 10, 4, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 96, 16, 10, 4, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 96, 18, 10, 6, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 96, 18, 10, 6, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 64, 32, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 64, 32, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 66, 34, 20, 10, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 66, 34, 20, 10, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 96, 20, 8, 2, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 20, 8, 2, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 164, 96, 20, 8, 2, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 164, 96, 20, 8, 2, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 96, 18, 10, 6, 1]
    unfold o165Cover_wc o165CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 18, 10, 6, 1] (step109wc165MatrixCodeNat M) h
    rwa [step109wc165_codeMat_matrixCode_all] at hspan

private theorem o165Cert_wc : (24 - 2) * 14 < ∑ i : Fin 15, o165Lambda_wc i * o165SourceLb_wc i := by
  simp only [o165Lambda_wc, o165SourceLb_wc]; decide
private theorem o165LambdaSum_wc : 2 ≤ ∑ i : Fin 15, o165Lambda_wc i := by
  simp only [o165Lambda_wc]; decide

theorem o165Lb15_wc
    (hSource : ∀ i : Fin 15, QuotientRankAtLeast (o165SourceU_wc i) (o165SourceLb_wc i)) :
    QuotientRankAtLeast o165W_wc 15 :=
  quotientRankAtLeast_of_contradiction o165W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o165SourceU_wc o165SourceLb_wc
      o165Lambda_wc 2 14
      o165Cover_wc o165W_le_source_wc hSource
      o165LambdaSum_wc o165CoverSound_wc
      (fun M => o165MatCoverage_wc M) (by omega) o165Cert_wc D)

end QiushiMatmul
