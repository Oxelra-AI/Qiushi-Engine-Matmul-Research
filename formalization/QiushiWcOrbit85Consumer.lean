import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 85, exact manifest basis [262, 131, 68, 35, 20, 10]. -/
def o85W_wc : Submodule F2 Mat3 := spanCodes [262, 131, 68, 35, 20, 10]

private theorem step109wc85_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc85MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc85_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc85MatrixCodeNat M) = M := by decide

private theorem step109wc85_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc85_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o85SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [262, 130, 68, 34, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [260, 129, 68, 33, 20, 8, 2]
  | ⟨2, _⟩ => spanCodes [261, 128, 68, 32, 20, 9, 3]
  | ⟨3, _⟩ => spanCodes [258, 131, 64, 35, 16, 10, 4]
  | ⟨4, _⟩ => spanCodes [259, 131, 65, 35, 17, 10, 5]
  | ⟨5, _⟩ => spanCodes [256, 131, 66, 35, 18, 10, 6]
  | ⟨6, _⟩ => spanCodes [257, 131, 67, 35, 19, 10, 7]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o85SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 14, 14, 14].getD k 0

def o85Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o85CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [262, 130, 68, 34, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [260, 129, 68, 33, 20, 8, 2] c
  | ⟨2, _⟩, c => spanContainsCodeCore [261, 128, 68, 32, 20, 9, 3] c
  | ⟨3, _⟩, c => spanContainsCodeCore [258, 131, 64, 35, 16, 10, 4] c
  | ⟨4, _⟩, c => spanContainsCodeCore [259, 131, 65, 35, 17, 10, 5] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 131, 66, 35, 18, 10, 6] c
  | ⟨6, _⟩, c => spanContainsCodeCore [257, 131, 67, 35, 19, 10, 7] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o85Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o85CoverB_wc i (step109wc85MatrixCodeNat M) = true

theorem o85CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o85CoverB_wc i c.val = true then o85Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o85MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o85Cover_wc i M then o85Lambda_wc i else 0 := by
  have h := o85CodeCoverage_wc ⟨step109wc85MatrixCodeNat M, step109wc85_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o85CoverB_wc i (step109wc85MatrixCodeNat M) <;> simp [o85Cover_wc, hb]

theorem o85W_le_source_wc (i : Fin 7) : o85W_wc ≤ o85SourceU_wc i := by
  fin_cases i
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [262, 130, 68, 34, 20, 10, 1]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [262, 130, 68, 34, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 34, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [260, 129, 68, 33, 20, 8, 2]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [260, 129, 68, 33, 20, 8, 2])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 129, 68, 33, 20, 8, 2] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [261, 128, 68, 32, 20, 9, 3]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [261, 128, 68, 32, 20, 9, 3])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [261, 128, 68, 32, 20, 9, 3] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [258, 131, 64, 35, 16, 10, 4]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [258, 131, 64, 35, 16, 10, 4])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 131, 64, 35, 16, 10, 4] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [259, 131, 65, 35, 17, 10, 5]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [259, 131, 65, 35, 17, 10, 5])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [259, 131, 65, 35, 17, 10, 5] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [256, 131, 66, 35, 18, 10, 6]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [256, 131, 66, 35, 18, 10, 6])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 131, 66, 35, 18, 10, 6] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 131, 68, 35, 20, 10] ≤ spanCodes [257, 131, 67, 35, 19, 10, 7]
    apply step109wc85_spanCodes_le_of_gens [262, 131, 68, 35, 20, 10] (spanCodes [257, 131, 67, 35, 19, 10, 7])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [257, 131, 67, 35, 19, 10, 7] n (by fin_cases hn <;> decide)

theorem o85CoverSound_wc (i : Fin 7) (M : Mat3) (h : o85Cover_wc i M) : M ∈ o85SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [262, 130, 68, 34, 20, 10, 1]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 130, 68, 34, 20, 10, 1] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 129, 68, 33, 20, 8, 2]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 129, 68, 33, 20, 8, 2] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [261, 128, 68, 32, 20, 9, 3]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [261, 128, 68, 32, 20, 9, 3] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 131, 64, 35, 16, 10, 4]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 131, 64, 35, 16, 10, 4] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [259, 131, 65, 35, 17, 10, 5]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [259, 131, 65, 35, 17, 10, 5] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 131, 66, 35, 18, 10, 6]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 131, 66, 35, 18, 10, 6] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [257, 131, 67, 35, 19, 10, 7]
    unfold o85Cover_wc o85CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [257, 131, 67, 35, 19, 10, 7] (step109wc85MatrixCodeNat M) h
    rwa [step109wc85_codeMat_matrixCode_all] at hspan

private theorem o85Cert_wc : (7 - 1) * 16 < ∑ i : Fin 7, o85Lambda_wc i * o85SourceLb_wc i := by
  simp only [o85Lambda_wc, o85SourceLb_wc]; decide
private theorem o85LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o85Lambda_wc i := by
  simp only [o85Lambda_wc]; decide

theorem o85Lb17_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o85SourceU_wc i) (o85SourceLb_wc i)) :
    QuotientRankAtLeast o85W_wc 17 :=
  quotientRankAtLeast_of_contradiction o85W_wc 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o85SourceU_wc o85SourceLb_wc
      o85Lambda_wc 1 16
      o85Cover_wc o85W_le_source_wc hSource
      o85LambdaSum_wc o85CoverSound_wc
      (fun M => o85MatCoverage_wc M) (by omega) o85Cert_wc D)

end QiushiMatmul
