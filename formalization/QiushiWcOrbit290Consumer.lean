import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 290, exact manifest basis [68, 32, 10, 1]. -/
def o290W_wc : Submodule F2 Mat3 := spanCodes [68, 32, 10, 1]

private theorem step109wc290_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc290MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc290_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc290MatrixCodeNat M) = M := by decide

private theorem step109wc290_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc290_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o290SourceU_wc : Fin 20 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [68, 32, 20, 10, 1]
  | ⟨1, _⟩ => spanCodes [68, 32, 22, 10, 1]
  | ⟨2, _⟩ => spanCodes [258, 68, 32, 10, 1]
  | ⟨3, _⟩ => spanCodes [262, 68, 32, 10, 1]
  | ⟨4, _⟩ => spanCodes [68, 32, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [64, 32, 10, 4, 1]
  | ⟨6, _⟩ => spanCodes [272, 146, 68, 32, 10, 1]
  | ⟨7, _⟩ => spanCodes [274, 150, 68, 32, 10, 1]
  | ⟨8, _⟩ => spanCodes [278, 144, 68, 32, 10, 1]
  | ⟨9, _⟩ => spanCodes [272, 128, 68, 32, 10, 1]
  | ⟨10, _⟩ => spanCodes [278, 134, 68, 32, 10, 1]
  | ⟨11, _⟩ => spanCodes [274, 132, 68, 32, 10, 1]
  | ⟨12, _⟩ => spanCodes [276, 130, 68, 32, 10, 1]
  | ⟨13, _⟩ => spanCodes [256, 128, 68, 32, 16, 10, 1]
  | ⟨14, _⟩ => spanCodes [260, 134, 68, 32, 18, 10, 1]
  | ⟨15, _⟩ => spanCodes [260, 130, 68, 32, 16, 10, 1]
  | ⟨16, _⟩ => spanCodes [258, 128, 66, 32, 16, 10, 6, 1]
  | ⟨17, _⟩ => spanCodes [256, 130, 66, 32, 16, 10, 6, 1]
  | ⟨18, _⟩ => spanCodes [256, 128, 66, 32, 18, 10, 6, 1]
  | ⟨19, _⟩ => spanCodes [258, 130, 66, 32, 18, 10, 6, 1]
  | ⟨k + 20, h⟩ => absurd h (by omega)

def o290SourceLb_wc : Fin 20 → ℕ
  | ⟨k, _⟩ => [16, 16, 16, 16, 15, 15, 15, 15, 15, 15, 15, 15, 15, 12, 12, 12, 9, 9, 9, 9].getD k 0

def o290Lambda_wc : Fin 20 → ℕ
  | ⟨k, _⟩ => [8, 12, 12, 8, 20, 20, 4, 12, 4, 2, 2, 10, 6, 8, 8, 4, 3, 5, 7, 5].getD k 0

def o290CoverB_wc : Fin 20 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [68, 32, 20, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [68, 32, 22, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [258, 68, 32, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [262, 68, 32, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [68, 32, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [64, 32, 10, 4, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [272, 146, 68, 32, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [274, 150, 68, 32, 10, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [278, 144, 68, 32, 10, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [272, 128, 68, 32, 10, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [278, 134, 68, 32, 10, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [274, 132, 68, 32, 10, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [276, 130, 68, 32, 10, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [256, 128, 68, 32, 16, 10, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [260, 134, 68, 32, 18, 10, 1] c
  | ⟨15, _⟩, c => spanContainsCodeCore [260, 130, 68, 32, 16, 10, 1] c
  | ⟨16, _⟩, c => spanContainsCodeCore [258, 128, 66, 32, 16, 10, 6, 1] c
  | ⟨17, _⟩, c => spanContainsCodeCore [256, 130, 66, 32, 16, 10, 6, 1] c
  | ⟨18, _⟩, c => spanContainsCodeCore [256, 128, 66, 32, 18, 10, 6, 1] c
  | ⟨19, _⟩, c => spanContainsCodeCore [258, 130, 66, 32, 18, 10, 6, 1] c
  | ⟨k + 20, h⟩, _ => absurd h (by omega)

def o290Cover_wc (i : Fin 20) (M : Mat3) : Prop :=
  o290CoverB_wc i (step109wc290MatrixCodeNat M) = true

theorem o290CodeCoverage_wc (c : Fin 512) :
    20 ≤ ∑ i : Fin 20, if o290CoverB_wc i c.val = true then o290Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o290MatCoverage_wc (M : Mat3) :
    20 ≤ ∑ i : Fin 20, if o290Cover_wc i M then o290Lambda_wc i else 0 := by
  have h := o290CodeCoverage_wc ⟨step109wc290MatrixCodeNat M, step109wc290_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o290CoverB_wc i (step109wc290MatrixCodeNat M) <;> simp [o290Cover_wc, hb]

theorem o290W_le_source_wc (i : Fin 20) : o290W_wc ≤ o290SourceU_wc i := by
  fin_cases i
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [68, 32, 20, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [68, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [68, 32, 22, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [68, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [68, 32, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [258, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [258, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [262, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [262, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [68, 32, 8, 2, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [68, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [68, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [64, 32, 10, 4, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [64, 32, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [64, 32, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [272, 146, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [272, 146, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 146, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [274, 150, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [274, 150, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 150, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [278, 144, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [278, 144, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 144, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [272, 128, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [272, 128, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [278, 134, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [278, 134, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 134, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [274, 132, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [274, 132, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 132, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [276, 130, 68, 32, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [276, 130, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 130, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [256, 128, 68, 32, 16, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [256, 128, 68, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [260, 134, 68, 32, 18, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [260, 134, 68, 32, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 134, 68, 32, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [260, 130, 68, 32, 16, 10, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [260, 130, 68, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 130, 68, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [258, 128, 66, 32, 16, 10, 6, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [258, 128, 66, 32, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [256, 130, 66, 32, 16, 10, 6, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [256, 130, 66, 32, 16, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 32, 16, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [256, 128, 66, 32, 18, 10, 6, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [256, 128, 66, 32, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 32, 18, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [68, 32, 10, 1] ≤ spanCodes [258, 130, 66, 32, 18, 10, 6, 1]
    apply step109wc290_spanCodes_le_of_gens [68, 32, 10, 1] (spanCodes [258, 130, 66, 32, 18, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 66, 32, 18, 10, 6, 1] n (by fin_cases hn <;> decide)

theorem o290CoverSound_wc (i : Fin 20) (M : Mat3) (h : o290Cover_wc i M) : M ∈ o290SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [68, 32, 20, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 32, 20, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [68, 32, 22, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 32, 22, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [68, 32, 8, 2, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [68, 32, 8, 2, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [64, 32, 10, 4, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [64, 32, 10, 4, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 146, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 146, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 150, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 150, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [278, 144, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 144, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 128, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 128, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [278, 134, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 134, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 132, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 132, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 130, 68, 32, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 130, 68, 32, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 68, 32, 16, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 16, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 134, 68, 32, 18, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 134, 68, 32, 18, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 130, 68, 32, 16, 10, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 130, 68, 32, 16, 10, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 66, 32, 16, 10, 6, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 6, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 130, 66, 32, 16, 10, 6, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 130, 66, 32, 16, 10, 6, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 66, 32, 18, 10, 6, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 66, 32, 18, 10, 6, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 130, 66, 32, 18, 10, 6, 1]
    unfold o290Cover_wc o290CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 66, 32, 18, 10, 6, 1] (step109wc290MatrixCodeNat M) h
    rwa [step109wc290_codeMat_matrixCode_all] at hspan

private theorem o290Cert_wc : (160 - 20) * 16 < ∑ i : Fin 20, o290Lambda_wc i * o290SourceLb_wc i := by
  simp only [o290Lambda_wc, o290SourceLb_wc]; decide
private theorem o290LambdaSum_wc : 20 ≤ ∑ i : Fin 20, o290Lambda_wc i := by
  simp only [o290Lambda_wc]; decide

theorem o290Lb17_wc
    (hSource : ∀ i : Fin 20, QuotientRankAtLeast (o290SourceU_wc i) (o290SourceLb_wc i)) :
    QuotientRankAtLeast o290W_wc 17 :=
  quotientRankAtLeast_of_contradiction o290W_wc 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o290SourceU_wc o290SourceLb_wc
      o290Lambda_wc 20 16
      o290Cover_wc o290W_le_source_wc hSource
      o290LambdaSum_wc o290CoverSound_wc
      (fun M => o290MatCoverage_wc M) (by omega) o290Cert_wc D)

end QiushiMatmul
