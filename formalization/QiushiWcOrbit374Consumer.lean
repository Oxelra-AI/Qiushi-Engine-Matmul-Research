import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 374, exact manifest basis [282, 160, 84, 1]. -/
def o374W_wc : Submodule F2 Mat3 := spanCodes [282, 160, 84, 1]

private theorem step109wc374_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc374MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc374_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc374MatrixCodeNat M) = M := by decide

private theorem step109wc374_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc374_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o374SourceU_wc : Fin 20 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [278, 160, 84, 12, 1]
  | ⟨1, _⟩ => spanCodes [276, 160, 84, 14, 1]
  | ⟨2, _⟩ => spanCodes [264, 160, 70, 18, 1]
  | ⟨3, _⟩ => spanCodes [268, 160, 66, 22, 1]
  | ⟨4, _⟩ => spanCodes [258, 160, 76, 24, 1]
  | ⟨5, _⟩ => spanCodes [260, 160, 74, 30, 1]
  | ⟨6, _⟩ => spanCodes [282, 132, 84, 36, 1]
  | ⟨7, _⟩ => spanCodes [282, 134, 84, 38, 1]
  | ⟨8, _⟩ => spanCodes [282, 138, 84, 42, 1]
  | ⟨9, _⟩ => spanCodes [282, 146, 84, 50, 1]
  | ⟨10, _⟩ => spanCodes [282, 148, 84, 52, 1]
  | ⟨11, _⟩ => spanCodes [282, 152, 84, 56, 1]
  | ⟨12, _⟩ => spanCodes [282, 156, 84, 60, 1]
  | ⟨13, _⟩ => spanCodes [256, 160, 68, 16, 10, 1]
  | ⟨14, _⟩ => spanCodes [274, 128, 80, 32, 8, 4, 1]
  | ⟨15, _⟩ => spanCodes [260, 140, 72, 44, 28, 2, 1]
  | ⟨16, _⟩ => spanCodes [268, 128, 64, 32, 20, 2, 1]
  | ⟨17, _⟩ => spanCodes [264, 136, 64, 40, 18, 6, 1]
  | ⟨18, _⟩ => spanCodes [274, 144, 82, 48, 8, 6, 1]
  | ⟨19, _⟩ => spanCodes [258, 130, 72, 34, 24, 4, 1]
  | ⟨k + 20, h⟩ => absurd h (by omega)

def o374SourceLb_wc : Fin 20 → ℕ
  | ⟨k, _⟩ => [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 14, 12, 12, 12, 12, 12, 12].getD k 0

def o374Lambda_wc : Fin 20 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1].getD k 0

def o374CoverB_wc : Fin 20 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [278, 160, 84, 12, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [276, 160, 84, 14, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [264, 160, 70, 18, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [268, 160, 66, 22, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [258, 160, 76, 24, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [260, 160, 74, 30, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [282, 132, 84, 36, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [282, 134, 84, 38, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [282, 138, 84, 42, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [282, 146, 84, 50, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [282, 148, 84, 52, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [282, 152, 84, 56, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [282, 156, 84, 60, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [256, 160, 68, 16, 10, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [274, 128, 80, 32, 8, 4, 1] c
  | ⟨15, _⟩, c => spanContainsCodeCore [260, 140, 72, 44, 28, 2, 1] c
  | ⟨16, _⟩, c => spanContainsCodeCore [268, 128, 64, 32, 20, 2, 1] c
  | ⟨17, _⟩, c => spanContainsCodeCore [264, 136, 64, 40, 18, 6, 1] c
  | ⟨18, _⟩, c => spanContainsCodeCore [274, 144, 82, 48, 8, 6, 1] c
  | ⟨19, _⟩, c => spanContainsCodeCore [258, 130, 72, 34, 24, 4, 1] c
  | ⟨k + 20, h⟩, _ => absurd h (by omega)

def o374Cover_wc (i : Fin 20) (M : Mat3) : Prop :=
  o374CoverB_wc i (step109wc374MatrixCodeNat M) = true

theorem o374CodeCoverage_wc (c : Fin 512) :
    2 ≤ ∑ i : Fin 20, if o374CoverB_wc i c.val = true then o374Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o374MatCoverage_wc (M : Mat3) :
    2 ≤ ∑ i : Fin 20, if o374Cover_wc i M then o374Lambda_wc i else 0 := by
  have h := o374CodeCoverage_wc ⟨step109wc374MatrixCodeNat M, step109wc374_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o374CoverB_wc i (step109wc374MatrixCodeNat M) <;> simp [o374Cover_wc, hb]

theorem o374W_le_source_wc (i : Fin 20) : o374W_wc ≤ o374SourceU_wc i := by
  fin_cases i
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [278, 160, 84, 12, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [278, 160, 84, 12, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [278, 160, 84, 12, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [276, 160, 84, 14, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [276, 160, 84, 14, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 160, 84, 14, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [264, 160, 70, 18, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [264, 160, 70, 18, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 160, 70, 18, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [268, 160, 66, 22, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [268, 160, 66, 22, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [268, 160, 66, 22, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [258, 160, 76, 24, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [258, 160, 76, 24, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 160, 76, 24, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [260, 160, 74, 30, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [260, 160, 74, 30, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 160, 74, 30, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 132, 84, 36, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 132, 84, 36, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 132, 84, 36, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 134, 84, 38, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 134, 84, 38, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 134, 84, 38, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 138, 84, 42, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 138, 84, 42, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 138, 84, 42, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 146, 84, 50, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 146, 84, 50, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 146, 84, 50, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 148, 84, 52, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 148, 84, 52, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 148, 84, 52, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 152, 84, 56, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 152, 84, 56, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 152, 84, 56, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [282, 156, 84, 60, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [282, 156, 84, 60, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [282, 156, 84, 60, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [256, 160, 68, 16, 10, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [256, 160, 68, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [274, 128, 80, 32, 8, 4, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [274, 128, 80, 32, 8, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 128, 80, 32, 8, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [260, 140, 72, 44, 28, 2, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [260, 140, 72, 44, 28, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 140, 72, 44, 28, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [268, 128, 64, 32, 20, 2, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [268, 128, 64, 32, 20, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [268, 128, 64, 32, 20, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [264, 136, 64, 40, 18, 6, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [264, 136, 64, 40, 18, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 136, 64, 40, 18, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [274, 144, 82, 48, 8, 6, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [274, 144, 82, 48, 8, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [274, 144, 82, 48, 8, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [282, 160, 84, 1] ≤ spanCodes [258, 130, 72, 34, 24, 4, 1]
    apply step109wc374_spanCodes_le_of_gens [282, 160, 84, 1] (spanCodes [258, 130, 72, 34, 24, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 130, 72, 34, 24, 4, 1] n (by fin_cases hn <;> decide)

theorem o374CoverSound_wc (i : Fin 20) (M : Mat3) (h : o374Cover_wc i M) : M ∈ o374SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [278, 160, 84, 12, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [278, 160, 84, 12, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 160, 84, 14, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 160, 84, 14, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 160, 70, 18, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 160, 70, 18, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [268, 160, 66, 22, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [268, 160, 66, 22, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 160, 76, 24, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 160, 76, 24, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 160, 74, 30, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 160, 74, 30, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 132, 84, 36, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 132, 84, 36, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 134, 84, 38, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 134, 84, 38, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 138, 84, 42, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 138, 84, 42, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 146, 84, 50, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 146, 84, 50, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 148, 84, 52, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 148, 84, 52, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 152, 84, 56, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 152, 84, 56, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [282, 156, 84, 60, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [282, 156, 84, 60, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 68, 16, 10, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 68, 16, 10, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 128, 80, 32, 8, 4, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 128, 80, 32, 8, 4, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 140, 72, 44, 28, 2, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 140, 72, 44, 28, 2, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [268, 128, 64, 32, 20, 2, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [268, 128, 64, 32, 20, 2, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 136, 64, 40, 18, 6, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 136, 64, 40, 18, 6, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [274, 144, 82, 48, 8, 6, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [274, 144, 82, 48, 8, 6, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 130, 72, 34, 24, 4, 1]
    unfold o374Cover_wc o374CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 130, 72, 34, 24, 4, 1] (step109wc374MatrixCodeNat M) h
    rwa [step109wc374_codeMat_matrixCode_all] at hspan

private theorem o374Cert_wc : (22 - 2) * 16 < ∑ i : Fin 20, o374Lambda_wc i * o374SourceLb_wc i := by
  simp only [o374Lambda_wc, o374SourceLb_wc]; decide
private theorem o374LambdaSum_wc : 2 ≤ ∑ i : Fin 20, o374Lambda_wc i := by
  simp only [o374Lambda_wc]; decide

theorem o374Lb17_wc
    (hSource : ∀ i : Fin 20, QuotientRankAtLeast (o374SourceU_wc i) (o374SourceLb_wc i)) :
    QuotientRankAtLeast o374W_wc 17 :=
  quotientRankAtLeast_of_contradiction o374W_wc 17 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o374SourceU_wc o374SourceLb_wc
      o374Lambda_wc 2 16
      o374Cover_wc o374W_le_source_wc hSource
      o374LambdaSum_wc o374CoverSound_wc
      (fun M => o374MatCoverage_wc M) (by omega) o374Cert_wc D)

end QiushiMatmul
