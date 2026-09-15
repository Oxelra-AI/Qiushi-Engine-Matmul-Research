import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 264, exact manifest basis [256, 12, 2, 1]. -/
def o264W_wc : Submodule F2 Mat3 := spanCodes [256, 12, 2, 1]

private theorem step109wc264_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc264MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc264_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc264MatrixCodeNat M) = M := by decide

private theorem step109wc264_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc264_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o264SourceU_wc : Fin 26 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 64, 12, 2, 1]
  | ⟨1, _⟩ => spanCodes [256, 80, 12, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 84, 12, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 112, 12, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 116, 12, 2, 1]
  | ⟨5, _⟩ => spanCodes [256, 128, 12, 2, 1]
  | ⟨6, _⟩ => spanCodes [256, 132, 12, 2, 1]
  | ⟨7, _⟩ => spanCodes [256, 160, 12, 2, 1]
  | ⟨8, _⟩ => spanCodes [256, 164, 12, 2, 1]
  | ⟨9, _⟩ => spanCodes [256, 192, 12, 2, 1]
  | ⟨10, _⟩ => spanCodes [256, 196, 12, 2, 1]
  | ⟨11, _⟩ => spanCodes [256, 224, 12, 2, 1]
  | ⟨12, _⟩ => spanCodes [256, 144, 12, 2, 1]
  | ⟨13, _⟩ => spanCodes [256, 212, 12, 2, 1]
  | ⟨14, _⟩ => spanCodes [256, 148, 96, 12, 2, 1]
  | ⟨15, _⟩ => spanCodes [256, 96, 8, 4, 2, 1]
  | ⟨16, _⟩ => spanCodes [256, 132, 36, 16, 12, 2, 1]
  | ⟨17, _⟩ => spanCodes [256, 132, 32, 16, 12, 2, 1]
  | ⟨18, _⟩ => spanCodes [256, 144, 68, 52, 12, 2, 1]
  | ⟨19, _⟩ => spanCodes [256, 144, 68, 48, 12, 2, 1]
  | ⟨20, _⟩ => spanCodes [256, 148, 68, 32, 12, 2, 1]
  | ⟨21, _⟩ => spanCodes [256, 196, 32, 20, 12, 2, 1]
  | ⟨22, _⟩ => spanCodes [256, 148, 68, 36, 12, 2, 1]
  | ⟨23, _⟩ => spanCodes [256, 196, 36, 20, 12, 2, 1]
  | ⟨24, _⟩ => spanCodes [256, 176, 96, 8, 4, 2, 1]
  | ⟨25, _⟩ => spanCodes [256, 224, 16, 8, 4, 2, 1]
  | ⟨k + 26, h⟩ => absurd h (by omega)

def o264SourceLb_wc : Fin 26 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 12, 12, 12, 12, 12, 12, 12, 12, 12, 9, 9].getD k 0

def o264Lambda_wc : Fin 26 → ℕ
  | ⟨k, _⟩ => [8, 8, 8, 7, 5, 8, 2, 1, 5, 8, 2, 2, 4, 1, 2, 3, 4, 2, 1, 3, 3, 3, 1, 3, 3, 2].getD k 0

def o264CoverB_wc : Fin 26 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 64, 12, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 80, 12, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 84, 12, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 112, 12, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 116, 12, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 128, 12, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 132, 12, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 160, 12, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [256, 164, 12, 2, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [256, 192, 12, 2, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [256, 196, 12, 2, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [256, 224, 12, 2, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [256, 144, 12, 2, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [256, 212, 12, 2, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [256, 148, 96, 12, 2, 1] c
  | ⟨15, _⟩, c => spanContainsCodeCore [256, 96, 8, 4, 2, 1] c
  | ⟨16, _⟩, c => spanContainsCodeCore [256, 132, 36, 16, 12, 2, 1] c
  | ⟨17, _⟩, c => spanContainsCodeCore [256, 132, 32, 16, 12, 2, 1] c
  | ⟨18, _⟩, c => spanContainsCodeCore [256, 144, 68, 52, 12, 2, 1] c
  | ⟨19, _⟩, c => spanContainsCodeCore [256, 144, 68, 48, 12, 2, 1] c
  | ⟨20, _⟩, c => spanContainsCodeCore [256, 148, 68, 32, 12, 2, 1] c
  | ⟨21, _⟩, c => spanContainsCodeCore [256, 196, 32, 20, 12, 2, 1] c
  | ⟨22, _⟩, c => spanContainsCodeCore [256, 148, 68, 36, 12, 2, 1] c
  | ⟨23, _⟩, c => spanContainsCodeCore [256, 196, 36, 20, 12, 2, 1] c
  | ⟨24, _⟩, c => spanContainsCodeCore [256, 176, 96, 8, 4, 2, 1] c
  | ⟨25, _⟩, c => spanContainsCodeCore [256, 224, 16, 8, 4, 2, 1] c
  | ⟨k + 26, h⟩, _ => absurd h (by omega)

def o264Cover_wc (i : Fin 26) (M : Mat3) : Prop :=
  o264CoverB_wc i (step109wc264MatrixCodeNat M) = true

theorem o264CodeCoverage_wc (c : Fin 512) :
    8 ≤ ∑ i : Fin 26, if o264CoverB_wc i c.val = true then o264Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o264MatCoverage_wc (M : Mat3) :
    8 ≤ ∑ i : Fin 26, if o264Cover_wc i M then o264Lambda_wc i else 0 := by
  have h := o264CodeCoverage_wc ⟨step109wc264MatrixCodeNat M, step109wc264_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o264CoverB_wc i (step109wc264MatrixCodeNat M) <;> simp [o264Cover_wc, hb]

theorem o264W_le_source_wc (i : Fin 26) : o264W_wc ≤ o264SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 64, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 64, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 64, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 80, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 80, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 84, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 84, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 84, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 112, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 112, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 112, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 116, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 116, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 116, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 128, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 128, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 132, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 132, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 160, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 160, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 164, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 164, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 164, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 192, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 192, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 192, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 196, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 196, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 196, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 224, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 224, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 224, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 144, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 144, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 212, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 212, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 212, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 148, 96, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 148, 96, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 148, 96, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 96, 8, 4, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 96, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 132, 36, 16, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 132, 36, 16, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 36, 16, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 132, 32, 16, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 132, 32, 16, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 32, 16, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 144, 68, 52, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 144, 68, 52, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 52, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 144, 68, 48, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 144, 68, 48, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 148, 68, 32, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 148, 68, 32, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 148, 68, 32, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 196, 32, 20, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 196, 32, 20, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 196, 32, 20, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 148, 68, 36, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 148, 68, 36, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 148, 68, 36, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 196, 36, 20, 12, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 196, 36, 20, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 196, 36, 20, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 176, 96, 8, 4, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 176, 96, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 176, 96, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 12, 2, 1] ≤ spanCodes [256, 224, 16, 8, 4, 2, 1]
    apply step109wc264_spanCodes_le_of_gens [256, 12, 2, 1] (spanCodes [256, 224, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 224, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o264CoverSound_wc (i : Fin 26) (M : Mat3) (h : o264Cover_wc i M) : M ∈ o264SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 64, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 64, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 80, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 80, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 84, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 84, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 112, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 112, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 116, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 116, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 164, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 164, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 192, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 192, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 196, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 196, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 224, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 224, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 212, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 212, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 148, 96, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 148, 96, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 96, 8, 4, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 96, 8, 4, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 36, 16, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 36, 16, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 32, 16, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 32, 16, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 68, 52, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 52, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 68, 48, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 68, 48, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 148, 68, 32, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 148, 68, 32, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 196, 32, 20, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 196, 32, 20, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 148, 68, 36, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 148, 68, 36, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 196, 36, 20, 12, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 196, 36, 20, 12, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 176, 96, 8, 4, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 176, 96, 8, 4, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 224, 16, 8, 4, 2, 1]
    unfold o264Cover_wc o264CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 224, 16, 8, 4, 2, 1] (step109wc264MatrixCodeNat M) h
    rwa [step109wc264_codeMat_matrixCode_all] at hspan

private theorem o264Cert_wc : (99 - 8) * 15 < ∑ i : Fin 26, o264Lambda_wc i * o264SourceLb_wc i := by
  simp only [o264Lambda_wc, o264SourceLb_wc]; decide
private theorem o264LambdaSum_wc : 8 ≤ ∑ i : Fin 26, o264Lambda_wc i := by
  simp only [o264Lambda_wc]; decide

theorem o264Lb16_wc
    (hSource : ∀ i : Fin 26, QuotientRankAtLeast (o264SourceU_wc i) (o264SourceLb_wc i)) :
    QuotientRankAtLeast o264W_wc 16 :=
  quotientRankAtLeast_of_contradiction o264W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o264SourceU_wc o264SourceLb_wc
      o264Lambda_wc 8 15
      o264Cover_wc o264W_le_source_wc hSource
      o264LambdaSum_wc o264CoverSound_wc
      (fun M => o264MatCoverage_wc M) (by omega) o264Cert_wc D)

end QiushiMatmul
