import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 334, exact manifest basis [140, 98, 16, 1]. -/
def o334W_wc : Submodule F2 Mat3 := spanCodes [140, 98, 16, 1]

private theorem step109wc334_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc334MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc334_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc334MatrixCodeNat M) = M := by decide

private theorem step109wc334_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc334_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o334SourceU_wc : Fin 31 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [140, 96, 16, 2, 1]
  | ⟨1, _⟩ => spanCodes [136, 98, 16, 4, 1]
  | ⟨2, _⟩ => spanCodes [138, 98, 16, 6, 1]
  | ⟨3, _⟩ => spanCodes [132, 98, 16, 8, 1]
  | ⟨4, _⟩ => spanCodes [134, 98, 16, 10, 1]
  | ⟨5, _⟩ => spanCodes [128, 98, 16, 12, 1]
  | ⟨6, _⟩ => spanCodes [130, 98, 16, 14, 1]
  | ⟨7, _⟩ => spanCodes [140, 66, 32, 16, 1]
  | ⟨8, _⟩ => spanCodes [140, 64, 34, 16, 1]
  | ⟨9, _⟩ => spanCodes [140, 74, 40, 16, 1]
  | ⟨10, _⟩ => spanCodes [140, 72, 42, 16, 1]
  | ⟨11, _⟩ => spanCodes [256, 140, 98, 16, 1]
  | ⟨12, _⟩ => spanCodes [258, 140, 98, 16, 1]
  | ⟨13, _⟩ => spanCodes [260, 140, 98, 16, 1]
  | ⟨14, _⟩ => spanCodes [262, 140, 98, 16, 1]
  | ⟨15, _⟩ => spanCodes [264, 140, 98, 16, 1]
  | ⟨16, _⟩ => spanCodes [266, 140, 98, 16, 1]
  | ⟨17, _⟩ => spanCodes [268, 140, 98, 16, 1]
  | ⟨18, _⟩ => spanCodes [270, 140, 98, 16, 1]
  | ⟨19, _⟩ => spanCodes [288, 140, 98, 16, 1]
  | ⟨20, _⟩ => spanCodes [290, 140, 98, 16, 1]
  | ⟨21, _⟩ => spanCodes [292, 140, 98, 16, 1]
  | ⟨22, _⟩ => spanCodes [294, 140, 98, 16, 1]
  | ⟨23, _⟩ => spanCodes [296, 140, 98, 16, 1]
  | ⟨24, _⟩ => spanCodes [298, 140, 98, 16, 1]
  | ⟨25, _⟩ => spanCodes [300, 140, 98, 16, 1]
  | ⟨26, _⟩ => spanCodes [302, 140, 98, 16, 1]
  | ⟨27, _⟩ => spanCodes [140, 70, 36, 16, 1]
  | ⟨28, _⟩ => spanCodes [140, 68, 38, 16, 1]
  | ⟨29, _⟩ => spanCodes [140, 78, 44, 16, 1]
  | ⟨30, _⟩ => spanCodes [140, 76, 46, 16, 1]
  | ⟨k + 31, h⟩ => absurd h (by omega)

def o334SourceLb_wc : Fin 31 → ℕ
  | ⟨k, _⟩ => [15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14].getD k 0

def o334Lambda_wc : Fin 31 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o334CoverB_wc : Fin 31 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [140, 96, 16, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [136, 98, 16, 4, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [138, 98, 16, 6, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [132, 98, 16, 8, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [134, 98, 16, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [128, 98, 16, 12, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [130, 98, 16, 14, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [140, 66, 32, 16, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [140, 64, 34, 16, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [140, 74, 40, 16, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [140, 72, 42, 16, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [256, 140, 98, 16, 1] c
  | ⟨12, _⟩, c => spanContainsCodeCore [258, 140, 98, 16, 1] c
  | ⟨13, _⟩, c => spanContainsCodeCore [260, 140, 98, 16, 1] c
  | ⟨14, _⟩, c => spanContainsCodeCore [262, 140, 98, 16, 1] c
  | ⟨15, _⟩, c => spanContainsCodeCore [264, 140, 98, 16, 1] c
  | ⟨16, _⟩, c => spanContainsCodeCore [266, 140, 98, 16, 1] c
  | ⟨17, _⟩, c => spanContainsCodeCore [268, 140, 98, 16, 1] c
  | ⟨18, _⟩, c => spanContainsCodeCore [270, 140, 98, 16, 1] c
  | ⟨19, _⟩, c => spanContainsCodeCore [288, 140, 98, 16, 1] c
  | ⟨20, _⟩, c => spanContainsCodeCore [290, 140, 98, 16, 1] c
  | ⟨21, _⟩, c => spanContainsCodeCore [292, 140, 98, 16, 1] c
  | ⟨22, _⟩, c => spanContainsCodeCore [294, 140, 98, 16, 1] c
  | ⟨23, _⟩, c => spanContainsCodeCore [296, 140, 98, 16, 1] c
  | ⟨24, _⟩, c => spanContainsCodeCore [298, 140, 98, 16, 1] c
  | ⟨25, _⟩, c => spanContainsCodeCore [300, 140, 98, 16, 1] c
  | ⟨26, _⟩, c => spanContainsCodeCore [302, 140, 98, 16, 1] c
  | ⟨27, _⟩, c => spanContainsCodeCore [140, 70, 36, 16, 1] c
  | ⟨28, _⟩, c => spanContainsCodeCore [140, 68, 38, 16, 1] c
  | ⟨29, _⟩, c => spanContainsCodeCore [140, 78, 44, 16, 1] c
  | ⟨30, _⟩, c => spanContainsCodeCore [140, 76, 46, 16, 1] c
  | ⟨k + 31, h⟩, _ => absurd h (by omega)

def o334Cover_wc (i : Fin 31) (M : Mat3) : Prop :=
  o334CoverB_wc i (step109wc334MatrixCodeNat M) = true

theorem o334CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 31, if o334CoverB_wc i c.val = true then o334Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o334MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 31, if o334Cover_wc i M then o334Lambda_wc i else 0 := by
  have h := o334CodeCoverage_wc ⟨step109wc334MatrixCodeNat M, step109wc334_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o334CoverB_wc i (step109wc334MatrixCodeNat M) <;> simp [o334Cover_wc, hb]

theorem o334W_le_source_wc (i : Fin 31) : o334W_wc ≤ o334SourceU_wc i := by
  fin_cases i
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 96, 16, 2, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 96, 16, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 96, 16, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [136, 98, 16, 4, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [136, 98, 16, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [136, 98, 16, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [138, 98, 16, 6, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [138, 98, 16, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [138, 98, 16, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [132, 98, 16, 8, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [132, 98, 16, 8, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [132, 98, 16, 8, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [134, 98, 16, 10, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [134, 98, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [134, 98, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [128, 98, 16, 12, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [128, 98, 16, 12, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [128, 98, 16, 12, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [130, 98, 16, 14, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [130, 98, 16, 14, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [130, 98, 16, 14, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 66, 32, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 66, 32, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 66, 32, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 64, 34, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 64, 34, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 64, 34, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 74, 40, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 74, 40, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 74, 40, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 72, 42, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 72, 42, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 72, 42, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [256, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [256, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [258, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [258, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [260, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [260, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [262, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [262, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [264, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [264, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [264, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [266, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [266, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [266, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [268, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [268, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [268, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [270, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [270, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [270, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [288, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [288, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [290, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [290, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [290, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [292, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [292, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [292, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [294, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [294, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [294, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [296, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [296, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [296, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [298, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [298, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [298, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [300, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [300, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [300, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [302, 140, 98, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [302, 140, 98, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [302, 140, 98, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 70, 36, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 70, 36, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 70, 36, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 68, 38, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 68, 38, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 68, 38, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 78, 44, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 78, 44, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 78, 44, 16, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [140, 98, 16, 1] ≤ spanCodes [140, 76, 46, 16, 1]
    apply step109wc334_spanCodes_le_of_gens [140, 98, 16, 1] (spanCodes [140, 76, 46, 16, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [140, 76, 46, 16, 1] n (by fin_cases hn <;> decide)

theorem o334CoverSound_wc (i : Fin 31) (M : Mat3) (h : o334Cover_wc i M) : M ∈ o334SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [140, 96, 16, 2, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 96, 16, 2, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [136, 98, 16, 4, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [136, 98, 16, 4, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [138, 98, 16, 6, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [138, 98, 16, 6, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [132, 98, 16, 8, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [132, 98, 16, 8, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [134, 98, 16, 10, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [134, 98, 16, 10, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [128, 98, 16, 12, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [128, 98, 16, 12, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [130, 98, 16, 14, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [130, 98, 16, 14, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 66, 32, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 66, 32, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 64, 34, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 64, 34, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 74, 40, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 74, 40, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 72, 42, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 72, 42, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [264, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [264, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [266, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [266, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [268, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [268, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [270, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [270, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [290, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [290, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [292, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [292, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [294, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [294, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [296, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [296, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [298, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [298, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [300, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [300, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [302, 140, 98, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [302, 140, 98, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 70, 36, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 70, 36, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 68, 38, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 68, 38, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 78, 44, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 78, 44, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [140, 76, 46, 16, 1]
    unfold o334Cover_wc o334CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [140, 76, 46, 16, 1] (step109wc334MatrixCodeNat M) h
    rwa [step109wc334_codeMat_matrixCode_all] at hspan

private theorem o334Cert_wc : (31 - 1) * 15 < ∑ i : Fin 31, o334Lambda_wc i * o334SourceLb_wc i := by
  simp only [o334Lambda_wc, o334SourceLb_wc]; decide
private theorem o334LambdaSum_wc : 1 ≤ ∑ i : Fin 31, o334Lambda_wc i := by
  simp only [o334Lambda_wc]; decide

theorem o334Lb16_wc
    (hSource : ∀ i : Fin 31, QuotientRankAtLeast (o334SourceU_wc i) (o334SourceLb_wc i)) :
    QuotientRankAtLeast o334W_wc 16 :=
  quotientRankAtLeast_of_contradiction o334W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o334SourceU_wc o334SourceLb_wc
      o334Lambda_wc 1 15
      o334Cover_wc o334W_le_source_wc hSource
      o334LambdaSum_wc o334CoverSound_wc
      (fun M => o334MatCoverage_wc M) (by omega) o334Cert_wc D)

end QiushiMatmul
