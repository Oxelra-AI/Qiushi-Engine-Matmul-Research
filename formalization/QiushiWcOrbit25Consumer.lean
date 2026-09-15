import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 25, exact manifest basis [256, 80, 8, 4, 2, 1]. -/
def o25W_wc : Submodule F2 Mat3 := spanCodes [256, 80, 8, 4, 2, 1]

private theorem step109wc25_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc25MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc25_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc25MatrixCodeNat M) = M := by decide

private theorem step109wc25_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc25_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o25SourceU_wc : Fin 5 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 80, 32, 8, 4, 2, 1]
  | ⟨1, _⟩ => spanCodes [256, 80, 48, 8, 4, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 128, 80, 8, 4, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 144, 80, 8, 4, 2, 1]
  | ⟨4, _⟩ => spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
  | ⟨k + 5, h⟩ => absurd h (by omega)

def o25SourceLb_wc : Fin 5 → ℕ
  | ⟨k, _⟩ => [9, 9, 9, 9, 6].getD k 0

def o25Lambda_wc : Fin 5 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1].getD k 0

def o25CoverB_wc : Fin 5 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 80, 32, 8, 4, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 80, 48, 8, 4, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 128, 80, 8, 4, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 144, 80, 8, 4, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [256, 160, 64, 16, 8, 4, 2, 1] c
  | ⟨k + 5, h⟩, _ => absurd h (by omega)

def o25Cover_wc (i : Fin 5) (M : Mat3) : Prop :=
  o25CoverB_wc i (step109wc25MatrixCodeNat M) = true

theorem o25CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 5, if o25CoverB_wc i c.val = true then o25Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o25MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 5, if o25Cover_wc i M then o25Lambda_wc i else 0 := by
  have h := o25CodeCoverage_wc ⟨step109wc25MatrixCodeNat M, step109wc25_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o25CoverB_wc i (step109wc25MatrixCodeNat M) <;> simp [o25Cover_wc, hb]

theorem o25W_le_source_wc (i : Fin 5) : o25W_wc ≤ o25SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 80, 8, 4, 2, 1] ≤ spanCodes [256, 80, 32, 8, 4, 2, 1]
    apply step109wc25_spanCodes_le_of_gens [256, 80, 8, 4, 2, 1] (spanCodes [256, 80, 32, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 80, 32, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 80, 8, 4, 2, 1] ≤ spanCodes [256, 80, 48, 8, 4, 2, 1]
    apply step109wc25_spanCodes_le_of_gens [256, 80, 8, 4, 2, 1] (spanCodes [256, 80, 48, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 80, 48, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 80, 8, 4, 2, 1] ≤ spanCodes [256, 128, 80, 8, 4, 2, 1]
    apply step109wc25_spanCodes_le_of_gens [256, 80, 8, 4, 2, 1] (spanCodes [256, 128, 80, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 80, 8, 4, 2, 1] ≤ spanCodes [256, 144, 80, 8, 4, 2, 1]
    apply step109wc25_spanCodes_le_of_gens [256, 80, 8, 4, 2, 1] (spanCodes [256, 144, 80, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 80, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 80, 8, 4, 2, 1] ≤ spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
    apply step109wc25_spanCodes_le_of_gens [256, 80, 8, 4, 2, 1] (spanCodes [256, 160, 64, 16, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o25CoverSound_wc (i : Fin 5) (M : Mat3) (h : o25Cover_wc i M) : M ∈ o25SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 80, 32, 8, 4, 2, 1]
    unfold o25Cover_wc o25CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 80, 32, 8, 4, 2, 1] (step109wc25MatrixCodeNat M) h
    rwa [step109wc25_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 80, 48, 8, 4, 2, 1]
    unfold o25Cover_wc o25CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 80, 48, 8, 4, 2, 1] (step109wc25MatrixCodeNat M) h
    rwa [step109wc25_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 80, 8, 4, 2, 1]
    unfold o25Cover_wc o25CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 80, 8, 4, 2, 1] (step109wc25MatrixCodeNat M) h
    rwa [step109wc25_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 80, 8, 4, 2, 1]
    unfold o25Cover_wc o25CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 80, 8, 4, 2, 1] (step109wc25MatrixCodeNat M) h
    rwa [step109wc25_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
    unfold o25Cover_wc o25CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 160, 64, 16, 8, 4, 2, 1] (step109wc25MatrixCodeNat M) h
    rwa [step109wc25_codeMat_matrixCode_all] at hspan

private theorem o25Cert_wc : (5 - 1) * 10 < ∑ i : Fin 5, o25Lambda_wc i * o25SourceLb_wc i := by
  simp only [o25Lambda_wc, o25SourceLb_wc]; decide
private theorem o25LambdaSum_wc : 1 ≤ ∑ i : Fin 5, o25Lambda_wc i := by
  simp only [o25Lambda_wc]; decide

theorem o25Lb11_wc
    (hSource : ∀ i : Fin 5, QuotientRankAtLeast (o25SourceU_wc i) (o25SourceLb_wc i)) :
    QuotientRankAtLeast o25W_wc 11 :=
  quotientRankAtLeast_of_contradiction o25W_wc 11 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o25SourceU_wc o25SourceLb_wc
      o25Lambda_wc 1 10
      o25Cover_wc o25W_le_source_wc hSource
      o25LambdaSum_wc o25CoverSound_wc
      (fun M => o25MatCoverage_wc M) (by omega) o25Cert_wc D)

end QiushiMatmul
