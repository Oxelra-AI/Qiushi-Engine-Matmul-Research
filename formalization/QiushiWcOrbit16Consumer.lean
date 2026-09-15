import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 16, exact manifest basis [256, 148, 80, 32, 12, 2, 1]. -/
def o16W_wc : Submodule F2 Mat3 := spanCodes [256, 148, 80, 32, 12, 2, 1]

private theorem step109wc16_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc16MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc16_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc16MatrixCodeNat M) = M := by decide

private theorem step109wc16_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc16_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o16SourceU_wc : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [256, 132, 64, 32, 16, 12, 2, 1]
  | ⟨1, _⟩ => spanCodes [256, 128, 68, 32, 20, 12, 2, 1]
  | ⟨2, _⟩ => spanCodes [256, 144, 80, 32, 8, 4, 2, 1]
  | ⟨k + 3, h⟩ => absurd h (by omega)

def o16SourceLb_wc : Fin 3 → ℕ
  | ⟨k, _⟩ => [9, 9, 6].getD k 0

def o16Lambda_wc : Fin 3 → ℕ
  | ⟨k, _⟩ => [1, 1, 1].getD k 0

def o16CoverB_wc : Fin 3 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [256, 132, 64, 32, 16, 12, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [256, 128, 68, 32, 20, 12, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [256, 144, 80, 32, 8, 4, 2, 1] c
  | ⟨k + 3, h⟩, _ => absurd h (by omega)

def o16Cover_wc (i : Fin 3) (M : Mat3) : Prop :=
  o16CoverB_wc i (step109wc16MatrixCodeNat M) = true

theorem o16CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 3, if o16CoverB_wc i c.val = true then o16Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o16MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 3, if o16Cover_wc i M then o16Lambda_wc i else 0 := by
  have h := o16CodeCoverage_wc ⟨step109wc16MatrixCodeNat M, step109wc16_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o16CoverB_wc i (step109wc16MatrixCodeNat M) <;> simp [o16Cover_wc, hb]

theorem o16W_le_source_wc (i : Fin 3) : o16W_wc ≤ o16SourceU_wc i := by
  fin_cases i
  · change spanCodes [256, 148, 80, 32, 12, 2, 1] ≤ spanCodes [256, 132, 64, 32, 16, 12, 2, 1]
    apply step109wc16_spanCodes_le_of_gens [256, 148, 80, 32, 12, 2, 1] (spanCodes [256, 132, 64, 32, 16, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 16, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 148, 80, 32, 12, 2, 1] ≤ spanCodes [256, 128, 68, 32, 20, 12, 2, 1]
    apply step109wc16_spanCodes_le_of_gens [256, 148, 80, 32, 12, 2, 1] (spanCodes [256, 128, 68, 32, 20, 12, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 12, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [256, 148, 80, 32, 12, 2, 1] ≤ spanCodes [256, 144, 80, 32, 8, 4, 2, 1]
    apply step109wc16_spanCodes_le_of_gens [256, 148, 80, 32, 12, 2, 1] (spanCodes [256, 144, 80, 32, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 144, 80, 32, 8, 4, 2, 1] n (by fin_cases hn <;> decide)

theorem o16CoverSound_wc (i : Fin 3) (M : Mat3) (h : o16Cover_wc i M) : M ∈ o16SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [256, 132, 64, 32, 16, 12, 2, 1]
    unfold o16Cover_wc o16CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 64, 32, 16, 12, 2, 1] (step109wc16MatrixCodeNat M) h
    rwa [step109wc16_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 68, 32, 20, 12, 2, 1]
    unfold o16Cover_wc o16CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 68, 32, 20, 12, 2, 1] (step109wc16MatrixCodeNat M) h
    rwa [step109wc16_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 144, 80, 32, 8, 4, 2, 1]
    unfold o16Cover_wc o16CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 144, 80, 32, 8, 4, 2, 1] (step109wc16MatrixCodeNat M) h
    rwa [step109wc16_codeMat_matrixCode_all] at hspan

private theorem o16Cert_wc : (3 - 1) * 11 < ∑ i : Fin 3, o16Lambda_wc i * o16SourceLb_wc i := by
  simp only [o16Lambda_wc, o16SourceLb_wc]; decide
private theorem o16LambdaSum_wc : 1 ≤ ∑ i : Fin 3, o16Lambda_wc i := by
  simp only [o16Lambda_wc]; decide

theorem o16Lb12_wc
    (hSource : ∀ i : Fin 3, QuotientRankAtLeast (o16SourceU_wc i) (o16SourceLb_wc i)) :
    QuotientRankAtLeast o16W_wc 12 :=
  quotientRankAtLeast_of_contradiction o16W_wc 12 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o16SourceU_wc o16SourceLb_wc
      o16Lambda_wc 1 11
      o16Cover_wc o16W_le_source_wc hSource
      o16LambdaSum_wc o16CoverSound_wc
      (fun M => o16MatCoverage_wc M) (by omega) o16Cert_wc D)

end QiushiMatmul
