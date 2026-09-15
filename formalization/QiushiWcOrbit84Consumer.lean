import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 84, exact manifest basis [258, 128, 84, 32, 10, 1]. -/
def o84W_wc : Submodule F2 Mat3 := spanCodes [258, 128, 84, 32, 10, 1]

private theorem step109wc84_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc84MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc84_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc84MatrixCodeNat M) = M := by decide

private theorem step109wc84_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc84_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o84SourceU_wc : Fin 7 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [258, 128, 80, 32, 10, 4, 1]
  | ⟨1, _⟩ => spanCodes [258, 128, 82, 32, 10, 6, 1]
  | ⟨2, _⟩ => spanCodes [258, 128, 68, 32, 16, 10, 1]
  | ⟨3, _⟩ => spanCodes [258, 128, 70, 32, 18, 10, 1]
  | ⟨4, _⟩ => spanCodes [258, 128, 64, 32, 20, 10, 1]
  | ⟨5, _⟩ => spanCodes [258, 128, 66, 32, 22, 10, 1]
  | ⟨6, _⟩ => spanCodes [256, 128, 84, 32, 8, 2, 1]
  | ⟨k + 7, h⟩ => absurd h (by omega)

def o84SourceLb_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [12, 12, 12, 12, 12, 12, 9].getD k 0

def o84Lambda_wc : Fin 7 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1].getD k 0

def o84CoverB_wc : Fin 7 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [258, 128, 80, 32, 10, 4, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [258, 128, 82, 32, 10, 6, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [258, 128, 68, 32, 16, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [258, 128, 70, 32, 18, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [258, 128, 64, 32, 20, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [258, 128, 66, 32, 22, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [256, 128, 84, 32, 8, 2, 1] c
  | ⟨k + 7, h⟩, _ => absurd h (by omega)

def o84Cover_wc (i : Fin 7) (M : Mat3) : Prop :=
  o84CoverB_wc i (step109wc84MatrixCodeNat M) = true

theorem o84CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 7, if o84CoverB_wc i c.val = true then o84Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o84MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 7, if o84Cover_wc i M then o84Lambda_wc i else 0 := by
  have h := o84CodeCoverage_wc ⟨step109wc84MatrixCodeNat M, step109wc84_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o84CoverB_wc i (step109wc84MatrixCodeNat M) <;> simp [o84Cover_wc, hb]

theorem o84W_le_source_wc (i : Fin 7) : o84W_wc ≤ o84SourceU_wc i := by
  fin_cases i
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 80, 32, 10, 4, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [258, 128, 80, 32, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 80, 32, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 82, 32, 10, 6, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [258, 128, 82, 32, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 82, 32, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 68, 32, 16, 10, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [258, 128, 68, 32, 16, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 68, 32, 16, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 70, 32, 18, 10, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [258, 128, 70, 32, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 70, 32, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 64, 32, 20, 10, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [258, 128, 64, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [258, 128, 66, 32, 22, 10, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [258, 128, 66, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [258, 128, 84, 32, 10, 1] ≤ spanCodes [256, 128, 84, 32, 8, 2, 1]
    apply step109wc84_spanCodes_le_of_gens [258, 128, 84, 32, 10, 1] (spanCodes [256, 128, 84, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o84CoverSound_wc (i : Fin 7) (M : Mat3) (h : o84Cover_wc i M) : M ∈ o84SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [258, 128, 80, 32, 10, 4, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 80, 32, 10, 4, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 82, 32, 10, 6, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 82, 32, 10, 6, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 68, 32, 16, 10, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 68, 32, 16, 10, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 70, 32, 18, 10, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 70, 32, 18, 10, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 64, 32, 20, 10, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 64, 32, 20, 10, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 66, 32, 22, 10, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 22, 10, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 84, 32, 8, 2, 1]
    unfold o84Cover_wc o84CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 84, 32, 8, 2, 1] (step109wc84MatrixCodeNat M) h
    rwa [step109wc84_codeMat_matrixCode_all] at hspan

private theorem o84Cert_wc : (7 - 1) * 13 < ∑ i : Fin 7, o84Lambda_wc i * o84SourceLb_wc i := by
  simp only [o84Lambda_wc, o84SourceLb_wc]; decide
private theorem o84LambdaSum_wc : 1 ≤ ∑ i : Fin 7, o84Lambda_wc i := by
  simp only [o84Lambda_wc]; decide

theorem o84Lb14_wc
    (hSource : ∀ i : Fin 7, QuotientRankAtLeast (o84SourceU_wc i) (o84SourceLb_wc i)) :
    QuotientRankAtLeast o84W_wc 14 :=
  quotientRankAtLeast_of_contradiction o84W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o84SourceU_wc o84SourceLb_wc
      o84Lambda_wc 1 13
      o84Cover_wc o84W_le_source_wc hSource
      o84LambdaSum_wc o84CoverSound_wc
      (fun M => o84MatCoverage_wc M) (by omega) o84Cert_wc D)

end QiushiMatmul
