import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 187, exact manifest basis [262, 128, 32, 10, 1]. -/
def o187W_wc : Submodule F2 Mat3 := spanCodes [262, 128, 32, 10, 1]

private theorem step109wc187_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc187MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc187_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc187MatrixCodeNat M) = M := by decide

private theorem step109wc187_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc187_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o187SourceU_wc : Fin 9 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [258, 128, 32, 10, 4, 1]
  | ⟨1, _⟩ => spanCodes [262, 128, 32, 20, 10, 1]
  | ⟨2, _⟩ => spanCodes [262, 128, 32, 22, 10, 1]
  | ⟨3, _⟩ => spanCodes [262, 128, 68, 32, 10, 1]
  | ⟨4, _⟩ => spanCodes [262, 128, 70, 32, 10, 1]
  | ⟨5, _⟩ => spanCodes [262, 128, 84, 32, 10, 1]
  | ⟨6, _⟩ => spanCodes [262, 128, 86, 32, 10, 1]
  | ⟨7, _⟩ => spanCodes [256, 128, 32, 10, 6, 1]
  | ⟨8, _⟩ => spanCodes [260, 128, 64, 32, 16, 8, 2, 1]
  | ⟨k + 9, h⟩ => absurd h (by omega)

def o187SourceLb_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [14, 14, 14, 14, 14, 14, 14, 12, 3].getD k 0

def o187Lambda_wc : Fin 9 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o187CoverB_wc : Fin 9 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [258, 128, 32, 10, 4, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [262, 128, 32, 20, 10, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [262, 128, 32, 22, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [262, 128, 68, 32, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [262, 128, 70, 32, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [262, 128, 84, 32, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [262, 128, 86, 32, 10, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [256, 128, 32, 10, 6, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [260, 128, 64, 32, 16, 8, 2, 1] c
  | ⟨k + 9, h⟩, _ => absurd h (by omega)

def o187Cover_wc (i : Fin 9) (M : Mat3) : Prop :=
  o187CoverB_wc i (step109wc187MatrixCodeNat M) = true

theorem o187CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 9, if o187CoverB_wc i c.val = true then o187Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o187MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 9, if o187Cover_wc i M then o187Lambda_wc i else 0 := by
  have h := o187CodeCoverage_wc ⟨step109wc187MatrixCodeNat M, step109wc187_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o187CoverB_wc i (step109wc187MatrixCodeNat M) <;> simp [o187Cover_wc, hb]

theorem o187W_le_source_wc (i : Fin 9) : o187W_wc ≤ o187SourceU_wc i := by
  fin_cases i
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [258, 128, 32, 10, 4, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [258, 128, 32, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 32, 10, 4, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [262, 128, 32, 20, 10, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [262, 128, 32, 20, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 32, 20, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [262, 128, 32, 22, 10, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [262, 128, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 32, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [262, 128, 68, 32, 10, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [262, 128, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [262, 128, 70, 32, 10, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [262, 128, 70, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 70, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [262, 128, 84, 32, 10, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [262, 128, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [262, 128, 86, 32, 10, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [262, 128, 86, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [262, 128, 86, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [256, 128, 32, 10, 6, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [256, 128, 32, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [262, 128, 32, 10, 1] ≤ spanCodes [260, 128, 64, 32, 16, 8, 2, 1]
    apply step109wc187_spanCodes_le_of_gens [262, 128, 32, 10, 1] (spanCodes [260, 128, 64, 32, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 128, 64, 32, 16, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o187CoverSound_wc (i : Fin 9) (M : Mat3) (h : o187Cover_wc i M) : M ∈ o187SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [258, 128, 32, 10, 4, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 32, 10, 4, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 32, 20, 10, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 32, 20, 10, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 32, 22, 10, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 32, 22, 10, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 68, 32, 10, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 68, 32, 10, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 70, 32, 10, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 70, 32, 10, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 84, 32, 10, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 84, 32, 10, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [262, 128, 86, 32, 10, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [262, 128, 86, 32, 10, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 32, 10, 6, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 32, 10, 6, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 128, 64, 32, 16, 8, 2, 1]
    unfold o187Cover_wc o187CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 128, 64, 32, 16, 8, 2, 1] (step109wc187MatrixCodeNat M) h
    rwa [step109wc187_codeMat_matrixCode_all] at hspan

private theorem o187Cert_wc : (9 - 1) * 14 < ∑ i : Fin 9, o187Lambda_wc i * o187SourceLb_wc i := by
  simp only [o187Lambda_wc, o187SourceLb_wc]; decide
private theorem o187LambdaSum_wc : 1 ≤ ∑ i : Fin 9, o187Lambda_wc i := by
  simp only [o187Lambda_wc]; decide

theorem o187Lb15_wc
    (hSource : ∀ i : Fin 9, QuotientRankAtLeast (o187SourceU_wc i) (o187SourceLb_wc i)) :
    QuotientRankAtLeast o187W_wc 15 :=
  quotientRankAtLeast_of_contradiction o187W_wc 15 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o187SourceU_wc o187SourceLb_wc
      o187Lambda_wc 1 14
      o187Cover_wc o187W_le_source_wc hSource
      o187LambdaSum_wc o187CoverSound_wc
      (fun M => o187MatCoverage_wc M) (by omega) o187Cert_wc D)

end QiushiMatmul
