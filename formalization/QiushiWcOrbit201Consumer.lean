import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 201, exact manifest basis [340, 132, 32, 10, 1]. -/
def o201W_wc : Submodule F2 Mat3 := spanCodes [340, 132, 32, 10, 1]

private theorem step109wc201_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc201MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc201_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc201MatrixCodeNat M) = M := by decide

private theorem step109wc201_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc201_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o201SourceU_wc : Fin 8 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [272, 132, 68, 32, 10, 1]
  | ⟨1, _⟩ => spanCodes [338, 130, 32, 10, 6, 1]
  | ⟨2, _⟩ => spanCodes [326, 132, 32, 18, 10, 1]
  | ⟨3, _⟩ => spanCodes [322, 132, 32, 22, 10, 1]
  | ⟨4, _⟩ => spanCodes [276, 132, 64, 32, 10, 1]
  | ⟨5, _⟩ => spanCodes [256, 132, 84, 32, 10, 1]
  | ⟨6, _⟩ => spanCodes [260, 132, 80, 32, 8, 2, 1]
  | ⟨7, _⟩ => spanCodes [258, 128, 66, 32, 16, 10, 4, 1]
  | ⟨k + 8, h⟩ => absurd h (by omega)

def o201SourceLb_wc : Fin 8 → ℕ
  | ⟨k, _⟩ => [15, 14, 14, 14, 14, 14, 12, 9].getD k 0

def o201Lambda_wc : Fin 8 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 1, 1, 1, 1, 1].getD k 0

def o201CoverB_wc : Fin 8 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [272, 132, 68, 32, 10, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [338, 130, 32, 10, 6, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [326, 132, 32, 18, 10, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [322, 132, 32, 22, 10, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [276, 132, 64, 32, 10, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [256, 132, 84, 32, 10, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [260, 132, 80, 32, 8, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [258, 128, 66, 32, 16, 10, 4, 1] c
  | ⟨k + 8, h⟩, _ => absurd h (by omega)

def o201Cover_wc (i : Fin 8) (M : Mat3) : Prop :=
  o201CoverB_wc i (step109wc201MatrixCodeNat M) = true

theorem o201CodeCoverage_wc (c : Fin 512) :
    1 ≤ ∑ i : Fin 8, if o201CoverB_wc i c.val = true then o201Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o201MatCoverage_wc (M : Mat3) :
    1 ≤ ∑ i : Fin 8, if o201Cover_wc i M then o201Lambda_wc i else 0 := by
  have h := o201CodeCoverage_wc ⟨step109wc201MatrixCodeNat M, step109wc201_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o201CoverB_wc i (step109wc201MatrixCodeNat M) <;> simp [o201Cover_wc, hb]

theorem o201W_le_source_wc (i : Fin 8) : o201W_wc ≤ o201SourceU_wc i := by
  fin_cases i
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [272, 132, 68, 32, 10, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [272, 132, 68, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [338, 130, 32, 10, 6, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [338, 130, 32, 10, 6, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [338, 130, 32, 10, 6, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [326, 132, 32, 18, 10, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [326, 132, 32, 18, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [326, 132, 32, 18, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [322, 132, 32, 22, 10, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [322, 132, 32, 22, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [322, 132, 32, 22, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [276, 132, 64, 32, 10, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [276, 132, 64, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 132, 64, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [256, 132, 84, 32, 10, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [256, 132, 84, 32, 10, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 132, 84, 32, 10, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [260, 132, 80, 32, 8, 2, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [260, 132, 80, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 80, 32, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [340, 132, 32, 10, 1] ≤ spanCodes [258, 128, 66, 32, 16, 10, 4, 1]
    apply step109wc201_spanCodes_le_of_gens [340, 132, 32, 10, 1] (spanCodes [258, 128, 66, 32, 16, 10, 4, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 4, 1] n (by fin_cases hn <;> decide)

theorem o201CoverSound_wc (i : Fin 8) (M : Mat3) (h : o201Cover_wc i M) : M ∈ o201SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [272, 132, 68, 32, 10, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 132, 68, 32, 10, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [338, 130, 32, 10, 6, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [338, 130, 32, 10, 6, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [326, 132, 32, 18, 10, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [326, 132, 32, 18, 10, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [322, 132, 32, 22, 10, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [322, 132, 32, 22, 10, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 132, 64, 32, 10, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 132, 64, 32, 10, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 132, 84, 32, 10, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 132, 84, 32, 10, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 132, 80, 32, 8, 2, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 80, 32, 8, 2, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [258, 128, 66, 32, 16, 10, 4, 1]
    unfold o201Cover_wc o201CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [258, 128, 66, 32, 16, 10, 4, 1] (step109wc201MatrixCodeNat M) h
    rwa [step109wc201_codeMat_matrixCode_all] at hspan

private theorem o201Cert_wc : (8 - 1) * 15 < ∑ i : Fin 8, o201Lambda_wc i * o201SourceLb_wc i := by
  simp only [o201Lambda_wc, o201SourceLb_wc]; decide
private theorem o201LambdaSum_wc : 1 ≤ ∑ i : Fin 8, o201Lambda_wc i := by
  simp only [o201Lambda_wc]; decide

theorem o201Lb16_wc
    (hSource : ∀ i : Fin 8, QuotientRankAtLeast (o201SourceU_wc i) (o201SourceLb_wc i)) :
    QuotientRankAtLeast o201W_wc 16 :=
  quotientRankAtLeast_of_contradiction o201W_wc 16 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o201SourceU_wc o201SourceLb_wc
      o201Lambda_wc 1 15
      o201Cover_wc o201W_le_source_wc hSource
      o201LambdaSum_wc o201CoverSound_wc
      (fun M => o201MatCoverage_wc M) (by omega) o201Cert_wc D)

end QiushiMatmul
