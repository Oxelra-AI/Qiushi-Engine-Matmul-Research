import QiushiDirectCoverage
import QiushiCodeSpanCore
import QiushiOrbitTransport

set_option maxHeartbeats 200000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

/-- Weighted-cover target orbit 113, exact manifest basis [384, 96, 8, 2, 1]. -/
def o113W_wc : Submodule F2 Mat3 := spanCodes [384, 96, 8, 2, 1]

private theorem step109wc113_matrixCodeNat_lt_all : ∀ M : Mat3,
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0) < 512 := by decide

def step109wc113MatrixCodeNat (M : Mat3) : Nat :=
    (if M 0 0 = 1 then 1 else 0) + (if M 0 1 = 1 then 2 else 0) +
    (if M 0 2 = 1 then 4 else 0) + (if M 1 0 = 1 then 8 else 0) +
    (if M 1 1 = 1 then 16 else 0) + (if M 1 2 = 1 then 32 else 0) +
    (if M 2 0 = 1 then 64 else 0) + (if M 2 1 = 1 then 128 else 0) +
    (if M 2 2 = 1 then 256 else 0)

private theorem step109wc113_codeMat_matrixCode_all : ∀ M : Mat3,
    codeMat (step109wc113MatrixCodeNat M) = M := by decide

private theorem step109wc113_spanCodes_le_of_gens (basis : List Nat) (U : Submodule F2 Mat3)
    (h : ∀ n ∈ basis, codeMat n ∈ U) : spanCodes basis ≤ U := by
  unfold spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM
    rcases hM with ⟨n, hn, rfl⟩
    exact h n hn)

private theorem step109wc113_codeMat_mem_actionW_of_witness
    {P Q : Mat3} {V : Submodule F2 Mat3} {witness target : Nat}
    (h_mem : codeMat witness ∈ V)
    (h_action : actionA P Q (codeMat witness) = codeMat target) :
    codeMat target ∈ actionW P Q V := by
  change ∃ X, X ∈ V ∧ actionA P Q X = codeMat target
  exact ⟨codeMat witness, h_mem, h_action⟩

def o113SourceU_wc : Fin 12 → Submodule F2 Mat3
  | ⟨0, _⟩ => spanCodes [384, 96, 20, 8, 2, 1]
  | ⟨1, _⟩ => spanCodes [308, 180, 96, 8, 2, 1]
  | ⟨2, _⟩ => spanCodes [384, 84, 52, 8, 2, 1]
  | ⟨3, _⟩ => spanCodes [256, 128, 96, 8, 2, 1]
  | ⟨4, _⟩ => spanCodes [260, 132, 96, 16, 8, 2, 1]
  | ⟨5, _⟩ => spanCodes [288, 160, 96, 8, 2, 1]
  | ⟨6, _⟩ => spanCodes [276, 148, 80, 48, 8, 2, 1]
  | ⟨7, _⟩ => spanCodes [276, 148, 68, 36, 8, 2, 1]
  | ⟨8, _⟩ => spanCodes [272, 144, 68, 36, 8, 2, 1]
  | ⟨9, _⟩ => spanCodes [384, 96, 8, 4, 2, 1]
  | ⟨10, _⟩ => spanCodes [384, 64, 32, 20, 8, 2, 1]
  | ⟨11, _⟩ => spanCodes [272, 144, 64, 32, 8, 2, 1]
  | ⟨k + 12, h⟩ => absurd h (by omega)

def o113SourceLb_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [13, 13, 12, 12, 12, 12, 12, 12, 12, 11, 9, 9].getD k 0

def o113Lambda_wc : Fin 12 → ℕ
  | ⟨k, _⟩ => [1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1].getD k 0

def o113CoverB_wc : Fin 12 → Nat → Bool
  | ⟨0, _⟩, c => spanContainsCodeCore [384, 96, 20, 8, 2, 1] c
  | ⟨1, _⟩, c => spanContainsCodeCore [308, 180, 96, 8, 2, 1] c
  | ⟨2, _⟩, c => spanContainsCodeCore [384, 84, 52, 8, 2, 1] c
  | ⟨3, _⟩, c => spanContainsCodeCore [256, 128, 96, 8, 2, 1] c
  | ⟨4, _⟩, c => spanContainsCodeCore [260, 132, 96, 16, 8, 2, 1] c
  | ⟨5, _⟩, c => spanContainsCodeCore [288, 160, 96, 8, 2, 1] c
  | ⟨6, _⟩, c => spanContainsCodeCore [276, 148, 80, 48, 8, 2, 1] c
  | ⟨7, _⟩, c => spanContainsCodeCore [276, 148, 68, 36, 8, 2, 1] c
  | ⟨8, _⟩, c => spanContainsCodeCore [272, 144, 68, 36, 8, 2, 1] c
  | ⟨9, _⟩, c => spanContainsCodeCore [384, 96, 8, 4, 2, 1] c
  | ⟨10, _⟩, c => spanContainsCodeCore [384, 64, 32, 20, 8, 2, 1] c
  | ⟨11, _⟩, c => spanContainsCodeCore [272, 144, 64, 32, 8, 2, 1] c
  | ⟨k + 12, h⟩, _ => absurd h (by omega)

def o113Cover_wc (i : Fin 12) (M : Mat3) : Prop :=
  o113CoverB_wc i (step109wc113MatrixCodeNat M) = true

theorem o113CodeCoverage_wc (c : Fin 512) :
    2 ≤ ∑ i : Fin 12, if o113CoverB_wc i c.val = true then o113Lambda_wc i else 0 := by
  fin_cases c <;> decide

theorem o113MatCoverage_wc (M : Mat3) :
    2 ≤ ∑ i : Fin 12, if o113Cover_wc i M then o113Lambda_wc i else 0 := by
  have h := o113CodeCoverage_wc ⟨step109wc113MatrixCodeNat M, step109wc113_matrixCodeNat_lt_all M⟩
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hb : o113CoverB_wc i (step109wc113MatrixCodeNat M) <;> simp [o113Cover_wc, hb]

theorem o113W_le_source_wc (i : Fin 12) : o113W_wc ≤ o113SourceU_wc i := by
  fin_cases i
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [384, 96, 20, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [384, 96, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 96, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [308, 180, 96, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [308, 180, 96, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [308, 180, 96, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [384, 84, 52, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [384, 84, 52, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 84, 52, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [256, 128, 96, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [256, 128, 96, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [260, 132, 96, 16, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [260, 132, 96, 16, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 16, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [288, 160, 96, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [288, 160, 96, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [276, 148, 80, 48, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [276, 148, 80, 48, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 148, 80, 48, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [276, 148, 68, 36, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [276, 148, 68, 36, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [276, 148, 68, 36, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [272, 144, 68, 36, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [272, 144, 68, 36, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 36, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [384, 96, 8, 4, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [384, 96, 8, 4, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 4, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [384, 64, 32, 20, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [384, 64, 32, 20, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [384, 64, 32, 20, 8, 2, 1] n (by fin_cases hn <;> decide)
  · change spanCodes [384, 96, 8, 2, 1] ≤ spanCodes [272, 144, 64, 32, 8, 2, 1]
    apply step109wc113_spanCodes_le_of_gens [384, 96, 8, 2, 1] (spanCodes [272, 144, 64, 32, 8, 2, 1])
    intro n hn
    exact spanContainsCodeCore_implies_mem_spanCodes [272, 144, 64, 32, 8, 2, 1] n (by fin_cases hn <;> decide)

theorem o113CoverSound_wc (i : Fin 12) (M : Mat3) (h : o113Cover_wc i M) : M ∈ o113SourceU_wc i := by
  fin_cases i
  · change M ∈ spanCodes [384, 96, 20, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 96, 20, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [308, 180, 96, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [308, 180, 96, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 84, 52, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 84, 52, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [256, 128, 96, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [256, 128, 96, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [260, 132, 96, 16, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [260, 132, 96, 16, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [288, 160, 96, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [288, 160, 96, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 148, 80, 48, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 148, 80, 48, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [276, 148, 68, 36, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [276, 148, 68, 36, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 144, 68, 36, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 68, 36, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 96, 8, 4, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 96, 8, 4, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [384, 64, 32, 20, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [384, 64, 32, 20, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan
  · change M ∈ spanCodes [272, 144, 64, 32, 8, 2, 1]
    unfold o113Cover_wc o113CoverB_wc at h
    have hspan := spanContainsCodeCore_implies_mem_spanCodes [272, 144, 64, 32, 8, 2, 1] (step109wc113MatrixCodeNat M) h
    rwa [step109wc113_codeMat_matrixCode_all] at hspan

private theorem o113Cert_wc : (17 - 2) * 13 < ∑ i : Fin 12, o113Lambda_wc i * o113SourceLb_wc i := by
  simp only [o113Lambda_wc, o113SourceLb_wc]; decide
private theorem o113LambdaSum_wc : 2 ≤ ∑ i : Fin 12, o113Lambda_wc i := by
  simp only [o113Lambda_wc]; decide

theorem o113Lb14_wc
    (hSource : ∀ i : Fin 12, QuotientRankAtLeast (o113SourceU_wc i) (o113SourceLb_wc i)) :
    QuotientRankAtLeast o113W_wc 14 :=
  quotientRankAtLeast_of_contradiction o113W_wc 14 (fun r hr D =>
    direct_coverage_quotient_decomp_false_of_cover
      o113SourceU_wc o113SourceLb_wc
      o113Lambda_wc 2 13
      o113Cover_wc o113W_le_source_wc hSource
      o113LambdaSum_wc o113CoverSound_wc
      (fun M => o113MatCoverage_wc M) (by omega) o113Cert_wc D)

end QiushiMatmul
