import QiushiFlattenSeeds
import QiushiWeightedCover

/-!
Generated qdim=2 occupation consumers.

Each source bound is proved for the actual source hyperplane used by the
occupation row, via a contraction minor for its annihilating functional.
No representative-orbit transport is assumed.
-/

set_option maxHeartbeats 32000000
open BigOperators Finset Matrix
namespace QiushiMatmul

theorem F2_ne_zero_eq_one_81 (x : F2) (h : x ≠ 0) : x = 1 := by
  revert x
  decide

theorem evalFunc_add_left81 (L N M : Mat3) :
    evalFunc (L + N) M = evalFunc L M + evalFunc N M := by
  unfold evalFunc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  show (L + N) i j * M i j = L i j * M i j + N i j * M i j
  rw [show (L + N) i j = L i j + N i j from rfl, add_mul]

def sect2_81 (s1 s2 : Mat3) : Fin 3 → Mat3
  | ⟨0, _⟩ => s1
  | ⟨1, _⟩ => s2
  | ⟨2, _⟩ => s1 + s2

def label2_81 (F G : Mat3) (M : Mat3) : Fin 4 :=
  if evalFunc F M = 0 then
    if evalFunc G M = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  else
    if evalFunc G M = 0 then ⟨1, by decide⟩ else ⟨3, by decide⟩

def Wpair2_81 (F G : Mat3) : Submodule F2 Mat3 := kerEvalFunc F ⊓ kerEvalFunc G

theorem label2_zero_mem_81 (F G : Mat3) (M : Mat3) :
    label2_81 F G M = 0 → M ∈ Wpair2_81 F G := by
  intro h
  unfold label2_81 at h
  by_cases hf : evalFunc F M = 0
  · by_cases hg : evalFunc G M = 0
    · change M ∈ kerEvalFunc F ∧ M ∈ kerEvalFunc G
      exact ⟨hf, hg⟩
    · simp [hf, hg] at h
  · by_cases hg : evalFunc G M = 0 <;> simp [hf, hg] at h

theorem label2_sect_coset_81 (F G s1 s2 : Mat3)
    (hF1 : evalFunc F s1 = 1) (hG1 : evalFunc G s1 = 0)
    (hF2 : evalFunc F s2 = 0) (hG2 : evalFunc G s2 = 1)
    (M : Mat3) (p : Fin 3) :
    label2_81 F G M = Fin.succ p → M + sect2_81 s1 s2 p ∈ Wpair2_81 F G := by
  intro h
  unfold label2_81 at h
  fin_cases p
  · by_cases hf : evalFunc F M = 0
    · by_cases hg : evalFunc G M = 0 <;> simp [hf, hg] at h
    · by_cases hg : evalFunc G M = 0
      · change evalFunc F (M + s1) = 0 ∧ evalFunc G (M + s1) = 0
        have hf1 : evalFunc F M = 1 := F2_ne_zero_eq_one_81 _ hf
        constructor
        · rw [evalFunc_add, hf1, hF1]
          decide
        · rw [evalFunc_add, hg, hG1, add_zero]
      · simp [hf, hg] at h
  · by_cases hf : evalFunc F M = 0
    · by_cases hg : evalFunc G M = 0
      · simp [hf, hg] at h
      · change evalFunc F (M + s2) = 0 ∧ evalFunc G (M + s2) = 0
        have hg1 : evalFunc G M = 1 := F2_ne_zero_eq_one_81 _ hg
        constructor
        · rw [evalFunc_add, hf, hF2, add_zero]
        · rw [evalFunc_add, hg1, hG2]
          decide
    · by_cases hg : evalFunc G M = 0 <;> simp [hf, hg] at h
  · by_cases hf : evalFunc F M = 0
    · by_cases hg : evalFunc G M = 0 <;> simp [hf, hg] at h
    · by_cases hg : evalFunc G M = 0
      · simp [hf, hg] at h
      · change evalFunc F (M + (s1 + s2)) = 0 ∧ evalFunc G (M + (s1 + s2)) = 0
        have hf1 : evalFunc F M = 1 := F2_ne_zero_eq_one_81 _ hf
        have hg1 : evalFunc G M = 1 := F2_ne_zero_eq_one_81 _ hg
        constructor
        · rw [evalFunc_add, evalFunc_add, hf1, hF1, hF2]
          decide
        · rw [evalFunc_add, evalFunc_add, hg1, hG1, hG2]
          decide

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 8, target 6 -> lb 7
-- W_basis=[304, 160, 64, 8, 4, 2, 1]; f=272, g=416; sections=16,32,48
-- ============================================================================

def step81o8s0Wspan : Submodule F2 Mat3 := spanCodes [304, 160, 64, 8, 4, 2, 1]
def step81o8s0Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 416)
def step81o8s0Sect : Fin 3 → Mat3 := sect2_81 (codeMat 16) (codeMat 32)
def step81o8s0Label : Mat3 → Fin 4 := label2_81 (codeMat 272) (codeMat 416)

-- source row 0: mask=1 U_basis=[288, 160, 64, 16, 8, 4, 2, 1] L=416 lb=6
def step81o8s0Rows0 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s0Cols0 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s0Q0 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
theorem step81o8s0Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 416)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 416) 6 step81o8s0Rows0 step81o8s0Cols0 step81o8s0Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[272, 128, 64, 32, 8, 4, 2, 1] L=272 lb=6
def step81o8s0Rows1 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s0Cols1 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s0Q1 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
theorem step81o8s0Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 272)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 272) 6 step81o8s0Rows1 step81o8s0Cols1 step81o8s0Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 144, 64, 48, 8, 4, 2, 1] L=176 lb=6
def step81o8s0Rows2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s0Cols2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s0Q2 : Matrix (Fin 6) (Fin 6) F2 := ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
theorem step81o8s0Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 176)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 176) 6 step81o8s0Rows2 step81o8s0Cols2 step81o8s0Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o8s0SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 416)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 272)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 176)
def step81o8s0SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 6
def step81o8s0Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o8s0Wpair_le_sourceU (i : Fin 3) : step81o8s0Wpair ≤ step81o8s0SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 272) ∧ M ∈ kerEvalFunc (codeMat 416) at hM
  fin_cases i
  · change evalFunc (codeMat 416) M = 0
    exact hM.2
  · change evalFunc (codeMat 272) M = 0
    exact hM.1
  · change evalFunc (codeMat 176) M = 0
    rw [show codeMat 176 = codeMat 272 + codeMat 416 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o8s0Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o8s0SourceU i) (step81o8s0SourceLb i) := by
  fin_cases i <;> simp [step81o8s0SourceU, step81o8s0SourceLb, step81o8s0Seed0, step81o8s0Seed1, step81o8s0Seed2]

theorem step81o8s0Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o8s0Mask i → step81o8s0Sect p ∈ step81o8s0SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o8s0Mask] at h
  · change evalFunc (codeMat 416) (codeMat 16) = 0
    decide
  · change evalFunc (codeMat 272) (codeMat 32) = 0
    decide
  · change evalFunc (codeMat 176) (codeMat 16 + codeMat 32) = 0
    rw [evalFunc_add]
    decide

theorem step81o8s0Label_zero_mem (M : Mat3) : step81o8s0Label M = 0 → M ∈ step81o8s0Wpair :=
  label2_zero_mem_81 (codeMat 272) (codeMat 416) M

theorem step81o8s0Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o8s0Label M = Fin.succ p → M + step81o8s0Sect p ∈ step81o8s0Wpair := by
  exact label2_sect_coset_81 (codeMat 272) (codeMat 416) (codeMat 16) (codeMat 32)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o8s0NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o8s0Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o8s0Pair_false_le_target {r : ℕ} (hrt : r ≤ 6)
    (D : QuotientTensorDecomp step81o8s0Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 6 <
      ∑ i : Fin 3, (1 : ℕ) * step81o8s0SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o8s0Label step81o8s0Sect step81o8s0SourceU
    step81o8s0SourceLb step81o8s0Mask (fun _ : Fin 3 => 1) 1 6
    step81o8s0Wpair_le_sourceU step81o8s0Source_lb step81o8s0Label_zero_mem step81o8s0Label_sect_coset
    step81o8s0Sect_source hZeroCoverage step81o8s0NonzeroCoverage hrt hCert D

theorem step81o8s0Pair_lb : QuotientRankAtLeast step81o8s0Wpair 7 :=
  quotientRankAtLeast_of_contradiction step81o8s0Wpair 7
    (fun r hr D => step81o8s0Pair_false_le_target (by omega) D)

theorem step81o8s0Wspan_le_pair : step81o8s0Wspan ≤ step81o8s0Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 272) ∧ M ∈ kerEvalFunc (codeMat 416)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [304, 160, 64, 8, 4, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 416) [304, 160, 64, 8, 4, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o8s0Span_lb : QuotientRankAtLeast step81o8s0Wspan 7 :=
  quotientRankAtLeast_mono step81o8s0Wspan_le_pair step81o8s0Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 8, target 7 -> lb 8
-- W_basis=[304, 160, 64, 8, 4, 2, 1]; f=272, g=416; sections=16,32,48
-- ============================================================================

def step81o8s1Wspan : Submodule F2 Mat3 := spanCodes [304, 160, 64, 8, 4, 2, 1]
def step81o8s1Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 416)
def step81o8s1Sect : Fin 3 → Mat3 := sect2_81 (codeMat 16) (codeMat 32)
def step81o8s1Label : Mat3 → Fin 4 := label2_81 (codeMat 272) (codeMat 416)

-- source row 0: mask=1 U_basis=[288, 160, 64, 16, 8, 4, 2, 1] L=416 lb=6
def step81o8s1Rows0 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s1Cols0 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s1Q0 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
theorem step81o8s1Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 416)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 416) 6 step81o8s1Rows0 step81o8s1Cols0 step81o8s1Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[272, 128, 64, 32, 8, 4, 2, 1] L=272 lb=6
def step81o8s1Rows1 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s1Cols1 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s1Q1 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
theorem step81o8s1Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 272)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 272) 6 step81o8s1Rows1 step81o8s1Cols1 step81o8s1Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 144, 64, 48, 8, 4, 2, 1] L=176 lb=6
def step81o8s1Rows2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s1Cols2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s1Q2 : Matrix (Fin 6) (Fin 6) F2 := ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
theorem step81o8s1Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 176)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 176) 6 step81o8s1Rows2 step81o8s1Cols2 step81o8s1Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o8s1SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 416)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 272)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 176)
def step81o8s1SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 6
def step81o8s1Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o8s1Wpair_le_sourceU (i : Fin 3) : step81o8s1Wpair ≤ step81o8s1SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 272) ∧ M ∈ kerEvalFunc (codeMat 416) at hM
  fin_cases i
  · change evalFunc (codeMat 416) M = 0
    exact hM.2
  · change evalFunc (codeMat 272) M = 0
    exact hM.1
  · change evalFunc (codeMat 176) M = 0
    rw [show codeMat 176 = codeMat 272 + codeMat 416 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o8s1Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o8s1SourceU i) (step81o8s1SourceLb i) := by
  fin_cases i <;> simp [step81o8s1SourceU, step81o8s1SourceLb, step81o8s1Seed0, step81o8s1Seed1, step81o8s1Seed2]

theorem step81o8s1Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o8s1Mask i → step81o8s1Sect p ∈ step81o8s1SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o8s1Mask] at h
  · change evalFunc (codeMat 416) (codeMat 16) = 0
    decide
  · change evalFunc (codeMat 272) (codeMat 32) = 0
    decide
  · change evalFunc (codeMat 176) (codeMat 16 + codeMat 32) = 0
    rw [evalFunc_add]
    decide

theorem step81o8s1Label_zero_mem (M : Mat3) : step81o8s1Label M = 0 → M ∈ step81o8s1Wpair :=
  label2_zero_mem_81 (codeMat 272) (codeMat 416) M

theorem step81o8s1Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o8s1Label M = Fin.succ p → M + step81o8s1Sect p ∈ step81o8s1Wpair := by
  exact label2_sect_coset_81 (codeMat 272) (codeMat 416) (codeMat 16) (codeMat 32)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o8s1NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o8s1Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o8s1Pair_false_le_target {r : ℕ} (hrt : r ≤ 7)
    (D : QuotientTensorDecomp step81o8s1Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 7 <
      ∑ i : Fin 3, (1 : ℕ) * step81o8s1SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o8s1Label step81o8s1Sect step81o8s1SourceU
    step81o8s1SourceLb step81o8s1Mask (fun _ : Fin 3 => 1) 1 7
    step81o8s1Wpair_le_sourceU step81o8s1Source_lb step81o8s1Label_zero_mem step81o8s1Label_sect_coset
    step81o8s1Sect_source hZeroCoverage step81o8s1NonzeroCoverage hrt hCert D

theorem step81o8s1Pair_lb : QuotientRankAtLeast step81o8s1Wpair 8 :=
  quotientRankAtLeast_of_contradiction step81o8s1Wpair 8
    (fun r hr D => step81o8s1Pair_false_le_target (by omega) D)

theorem step81o8s1Wspan_le_pair : step81o8s1Wspan ≤ step81o8s1Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 272) ∧ M ∈ kerEvalFunc (codeMat 416)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [304, 160, 64, 8, 4, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 416) [304, 160, 64, 8, 4, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o8s1Span_lb : QuotientRankAtLeast step81o8s1Wspan 8 :=
  quotientRankAtLeast_mono step81o8s1Wspan_le_pair step81o8s1Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 8, target 8 -> lb 9
-- W_basis=[304, 160, 64, 8, 4, 2, 1]; f=272, g=416; sections=16,32,48
-- ============================================================================

def step81o8s2Wspan : Submodule F2 Mat3 := spanCodes [304, 160, 64, 8, 4, 2, 1]
def step81o8s2Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 272) ⊓ kerEvalFunc (codeMat 416)
def step81o8s2Sect : Fin 3 → Mat3 := sect2_81 (codeMat 16) (codeMat 32)
def step81o8s2Label : Mat3 → Fin 4 := label2_81 (codeMat 272) (codeMat 416)

-- source row 0: mask=1 U_basis=[288, 160, 64, 16, 8, 4, 2, 1] L=416 lb=6
def step81o8s2Rows0 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s2Cols0 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s2Q0 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
theorem step81o8s2Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 416)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 416) 6 step81o8s2Rows0 step81o8s2Cols0 step81o8s2Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[272, 128, 64, 32, 8, 4, 2, 1] L=272 lb=6
def step81o8s2Rows1 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s2Cols1 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s2Q1 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
theorem step81o8s2Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 272)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 272) 6 step81o8s2Rows1 step81o8s2Cols1 step81o8s2Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 144, 64, 48, 8, 4, 2, 1] L=176 lb=6
def step81o8s2Rows2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s2Cols2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o8s2Q2 : Matrix (Fin 6) (Fin 6) F2 := ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
theorem step81o8s2Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 176)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 176) 6 step81o8s2Rows2 step81o8s2Cols2 step81o8s2Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o8s2SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 416)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 272)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 176)
def step81o8s2SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 6
def step81o8s2Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o8s2Wpair_le_sourceU (i : Fin 3) : step81o8s2Wpair ≤ step81o8s2SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 272) ∧ M ∈ kerEvalFunc (codeMat 416) at hM
  fin_cases i
  · change evalFunc (codeMat 416) M = 0
    exact hM.2
  · change evalFunc (codeMat 272) M = 0
    exact hM.1
  · change evalFunc (codeMat 176) M = 0
    rw [show codeMat 176 = codeMat 272 + codeMat 416 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o8s2Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o8s2SourceU i) (step81o8s2SourceLb i) := by
  fin_cases i <;> simp [step81o8s2SourceU, step81o8s2SourceLb, step81o8s2Seed0, step81o8s2Seed1, step81o8s2Seed2]

theorem step81o8s2Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o8s2Mask i → step81o8s2Sect p ∈ step81o8s2SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o8s2Mask] at h
  · change evalFunc (codeMat 416) (codeMat 16) = 0
    decide
  · change evalFunc (codeMat 272) (codeMat 32) = 0
    decide
  · change evalFunc (codeMat 176) (codeMat 16 + codeMat 32) = 0
    rw [evalFunc_add]
    decide

theorem step81o8s2Label_zero_mem (M : Mat3) : step81o8s2Label M = 0 → M ∈ step81o8s2Wpair :=
  label2_zero_mem_81 (codeMat 272) (codeMat 416) M

theorem step81o8s2Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o8s2Label M = Fin.succ p → M + step81o8s2Sect p ∈ step81o8s2Wpair := by
  exact label2_sect_coset_81 (codeMat 272) (codeMat 416) (codeMat 16) (codeMat 32)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o8s2NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o8s2Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o8s2Pair_false_le_target {r : ℕ} (hrt : r ≤ 8)
    (D : QuotientTensorDecomp step81o8s2Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 8 <
      ∑ i : Fin 3, (1 : ℕ) * step81o8s2SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o8s2Label step81o8s2Sect step81o8s2SourceU
    step81o8s2SourceLb step81o8s2Mask (fun _ : Fin 3 => 1) 1 8
    step81o8s2Wpair_le_sourceU step81o8s2Source_lb step81o8s2Label_zero_mem step81o8s2Label_sect_coset
    step81o8s2Sect_source hZeroCoverage step81o8s2NonzeroCoverage hrt hCert D

theorem step81o8s2Pair_lb : QuotientRankAtLeast step81o8s2Wpair 9 :=
  quotientRankAtLeast_of_contradiction step81o8s2Wpair 9
    (fun r hr D => step81o8s2Pair_false_le_target (by omega) D)

theorem step81o8s2Wspan_le_pair : step81o8s2Wspan ≤ step81o8s2Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 272) ∧ M ∈ kerEvalFunc (codeMat 416)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 272) [304, 160, 64, 8, 4, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 416) [304, 160, 64, 8, 4, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o8s2Span_lb : QuotientRankAtLeast step81o8s2Wspan 9 :=
  quotientRankAtLeast_mono step81o8s2Wspan_le_pair step81o8s2Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 16, target 9 -> lb 10
-- W_basis=[256, 148, 80, 32, 12, 2, 1]; f=140, g=208; sections=4,16,20
-- ============================================================================

def step81o16s0Wspan : Submodule F2 Mat3 := spanCodes [256, 148, 80, 32, 12, 2, 1]
def step81o16s0Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 140) ⊓ kerEvalFunc (codeMat 208)
def step81o16s0Sect : Fin 3 → Mat3 := sect2_81 (codeMat 4) (codeMat 16)
def step81o16s0Label : Mat3 → Fin 4 := label2_81 (codeMat 140) (codeMat 208)

-- source row 0: mask=2 U_basis=[256, 132, 64, 32, 16, 12, 2, 1] L=140 lb=9
def step81o16s0Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s0Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s0Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0]]
theorem step81o16s0Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 140)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 140) 9 step81o16s0Rows0 step81o16s0Cols0 step81o16s0Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=4 U_basis=[256, 128, 68, 32, 20, 12, 2, 1] L=92 lb=9
def step81o16s0Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s0Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s0Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 0]]
theorem step81o16s0Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 92)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 92) 9 step81o16s0Rows1 step81o16s0Cols1 step81o16s0Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=1 U_basis=[256, 144, 80, 32, 8, 4, 2, 1] L=208 lb=6
def step81o16s0Rows2 : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
def step81o16s0Cols2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s0Q2 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
theorem step81o16s0Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 208)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 208) 6 step81o16s0Rows2 step81o16s0Cols2 step81o16s0Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o16s0SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 140)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 92)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 208)
def step81o16s0SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 6
def step81o16s0Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({1} : Finset (Fin 3))
  | ⟨1, _⟩ => ({2} : Finset (Fin 3))
  | ⟨2, _⟩ => ({0} : Finset (Fin 3))

theorem step81o16s0Wpair_le_sourceU (i : Fin 3) : step81o16s0Wpair ≤ step81o16s0SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 140) ∧ M ∈ kerEvalFunc (codeMat 208) at hM
  fin_cases i
  · change evalFunc (codeMat 140) M = 0
    exact hM.1
  · change evalFunc (codeMat 92) M = 0
    rw [show codeMat 92 = codeMat 140 + codeMat 208 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]
  · change evalFunc (codeMat 208) M = 0
    exact hM.2

theorem step81o16s0Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o16s0SourceU i) (step81o16s0SourceLb i) := by
  fin_cases i <;> simp [step81o16s0SourceU, step81o16s0SourceLb, step81o16s0Seed0, step81o16s0Seed1, step81o16s0Seed2]

theorem step81o16s0Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o16s0Mask i → step81o16s0Sect p ∈ step81o16s0SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o16s0Mask] at h
  · change evalFunc (codeMat 140) (codeMat 16) = 0
    decide
  · change evalFunc (codeMat 92) (codeMat 4 + codeMat 16) = 0
    rw [evalFunc_add]
    decide
  · change evalFunc (codeMat 208) (codeMat 4) = 0
    decide

theorem step81o16s0Label_zero_mem (M : Mat3) : step81o16s0Label M = 0 → M ∈ step81o16s0Wpair :=
  label2_zero_mem_81 (codeMat 140) (codeMat 208) M

theorem step81o16s0Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o16s0Label M = Fin.succ p → M + step81o16s0Sect p ∈ step81o16s0Wpair := by
  exact label2_sect_coset_81 (codeMat 140) (codeMat 208) (codeMat 4) (codeMat 16)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o16s0NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o16s0Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o16s0Pair_false_le_target {r : ℕ} (hrt : r ≤ 9)
    (D : QuotientTensorDecomp step81o16s0Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 9 <
      ∑ i : Fin 3, (1 : ℕ) * step81o16s0SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o16s0Label step81o16s0Sect step81o16s0SourceU
    step81o16s0SourceLb step81o16s0Mask (fun _ : Fin 3 => 1) 1 9
    step81o16s0Wpair_le_sourceU step81o16s0Source_lb step81o16s0Label_zero_mem step81o16s0Label_sect_coset
    step81o16s0Sect_source hZeroCoverage step81o16s0NonzeroCoverage hrt hCert D

theorem step81o16s0Pair_lb : QuotientRankAtLeast step81o16s0Wpair 10 :=
  quotientRankAtLeast_of_contradiction step81o16s0Wpair 10
    (fun r hr D => step81o16s0Pair_false_le_target (by omega) D)

theorem step81o16s0Wspan_le_pair : step81o16s0Wspan ≤ step81o16s0Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 140) ∧ M ∈ kerEvalFunc (codeMat 208)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [256, 148, 80, 32, 12, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 208) [256, 148, 80, 32, 12, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o16s0Span_lb : QuotientRankAtLeast step81o16s0Wspan 10 :=
  quotientRankAtLeast_mono step81o16s0Wspan_le_pair step81o16s0Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 16, target 10 -> lb 11
-- W_basis=[256, 148, 80, 32, 12, 2, 1]; f=140, g=208; sections=4,16,20
-- ============================================================================

def step81o16s1Wspan : Submodule F2 Mat3 := spanCodes [256, 148, 80, 32, 12, 2, 1]
def step81o16s1Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 140) ⊓ kerEvalFunc (codeMat 208)
def step81o16s1Sect : Fin 3 → Mat3 := sect2_81 (codeMat 4) (codeMat 16)
def step81o16s1Label : Mat3 → Fin 4 := label2_81 (codeMat 140) (codeMat 208)

-- source row 0: mask=2 U_basis=[256, 132, 64, 32, 16, 12, 2, 1] L=140 lb=9
def step81o16s1Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s1Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s1Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0]]
theorem step81o16s1Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 140)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 140) 9 step81o16s1Rows0 step81o16s1Cols0 step81o16s1Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=4 U_basis=[256, 128, 68, 32, 20, 12, 2, 1] L=92 lb=9
def step81o16s1Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s1Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s1Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 0]]
theorem step81o16s1Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 92)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 92) 9 step81o16s1Rows1 step81o16s1Cols1 step81o16s1Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=1 U_basis=[256, 144, 80, 32, 8, 4, 2, 1] L=208 lb=6
def step81o16s1Rows2 : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
def step81o16s1Cols2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s1Q2 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
theorem step81o16s1Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 208)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 208) 6 step81o16s1Rows2 step81o16s1Cols2 step81o16s1Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o16s1SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 140)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 92)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 208)
def step81o16s1SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 6
def step81o16s1Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({1} : Finset (Fin 3))
  | ⟨1, _⟩ => ({2} : Finset (Fin 3))
  | ⟨2, _⟩ => ({0} : Finset (Fin 3))

theorem step81o16s1Wpair_le_sourceU (i : Fin 3) : step81o16s1Wpair ≤ step81o16s1SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 140) ∧ M ∈ kerEvalFunc (codeMat 208) at hM
  fin_cases i
  · change evalFunc (codeMat 140) M = 0
    exact hM.1
  · change evalFunc (codeMat 92) M = 0
    rw [show codeMat 92 = codeMat 140 + codeMat 208 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]
  · change evalFunc (codeMat 208) M = 0
    exact hM.2

theorem step81o16s1Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o16s1SourceU i) (step81o16s1SourceLb i) := by
  fin_cases i <;> simp [step81o16s1SourceU, step81o16s1SourceLb, step81o16s1Seed0, step81o16s1Seed1, step81o16s1Seed2]

theorem step81o16s1Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o16s1Mask i → step81o16s1Sect p ∈ step81o16s1SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o16s1Mask] at h
  · change evalFunc (codeMat 140) (codeMat 16) = 0
    decide
  · change evalFunc (codeMat 92) (codeMat 4 + codeMat 16) = 0
    rw [evalFunc_add]
    decide
  · change evalFunc (codeMat 208) (codeMat 4) = 0
    decide

theorem step81o16s1Label_zero_mem (M : Mat3) : step81o16s1Label M = 0 → M ∈ step81o16s1Wpair :=
  label2_zero_mem_81 (codeMat 140) (codeMat 208) M

theorem step81o16s1Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o16s1Label M = Fin.succ p → M + step81o16s1Sect p ∈ step81o16s1Wpair := by
  exact label2_sect_coset_81 (codeMat 140) (codeMat 208) (codeMat 4) (codeMat 16)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o16s1NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o16s1Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o16s1Pair_false_le_target {r : ℕ} (hrt : r ≤ 10)
    (D : QuotientTensorDecomp step81o16s1Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 10 <
      ∑ i : Fin 3, (1 : ℕ) * step81o16s1SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o16s1Label step81o16s1Sect step81o16s1SourceU
    step81o16s1SourceLb step81o16s1Mask (fun _ : Fin 3 => 1) 1 10
    step81o16s1Wpair_le_sourceU step81o16s1Source_lb step81o16s1Label_zero_mem step81o16s1Label_sect_coset
    step81o16s1Sect_source hZeroCoverage step81o16s1NonzeroCoverage hrt hCert D

theorem step81o16s1Pair_lb : QuotientRankAtLeast step81o16s1Wpair 11 :=
  quotientRankAtLeast_of_contradiction step81o16s1Wpair 11
    (fun r hr D => step81o16s1Pair_false_le_target (by omega) D)

theorem step81o16s1Wspan_le_pair : step81o16s1Wspan ≤ step81o16s1Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 140) ∧ M ∈ kerEvalFunc (codeMat 208)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [256, 148, 80, 32, 12, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 208) [256, 148, 80, 32, 12, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o16s1Span_lb : QuotientRankAtLeast step81o16s1Wspan 11 :=
  quotientRankAtLeast_mono step81o16s1Wspan_le_pair step81o16s1Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 16, target 11 -> lb 12
-- W_basis=[256, 148, 80, 32, 12, 2, 1]; f=140, g=208; sections=4,16,20
-- ============================================================================

def step81o16s2Wspan : Submodule F2 Mat3 := spanCodes [256, 148, 80, 32, 12, 2, 1]
def step81o16s2Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 140) ⊓ kerEvalFunc (codeMat 208)
def step81o16s2Sect : Fin 3 → Mat3 := sect2_81 (codeMat 4) (codeMat 16)
def step81o16s2Label : Mat3 → Fin 4 := label2_81 (codeMat 140) (codeMat 208)

-- source row 0: mask=2 U_basis=[256, 132, 64, 32, 16, 12, 2, 1] L=140 lb=9
def step81o16s2Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s2Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s2Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0]]
theorem step81o16s2Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 140)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 140) 9 step81o16s2Rows0 step81o16s2Cols0 step81o16s2Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=4 U_basis=[256, 128, 68, 32, 20, 12, 2, 1] L=92 lb=9
def step81o16s2Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s2Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s2Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 0]]
theorem step81o16s2Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 92)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 92) 9 step81o16s2Rows1 step81o16s2Cols1 step81o16s2Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=1 U_basis=[256, 144, 80, 32, 8, 4, 2, 1] L=208 lb=6
def step81o16s2Rows2 : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
def step81o16s2Cols2 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o16s2Q2 : Matrix (Fin 6) (Fin 6) F2 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
theorem step81o16s2Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 208)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 208) 6 step81o16s2Rows2 step81o16s2Cols2 step81o16s2Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o16s2SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 140)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 92)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 208)
def step81o16s2SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 6
def step81o16s2Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({1} : Finset (Fin 3))
  | ⟨1, _⟩ => ({2} : Finset (Fin 3))
  | ⟨2, _⟩ => ({0} : Finset (Fin 3))

theorem step81o16s2Wpair_le_sourceU (i : Fin 3) : step81o16s2Wpair ≤ step81o16s2SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 140) ∧ M ∈ kerEvalFunc (codeMat 208) at hM
  fin_cases i
  · change evalFunc (codeMat 140) M = 0
    exact hM.1
  · change evalFunc (codeMat 92) M = 0
    rw [show codeMat 92 = codeMat 140 + codeMat 208 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]
  · change evalFunc (codeMat 208) M = 0
    exact hM.2

theorem step81o16s2Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o16s2SourceU i) (step81o16s2SourceLb i) := by
  fin_cases i <;> simp [step81o16s2SourceU, step81o16s2SourceLb, step81o16s2Seed0, step81o16s2Seed1, step81o16s2Seed2]

theorem step81o16s2Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o16s2Mask i → step81o16s2Sect p ∈ step81o16s2SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o16s2Mask] at h
  · change evalFunc (codeMat 140) (codeMat 16) = 0
    decide
  · change evalFunc (codeMat 92) (codeMat 4 + codeMat 16) = 0
    rw [evalFunc_add]
    decide
  · change evalFunc (codeMat 208) (codeMat 4) = 0
    decide

theorem step81o16s2Label_zero_mem (M : Mat3) : step81o16s2Label M = 0 → M ∈ step81o16s2Wpair :=
  label2_zero_mem_81 (codeMat 140) (codeMat 208) M

theorem step81o16s2Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o16s2Label M = Fin.succ p → M + step81o16s2Sect p ∈ step81o16s2Wpair := by
  exact label2_sect_coset_81 (codeMat 140) (codeMat 208) (codeMat 4) (codeMat 16)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o16s2NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o16s2Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o16s2Pair_false_le_target {r : ℕ} (hrt : r ≤ 11)
    (D : QuotientTensorDecomp step81o16s2Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 11 <
      ∑ i : Fin 3, (1 : ℕ) * step81o16s2SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o16s2Label step81o16s2Sect step81o16s2SourceU
    step81o16s2SourceLb step81o16s2Mask (fun _ : Fin 3 => 1) 1 11
    step81o16s2Wpair_le_sourceU step81o16s2Source_lb step81o16s2Label_zero_mem step81o16s2Label_sect_coset
    step81o16s2Sect_source hZeroCoverage step81o16s2NonzeroCoverage hrt hCert D

theorem step81o16s2Pair_lb : QuotientRankAtLeast step81o16s2Wpair 12 :=
  quotientRankAtLeast_of_contradiction step81o16s2Wpair 12
    (fun r hr D => step81o16s2Pair_false_le_target (by omega) D)

theorem step81o16s2Wspan_le_pair : step81o16s2Wspan ≤ step81o16s2Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 140) ∧ M ∈ kerEvalFunc (codeMat 208)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 140) [256, 148, 80, 32, 12, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 208) [256, 148, 80, 32, 12, 2, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o16s2Span_lb : QuotientRankAtLeast step81o16s2Wspan 12 :=
  quotientRankAtLeast_mono step81o16s2Wspan_le_pair step81o16s2Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 17, target 9 -> lb 10
-- W_basis=[262, 128, 68, 32, 20, 10, 1]; f=266, g=340; sections=2,4,6
-- ============================================================================

def step81o17s0Wspan : Submodule F2 Mat3 := spanCodes [262, 128, 68, 32, 20, 10, 1]
def step81o17s0Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 340)
def step81o17s0Sect : Fin 3 → Mat3 := sect2_81 (codeMat 2) (codeMat 4)
def step81o17s0Label : Mat3 → Fin 4 := label2_81 (codeMat 266) (codeMat 340)

-- source row 0: mask=1 U_basis=[260, 128, 68, 32, 20, 8, 2, 1] L=340 lb=9
def step81o17s0Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s0Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s0Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![1, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0]]
theorem step81o17s0Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 340)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 340) 9 step81o17s0Rows0 step81o17s0Cols0 step81o17s0Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[258, 128, 64, 32, 16, 10, 4, 1] L=266 lb=9
def step81o17s0Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s0Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s0Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]
theorem step81o17s0Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 266)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 266) 9 step81o17s0Rows1 step81o17s0Cols1 step81o17s0Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 128, 66, 32, 18, 10, 6, 1] L=94 lb=9
def step81o17s0Rows2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s0Cols2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s0Q2 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 1]]
theorem step81o17s0Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 94)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 94) 9 step81o17s0Rows2 step81o17s0Cols2 step81o17s0Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o17s0SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 340)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 94)
def step81o17s0SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
def step81o17s0Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o17s0Wpair_le_sourceU (i : Fin 3) : step81o17s0Wpair ≤ step81o17s0SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340) at hM
  fin_cases i
  · change evalFunc (codeMat 340) M = 0
    exact hM.2
  · change evalFunc (codeMat 266) M = 0
    exact hM.1
  · change evalFunc (codeMat 94) M = 0
    rw [show codeMat 94 = codeMat 266 + codeMat 340 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o17s0Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o17s0SourceU i) (step81o17s0SourceLb i) := by
  fin_cases i <;> simp [step81o17s0SourceU, step81o17s0SourceLb, step81o17s0Seed0, step81o17s0Seed1, step81o17s0Seed2]

theorem step81o17s0Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o17s0Mask i → step81o17s0Sect p ∈ step81o17s0SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o17s0Mask] at h
  · change evalFunc (codeMat 340) (codeMat 2) = 0
    decide
  · change evalFunc (codeMat 266) (codeMat 4) = 0
    decide
  · change evalFunc (codeMat 94) (codeMat 2 + codeMat 4) = 0
    rw [evalFunc_add]
    decide

theorem step81o17s0Label_zero_mem (M : Mat3) : step81o17s0Label M = 0 → M ∈ step81o17s0Wpair :=
  label2_zero_mem_81 (codeMat 266) (codeMat 340) M

theorem step81o17s0Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o17s0Label M = Fin.succ p → M + step81o17s0Sect p ∈ step81o17s0Wpair := by
  exact label2_sect_coset_81 (codeMat 266) (codeMat 340) (codeMat 2) (codeMat 4)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o17s0NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o17s0Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o17s0Pair_false_le_target {r : ℕ} (hrt : r ≤ 9)
    (D : QuotientTensorDecomp step81o17s0Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 9 <
      ∑ i : Fin 3, (1 : ℕ) * step81o17s0SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o17s0Label step81o17s0Sect step81o17s0SourceU
    step81o17s0SourceLb step81o17s0Mask (fun _ : Fin 3 => 1) 1 9
    step81o17s0Wpair_le_sourceU step81o17s0Source_lb step81o17s0Label_zero_mem step81o17s0Label_sect_coset
    step81o17s0Sect_source hZeroCoverage step81o17s0NonzeroCoverage hrt hCert D

theorem step81o17s0Pair_lb : QuotientRankAtLeast step81o17s0Wpair 10 :=
  quotientRankAtLeast_of_contradiction step81o17s0Wpair 10
    (fun r hr D => step81o17s0Pair_false_le_target (by omega) D)

theorem step81o17s0Wspan_le_pair : step81o17s0Wspan ≤ step81o17s0Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 340) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o17s0Span_lb : QuotientRankAtLeast step81o17s0Wspan 10 :=
  quotientRankAtLeast_mono step81o17s0Wspan_le_pair step81o17s0Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 17, target 10 -> lb 11
-- W_basis=[262, 128, 68, 32, 20, 10, 1]; f=266, g=340; sections=2,4,6
-- ============================================================================

def step81o17s1Wspan : Submodule F2 Mat3 := spanCodes [262, 128, 68, 32, 20, 10, 1]
def step81o17s1Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 340)
def step81o17s1Sect : Fin 3 → Mat3 := sect2_81 (codeMat 2) (codeMat 4)
def step81o17s1Label : Mat3 → Fin 4 := label2_81 (codeMat 266) (codeMat 340)

-- source row 0: mask=1 U_basis=[260, 128, 68, 32, 20, 8, 2, 1] L=340 lb=9
def step81o17s1Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s1Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s1Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![1, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0]]
theorem step81o17s1Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 340)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 340) 9 step81o17s1Rows0 step81o17s1Cols0 step81o17s1Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[258, 128, 64, 32, 16, 10, 4, 1] L=266 lb=9
def step81o17s1Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s1Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s1Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]
theorem step81o17s1Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 266)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 266) 9 step81o17s1Rows1 step81o17s1Cols1 step81o17s1Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 128, 66, 32, 18, 10, 6, 1] L=94 lb=9
def step81o17s1Rows2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s1Cols2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s1Q2 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 1]]
theorem step81o17s1Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 94)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 94) 9 step81o17s1Rows2 step81o17s1Cols2 step81o17s1Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o17s1SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 340)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 94)
def step81o17s1SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
def step81o17s1Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o17s1Wpair_le_sourceU (i : Fin 3) : step81o17s1Wpair ≤ step81o17s1SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340) at hM
  fin_cases i
  · change evalFunc (codeMat 340) M = 0
    exact hM.2
  · change evalFunc (codeMat 266) M = 0
    exact hM.1
  · change evalFunc (codeMat 94) M = 0
    rw [show codeMat 94 = codeMat 266 + codeMat 340 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o17s1Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o17s1SourceU i) (step81o17s1SourceLb i) := by
  fin_cases i <;> simp [step81o17s1SourceU, step81o17s1SourceLb, step81o17s1Seed0, step81o17s1Seed1, step81o17s1Seed2]

theorem step81o17s1Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o17s1Mask i → step81o17s1Sect p ∈ step81o17s1SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o17s1Mask] at h
  · change evalFunc (codeMat 340) (codeMat 2) = 0
    decide
  · change evalFunc (codeMat 266) (codeMat 4) = 0
    decide
  · change evalFunc (codeMat 94) (codeMat 2 + codeMat 4) = 0
    rw [evalFunc_add]
    decide

theorem step81o17s1Label_zero_mem (M : Mat3) : step81o17s1Label M = 0 → M ∈ step81o17s1Wpair :=
  label2_zero_mem_81 (codeMat 266) (codeMat 340) M

theorem step81o17s1Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o17s1Label M = Fin.succ p → M + step81o17s1Sect p ∈ step81o17s1Wpair := by
  exact label2_sect_coset_81 (codeMat 266) (codeMat 340) (codeMat 2) (codeMat 4)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o17s1NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o17s1Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o17s1Pair_false_le_target {r : ℕ} (hrt : r ≤ 10)
    (D : QuotientTensorDecomp step81o17s1Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 10 <
      ∑ i : Fin 3, (1 : ℕ) * step81o17s1SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o17s1Label step81o17s1Sect step81o17s1SourceU
    step81o17s1SourceLb step81o17s1Mask (fun _ : Fin 3 => 1) 1 10
    step81o17s1Wpair_le_sourceU step81o17s1Source_lb step81o17s1Label_zero_mem step81o17s1Label_sect_coset
    step81o17s1Sect_source hZeroCoverage step81o17s1NonzeroCoverage hrt hCert D

theorem step81o17s1Pair_lb : QuotientRankAtLeast step81o17s1Wpair 11 :=
  quotientRankAtLeast_of_contradiction step81o17s1Wpair 11
    (fun r hr D => step81o17s1Pair_false_le_target (by omega) D)

theorem step81o17s1Wspan_le_pair : step81o17s1Wspan ≤ step81o17s1Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 340) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o17s1Span_lb : QuotientRankAtLeast step81o17s1Wspan 11 :=
  quotientRankAtLeast_mono step81o17s1Wspan_le_pair step81o17s1Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 17, target 11 -> lb 12
-- W_basis=[262, 128, 68, 32, 20, 10, 1]; f=266, g=340; sections=2,4,6
-- ============================================================================

def step81o17s2Wspan : Submodule F2 Mat3 := spanCodes [262, 128, 68, 32, 20, 10, 1]
def step81o17s2Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 340)
def step81o17s2Sect : Fin 3 → Mat3 := sect2_81 (codeMat 2) (codeMat 4)
def step81o17s2Label : Mat3 → Fin 4 := label2_81 (codeMat 266) (codeMat 340)

-- source row 0: mask=1 U_basis=[260, 128, 68, 32, 20, 8, 2, 1] L=340 lb=9
def step81o17s2Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s2Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s2Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![1, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0]]
theorem step81o17s2Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 340)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 340) 9 step81o17s2Rows0 step81o17s2Cols0 step81o17s2Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[258, 128, 64, 32, 16, 10, 4, 1] L=266 lb=9
def step81o17s2Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s2Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s2Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]
theorem step81o17s2Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 266)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 266) 9 step81o17s2Rows1 step81o17s2Cols1 step81o17s2Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 128, 66, 32, 18, 10, 6, 1] L=94 lb=9
def step81o17s2Rows2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s2Cols2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s2Q2 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 1]]
theorem step81o17s2Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 94)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 94) 9 step81o17s2Rows2 step81o17s2Cols2 step81o17s2Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o17s2SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 340)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 94)
def step81o17s2SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
def step81o17s2Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o17s2Wpair_le_sourceU (i : Fin 3) : step81o17s2Wpair ≤ step81o17s2SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340) at hM
  fin_cases i
  · change evalFunc (codeMat 340) M = 0
    exact hM.2
  · change evalFunc (codeMat 266) M = 0
    exact hM.1
  · change evalFunc (codeMat 94) M = 0
    rw [show codeMat 94 = codeMat 266 + codeMat 340 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o17s2Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o17s2SourceU i) (step81o17s2SourceLb i) := by
  fin_cases i <;> simp [step81o17s2SourceU, step81o17s2SourceLb, step81o17s2Seed0, step81o17s2Seed1, step81o17s2Seed2]

theorem step81o17s2Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o17s2Mask i → step81o17s2Sect p ∈ step81o17s2SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o17s2Mask] at h
  · change evalFunc (codeMat 340) (codeMat 2) = 0
    decide
  · change evalFunc (codeMat 266) (codeMat 4) = 0
    decide
  · change evalFunc (codeMat 94) (codeMat 2 + codeMat 4) = 0
    rw [evalFunc_add]
    decide

theorem step81o17s2Label_zero_mem (M : Mat3) : step81o17s2Label M = 0 → M ∈ step81o17s2Wpair :=
  label2_zero_mem_81 (codeMat 266) (codeMat 340) M

theorem step81o17s2Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o17s2Label M = Fin.succ p → M + step81o17s2Sect p ∈ step81o17s2Wpair := by
  exact label2_sect_coset_81 (codeMat 266) (codeMat 340) (codeMat 2) (codeMat 4)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o17s2NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o17s2Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o17s2Pair_false_le_target {r : ℕ} (hrt : r ≤ 11)
    (D : QuotientTensorDecomp step81o17s2Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 11 <
      ∑ i : Fin 3, (1 : ℕ) * step81o17s2SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o17s2Label step81o17s2Sect step81o17s2SourceU
    step81o17s2SourceLb step81o17s2Mask (fun _ : Fin 3 => 1) 1 11
    step81o17s2Wpair_le_sourceU step81o17s2Source_lb step81o17s2Label_zero_mem step81o17s2Label_sect_coset
    step81o17s2Sect_source hZeroCoverage step81o17s2NonzeroCoverage hrt hCert D

theorem step81o17s2Pair_lb : QuotientRankAtLeast step81o17s2Wpair 12 :=
  quotientRankAtLeast_of_contradiction step81o17s2Wpair 12
    (fun r hr D => step81o17s2Pair_false_le_target (by omega) D)

theorem step81o17s2Wspan_le_pair : step81o17s2Wspan ≤ step81o17s2Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 340) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o17s2Span_lb : QuotientRankAtLeast step81o17s2Wspan 12 :=
  quotientRankAtLeast_mono step81o17s2Wspan_le_pair step81o17s2Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 17, target 12 -> lb 13
-- W_basis=[262, 128, 68, 32, 20, 10, 1]; f=266, g=340; sections=2,4,6
-- ============================================================================

def step81o17s3Wspan : Submodule F2 Mat3 := spanCodes [262, 128, 68, 32, 20, 10, 1]
def step81o17s3Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 340)
def step81o17s3Sect : Fin 3 → Mat3 := sect2_81 (codeMat 2) (codeMat 4)
def step81o17s3Label : Mat3 → Fin 4 := label2_81 (codeMat 266) (codeMat 340)

-- source row 0: mask=1 U_basis=[260, 128, 68, 32, 20, 8, 2, 1] L=340 lb=9
def step81o17s3Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s3Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s3Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![1, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0]]
theorem step81o17s3Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 340)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 340) 9 step81o17s3Rows0 step81o17s3Cols0 step81o17s3Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[258, 128, 64, 32, 16, 10, 4, 1] L=266 lb=9
def step81o17s3Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s3Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s3Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]
theorem step81o17s3Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 266)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 266) 9 step81o17s3Rows1 step81o17s3Cols1 step81o17s3Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 128, 66, 32, 18, 10, 6, 1] L=94 lb=9
def step81o17s3Rows2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s3Cols2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s3Q2 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 1]]
theorem step81o17s3Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 94)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 94) 9 step81o17s3Rows2 step81o17s3Cols2 step81o17s3Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o17s3SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 340)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 94)
def step81o17s3SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
def step81o17s3Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o17s3Wpair_le_sourceU (i : Fin 3) : step81o17s3Wpair ≤ step81o17s3SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340) at hM
  fin_cases i
  · change evalFunc (codeMat 340) M = 0
    exact hM.2
  · change evalFunc (codeMat 266) M = 0
    exact hM.1
  · change evalFunc (codeMat 94) M = 0
    rw [show codeMat 94 = codeMat 266 + codeMat 340 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o17s3Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o17s3SourceU i) (step81o17s3SourceLb i) := by
  fin_cases i <;> simp [step81o17s3SourceU, step81o17s3SourceLb, step81o17s3Seed0, step81o17s3Seed1, step81o17s3Seed2]

theorem step81o17s3Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o17s3Mask i → step81o17s3Sect p ∈ step81o17s3SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o17s3Mask] at h
  · change evalFunc (codeMat 340) (codeMat 2) = 0
    decide
  · change evalFunc (codeMat 266) (codeMat 4) = 0
    decide
  · change evalFunc (codeMat 94) (codeMat 2 + codeMat 4) = 0
    rw [evalFunc_add]
    decide

theorem step81o17s3Label_zero_mem (M : Mat3) : step81o17s3Label M = 0 → M ∈ step81o17s3Wpair :=
  label2_zero_mem_81 (codeMat 266) (codeMat 340) M

theorem step81o17s3Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o17s3Label M = Fin.succ p → M + step81o17s3Sect p ∈ step81o17s3Wpair := by
  exact label2_sect_coset_81 (codeMat 266) (codeMat 340) (codeMat 2) (codeMat 4)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o17s3NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o17s3Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o17s3Pair_false_le_target {r : ℕ} (hrt : r ≤ 12)
    (D : QuotientTensorDecomp step81o17s3Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 12 <
      ∑ i : Fin 3, (1 : ℕ) * step81o17s3SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o17s3Label step81o17s3Sect step81o17s3SourceU
    step81o17s3SourceLb step81o17s3Mask (fun _ : Fin 3 => 1) 1 12
    step81o17s3Wpair_le_sourceU step81o17s3Source_lb step81o17s3Label_zero_mem step81o17s3Label_sect_coset
    step81o17s3Sect_source hZeroCoverage step81o17s3NonzeroCoverage hrt hCert D

theorem step81o17s3Pair_lb : QuotientRankAtLeast step81o17s3Wpair 13 :=
  quotientRankAtLeast_of_contradiction step81o17s3Wpair 13
    (fun r hr D => step81o17s3Pair_false_le_target (by omega) D)

theorem step81o17s3Wspan_le_pair : step81o17s3Wspan ≤ step81o17s3Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 340) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o17s3Span_lb : QuotientRankAtLeast step81o17s3Wspan 13 :=
  quotientRankAtLeast_mono step81o17s3Wspan_le_pair step81o17s3Pair_lb

-- ============================================================================
-- Generated qdim=2 direct occupation consumer: orbit 17, target 13 -> lb 14
-- W_basis=[262, 128, 68, 32, 20, 10, 1]; f=266, g=340; sections=2,4,6
-- ============================================================================

def step81o17s4Wspan : Submodule F2 Mat3 := spanCodes [262, 128, 68, 32, 20, 10, 1]
def step81o17s4Wpair : Submodule F2 Mat3 := kerEvalFunc (codeMat 266) ⊓ kerEvalFunc (codeMat 340)
def step81o17s4Sect : Fin 3 → Mat3 := sect2_81 (codeMat 2) (codeMat 4)
def step81o17s4Label : Mat3 → Fin 4 := label2_81 (codeMat 266) (codeMat 340)

-- source row 0: mask=1 U_basis=[260, 128, 68, 32, 20, 8, 2, 1] L=340 lb=9
def step81o17s4Rows0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s4Cols0 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s4Q0 : Matrix (Fin 9) (Fin 9) F2 := ![![1, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0]]
theorem step81o17s4Seed0 : QuotientRankAtLeast (kerEvalFunc (codeMat 340)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 340) 9 step81o17s4Rows0 step81o17s4Cols0 step81o17s4Q0
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 1: mask=2 U_basis=[258, 128, 64, 32, 16, 10, 4, 1] L=266 lb=9
def step81o17s4Rows1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s4Cols1 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s4Q1 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]
theorem step81o17s4Seed1 : QuotientRankAtLeast (kerEvalFunc (codeMat 266)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 266) 9 step81o17s4Rows1 step81o17s4Cols1 step81o17s4Q1
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

-- source row 2: mask=4 U_basis=[256, 128, 66, 32, 18, 10, 6, 1] L=94 lb=9
def step81o17s4Rows2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s4Cols2 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
def step81o17s4Q2 : Matrix (Fin 9) (Fin 9) F2 := ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1, 0, 0, 1]]
theorem step81o17s4Seed2 : QuotientRankAtLeast (kerEvalFunc (codeMat 94)) 9 :=
  contraction_seed_ker_invertible_minor (codeMat 94) 9 step81o17s4Rows2 step81o17s4Cols2 step81o17s4Q2
    (by ext i j; fin_cases i <;> fin_cases j <;> decide)

def step81o17s4SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 340)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 266)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 94)
def step81o17s4SourceLb : Fin 3 → ℕ
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 9
  | ⟨2, _⟩ => 9
def step81o17s4Mask : Fin 3 → Finset (Fin 3)
  | ⟨0, _⟩ => ({0} : Finset (Fin 3))
  | ⟨1, _⟩ => ({1} : Finset (Fin 3))
  | ⟨2, _⟩ => ({2} : Finset (Fin 3))

theorem step81o17s4Wpair_le_sourceU (i : Fin 3) : step81o17s4Wpair ≤ step81o17s4SourceU i := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340) at hM
  fin_cases i
  · change evalFunc (codeMat 340) M = 0
    exact hM.2
  · change evalFunc (codeMat 266) M = 0
    exact hM.1
  · change evalFunc (codeMat 94) M = 0
    rw [show codeMat 94 = codeMat 266 + codeMat 340 from by ext x y; fin_cases x <;> fin_cases y <;> decide]
    rw [evalFunc_add_left81, hM.1, hM.2, add_zero]

theorem step81o17s4Source_lb (i : Fin 3) : QuotientRankAtLeast (step81o17s4SourceU i) (step81o17s4SourceLb i) := by
  fin_cases i <;> simp [step81o17s4SourceU, step81o17s4SourceLb, step81o17s4Seed0, step81o17s4Seed1, step81o17s4Seed2]

theorem step81o17s4Sect_source (i : Fin 3) (p : Fin 3) : p ∈ step81o17s4Mask i → step81o17s4Sect p ∈ step81o17s4SourceU i := by
  intro h
  fin_cases i <;> fin_cases p <;> simp [step81o17s4Mask] at h
  · change evalFunc (codeMat 340) (codeMat 2) = 0
    decide
  · change evalFunc (codeMat 266) (codeMat 4) = 0
    decide
  · change evalFunc (codeMat 94) (codeMat 2 + codeMat 4) = 0
    rw [evalFunc_add]
    decide

theorem step81o17s4Label_zero_mem (M : Mat3) : step81o17s4Label M = 0 → M ∈ step81o17s4Wpair :=
  label2_zero_mem_81 (codeMat 266) (codeMat 340) M

theorem step81o17s4Label_sect_coset (M : Mat3) (p : Fin 3) :
    step81o17s4Label M = Fin.succ p → M + step81o17s4Sect p ∈ step81o17s4Wpair := by
  exact label2_sect_coset_81 (codeMat 266) (codeMat 340) (codeMat 2) (codeMat 4)
    (by decide) (by decide) (by decide) (by decide) M p

theorem step81o17s4NonzeroCoverage (p : Fin 3) :
    1 ≤ ∑ i : Fin 3, if p ∈ step81o17s4Mask i then (1 : ℕ) else 0 := by
  fin_cases p <;> decide

theorem step81o17s4Pair_false_le_target {r : ℕ} (hrt : r ≤ 13)
    (D : QuotientTensorDecomp step81o17s4Wpair r) : False := by
  have hZeroCoverage : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
  have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 13 <
      ∑ i : Fin 3, (1 : ℕ) * step81o17s4SourceLb i := by decide
  exact weighted_cover_quotient_decomp_false step81o17s4Label step81o17s4Sect step81o17s4SourceU
    step81o17s4SourceLb step81o17s4Mask (fun _ : Fin 3 => 1) 1 13
    step81o17s4Wpair_le_sourceU step81o17s4Source_lb step81o17s4Label_zero_mem step81o17s4Label_sect_coset
    step81o17s4Sect_source hZeroCoverage step81o17s4NonzeroCoverage hrt hCert D

theorem step81o17s4Pair_lb : QuotientRankAtLeast step81o17s4Wpair 14 :=
  quotientRankAtLeast_of_contradiction step81o17s4Wpair 14
    (fun r hr D => step81o17s4Pair_false_le_target (by omega) D)

theorem step81o17s4Wspan_le_pair : step81o17s4Wspan ≤ step81o17s4Wpair := by
  intro M hM
  change M ∈ kerEvalFunc (codeMat 266) ∧ M ∈ kerEvalFunc (codeMat 340)
  exact ⟨(spanCodes_le_kerEvalFunc_of_gens' (codeMat 266) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM,
    (spanCodes_le_kerEvalFunc_of_gens' (codeMat 340) [262, 128, 68, 32, 20, 10, 1] (by intro n hn; fin_cases hn <;> decide)) hM⟩

theorem step81o17s4Span_lb : QuotientRankAtLeast step81o17s4Wspan 14 :=
  quotientRankAtLeast_mono step81o17s4Wspan_le_pair step81o17s4Pair_lb
end QiushiMatmul
