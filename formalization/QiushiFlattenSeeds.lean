import QiushiContractionSeed

/-!
# All 13 flatten seed QuotientRankAtLeast theorems

Uses multi-functional contraction with identity minors in BC or CB orientation.
Correct convention: `contractionVal(L,b,c) = L(c.1, b.1) * δ(c.2, b.2)`.
-/

set_option maxHeartbeats 32000000
open BigOperators Finset Matrix
namespace QiushiMatmul

theorem spanCodes_le_kerEvalFunc_of_gens' (L : Mat3) (basis : List ℕ)
    (hGens : ∀ n ∈ basis, evalFunc L (codeMat n) = 0)
    : spanCodes basis ≤ kerEvalFunc L := by
  intro M hM
  change evalFunc L M = 0
  refine Submodule.span_induction (p := fun x _ => evalFunc L x = 0) ?_ ?_ ?_ ?_ hM
  · intro x hx; rcases hx with ⟨n, hn, rfl⟩; exact hGens n hn
  · exact evalFunc_zero L
  · intro x y _ _ hx hy; rw [evalFunc_add, hx, hy, add_zero]
  · intro a x _ hx; rw [evalFunc_smul, hx, mul_zero]


-- ============================================================================
-- Orbit 1 : dim=8, lb=3, BC orientation
-- ============================================================================

def flatW_1 : Submodule F2 Mat3 := spanCodes [128, 64, 32, 16, 8, 4, 2, 1]
def flatLs_1 : Fin 1 → Mat3 := ![codeMat 256]
def flatRows_1 : Fin 3 → Fin 1 × Coord9 := ![⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩]  -- (s, b)
def flatCols_1 : Fin 3 → Coord9 := ![(2, 0), (2, 1), (2, 2)]  -- c coords

theorem flatContain_1 : ∀ s : Fin 1, flatW_1 ≤ kerEvalFunc (flatLs_1 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_1 : multiContractionMinor flatLs_1 flatRows_1 flatCols_1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_1 : QuotientRankAtLeast flatW_1 3 :=
  multi_contraction_seed_of_le_kernels flatW_1 flatLs_1 flatContain_1
    flatRows_1 flatCols_1 1 (by rw [Matrix.one_mul]; exact flatMinor_1)


-- ============================================================================
-- Orbit 2 : dim=8, lb=6, BC orientation
-- ============================================================================

def flatW_2 : Submodule F2 Mat3 := spanCodes [256, 160, 64, 16, 8, 4, 2, 1]
def flatLs_2 : Fin 1 → Mat3 := ![codeMat 160]
def flatRows_2 : Fin 6 → Fin 1 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩]  -- (s, b)
def flatCols_2 : Fin 6 → Coord9 := ![(2, 0), (2, 1), (2, 2), (1, 0), (1, 1), (1, 2)]  -- c coords

theorem flatContain_2 : ∀ s : Fin 1, flatW_2 ≤ kerEvalFunc (flatLs_2 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_2 : multiContractionMinor flatLs_2 flatRows_2 flatCols_2 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_2 : QuotientRankAtLeast flatW_2 6 :=
  multi_contraction_seed_of_le_kernels flatW_2 flatLs_2 flatContain_2
    flatRows_2 flatCols_2 1 (by rw [Matrix.one_mul]; exact flatMinor_2)


-- ============================================================================
-- Orbit 3 : dim=8, lb=9, BC orientation
-- ============================================================================

def flatW_3 : Submodule F2 Mat3 := spanCodes [256, 128, 68, 32, 20, 8, 2, 1]
def flatLs_3 : Fin 1 → Mat3 := ![codeMat 84]
def flatRows_3 : Fin 9 → Fin 1 × Coord9 := ![⟨0, (0, 0)⟩, ⟨0, (0, 1)⟩, ⟨0, (0, 2)⟩, ⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩]  -- (s, b)
def flatCols_3 : Fin 9 → Coord9 := ![(2, 0), (2, 1), (2, 2), (1, 0), (1, 1), (1, 2), (0, 0), (0, 1), (0, 2)]  -- c coords

theorem flatContain_3 : ∀ s : Fin 1, flatW_3 ≤ kerEvalFunc (flatLs_3 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_3 : multiContractionMinor flatLs_3 flatRows_3 flatCols_3 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_3 : QuotientRankAtLeast flatW_3 9 :=
  multi_contraction_seed_of_le_kernels flatW_3 flatLs_3 flatContain_3
    flatRows_3 flatCols_3 1 (by rw [Matrix.one_mul]; exact flatMinor_3)


-- ============================================================================
-- Orbit 4 : dim=7, lb=6, CB orientation
-- ============================================================================

def flatW_4 : Submodule F2 Mat3 := spanCodes [64, 32, 16, 8, 4, 2, 1]
def flatLs_4 : Fin 2 → Mat3 := ![codeMat 128, codeMat 256]
def flatRows_4 : Fin 6 → Fin 2 × Coord9 := ![⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (2, 0)⟩, ⟨1, (2, 1)⟩, ⟨1, (2, 2)⟩]  -- (s, c)
def flatCols_4 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]  -- b coords

theorem flatContain_4 : ∀ s : Fin 2, flatW_4 ≤ kerEvalFunc (flatLs_4 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_4 : multiContractionMinorCB flatLs_4 flatRows_4 flatCols_4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_4 : QuotientRankAtLeast flatW_4 6 :=
  multi_contraction_seed_CB_of_le_kernels flatW_4 flatLs_4 flatContain_4
    flatRows_4 flatCols_4 1 (by rw [Matrix.one_mul]; exact flatMinor_4)


-- ============================================================================
-- Orbit 6 : dim=7, lb=6, BC orientation
-- ============================================================================

def flatW_6 : Submodule F2 Mat3 := spanCodes [256, 64, 16, 8, 4, 2, 1]
def flatLs_6 : Fin 2 → Mat3 := ![codeMat 32, codeMat 128]
def flatRows_6 : Fin 6 → Fin 2 × Coord9 := ![⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (1, 0)⟩, ⟨1, (1, 1)⟩, ⟨1, (1, 2)⟩]  -- (s, b)
def flatCols_6 : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]  -- c coords

theorem flatContain_6 : ∀ s : Fin 2, flatW_6 ≤ kerEvalFunc (flatLs_6 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_6 : multiContractionMinor flatLs_6 flatRows_6 flatCols_6 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_6 : QuotientRankAtLeast flatW_6 6 :=
  multi_contraction_seed_of_le_kernels flatW_6 flatLs_6 flatContain_6
    flatRows_6 flatCols_6 1 (by rw [Matrix.one_mul]; exact flatMinor_6)


-- ============================================================================
-- Orbit 7 : dim=7, lb=9, CB orientation
-- ============================================================================

def flatW_7 : Submodule F2 Mat3 := spanCodes [256, 96, 16, 8, 4, 2, 1]
def flatLs_7 : Fin 2 → Mat3 := ![codeMat 96, codeMat 128]
def flatRows_7 : Fin 9 → Fin 2 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (2, 0)⟩, ⟨1, (2, 1)⟩, ⟨1, (2, 2)⟩]  -- (s, c)
def flatCols_7 : Fin 9 → Coord9 := ![(2, 0), (2, 1), (2, 2), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]  -- b coords

theorem flatContain_7 : ∀ s : Fin 2, flatW_7 ≤ kerEvalFunc (flatLs_7 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_7 : multiContractionMinorCB flatLs_7 flatRows_7 flatCols_7 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_7 : QuotientRankAtLeast flatW_7 9 :=
  multi_contraction_seed_CB_of_le_kernels flatW_7 flatLs_7 flatContain_7
    flatRows_7 flatCols_7 1 (by rw [Matrix.one_mul]; exact flatMinor_7)


-- ============================================================================
-- Orbit 9 : dim=7, lb=9, CB orientation
-- ============================================================================

def flatW_9 : Submodule F2 Mat3 := spanCodes [256, 160, 80, 8, 4, 2, 1]
def flatLs_9 : Fin 2 → Mat3 := ![codeMat 80, codeMat 160]
def flatRows_9 : Fin 9 → Fin 2 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (1, 0)⟩, ⟨1, (1, 1)⟩, ⟨1, (1, 2)⟩]  -- (s, c)
def flatCols_9 : Fin 9 → Coord9 := ![(1, 0), (1, 1), (1, 2), (0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]  -- b coords

theorem flatContain_9 : ∀ s : Fin 2, flatW_9 ≤ kerEvalFunc (flatLs_9 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_9 : multiContractionMinorCB flatLs_9 flatRows_9 flatCols_9 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_9 : QuotientRankAtLeast flatW_9 9 :=
  multi_contraction_seed_CB_of_le_kernels flatW_9 flatLs_9 flatContain_9
    flatRows_9 flatCols_9 1 (by rw [Matrix.one_mul]; exact flatMinor_9)


-- ============================================================================
-- Orbit 12 : dim=7, lb=9, BC orientation
-- ============================================================================

def flatW_12 : Submodule F2 Mat3 := spanCodes [256, 128, 32, 20, 8, 2, 1]
def flatLs_12 : Fin 2 → Mat3 := ![codeMat 20, codeMat 64]
def flatRows_12 : Fin 9 → Fin 2 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (0, 0)⟩, ⟨1, (0, 1)⟩, ⟨1, (0, 2)⟩]  -- (s, b)
def flatCols_12 : Fin 9 → Coord9 := ![(1, 0), (1, 1), (1, 2), (0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]  -- c coords

theorem flatContain_12 : ∀ s : Fin 2, flatW_12 ≤ kerEvalFunc (flatLs_12 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_12 : multiContractionMinor flatLs_12 flatRows_12 flatCols_12 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_12 : QuotientRankAtLeast flatW_12 9 :=
  multi_contraction_seed_of_le_kernels flatW_12 flatLs_12 flatContain_12
    flatRows_12 flatCols_12 1 (by rw [Matrix.one_mul]; exact flatMinor_12)


-- ============================================================================
-- Orbit 15 : dim=7, lb=9, BC orientation
-- ============================================================================

def flatW_15 : Submodule F2 Mat3 := spanCodes [256, 128, 84, 32, 8, 2, 1]
def flatLs_15 : Fin 2 → Mat3 := ![codeMat 20, codeMat 68]
def flatRows_15 : Fin 9 → Fin 2 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (0, 0)⟩, ⟨1, (0, 1)⟩, ⟨1, (0, 2)⟩]  -- (s, b)
def flatCols_15 : Fin 9 → Coord9 := ![(1, 0), (1, 1), (1, 2), (0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]  -- c coords

theorem flatContain_15 : ∀ s : Fin 2, flatW_15 ≤ kerEvalFunc (flatLs_15 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_15 : multiContractionMinor flatLs_15 flatRows_15 flatCols_15 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_15 : QuotientRankAtLeast flatW_15 9 :=
  multi_contraction_seed_of_le_kernels flatW_15 flatLs_15 flatContain_15
    flatRows_15 flatCols_15 1 (by rw [Matrix.one_mul]; exact flatMinor_15)


-- ============================================================================
-- Orbit 18 : dim=6, lb=9, CB orientation
-- ============================================================================

def flatW_18 : Submodule F2 Mat3 := spanCodes [32, 16, 8, 4, 2, 1]
def flatLs_18 : Fin 3 → Mat3 := ![codeMat 64, codeMat 128, codeMat 256]
def flatRows_18 : Fin 9 → Fin 3 × Coord9 := ![⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (2, 0)⟩, ⟨1, (2, 1)⟩, ⟨1, (2, 2)⟩, ⟨2, (2, 0)⟩, ⟨2, (2, 1)⟩, ⟨2, (2, 2)⟩]  -- (s, c)
def flatCols_18 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]  -- b coords

theorem flatContain_18 : ∀ s : Fin 3, flatW_18 ≤ kerEvalFunc (flatLs_18 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_18 : multiContractionMinorCB flatLs_18 flatRows_18 flatCols_18 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_18 : QuotientRankAtLeast flatW_18 9 :=
  multi_contraction_seed_CB_of_le_kernels flatW_18 flatLs_18 flatContain_18
    flatRows_18 flatCols_18 1 (by rw [Matrix.one_mul]; exact flatMinor_18)


-- ============================================================================
-- Orbit 21 : dim=6, lb=9, CB orientation
-- ============================================================================

def flatW_21 : Submodule F2 Mat3 := spanCodes [256, 16, 8, 4, 2, 1]
def flatLs_21 : Fin 3 → Mat3 := ![codeMat 32, codeMat 64, codeMat 128]
def flatRows_21 : Fin 9 → Fin 3 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨1, (2, 0)⟩, ⟨1, (2, 1)⟩, ⟨1, (2, 2)⟩, ⟨2, (2, 0)⟩, ⟨2, (2, 1)⟩, ⟨2, (2, 2)⟩]  -- (s, c)
def flatCols_21 : Fin 9 → Coord9 := ![(2, 0), (2, 1), (2, 2), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]  -- b coords

theorem flatContain_21 : ∀ s : Fin 3, flatW_21 ≤ kerEvalFunc (flatLs_21 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_21 : multiContractionMinorCB flatLs_21 flatRows_21 flatCols_21 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_21 : QuotientRankAtLeast flatW_21 9 :=
  multi_contraction_seed_CB_of_le_kernels flatW_21 flatLs_21 flatContain_21
    flatRows_21 flatCols_21 1 (by rw [Matrix.one_mul]; exact flatMinor_21)


-- ============================================================================
-- Orbit 26 : dim=6, lb=9, CB orientation
-- ============================================================================

def flatW_26 : Submodule F2 Mat3 := spanCodes [288, 128, 8, 4, 2, 1]
def flatLs_26 : Fin 3 → Mat3 := ![codeMat 16, codeMat 64, codeMat 288]
def flatRows_26 : Fin 9 → Fin 3 × Coord9 := ![⟨0, (1, 0)⟩, ⟨0, (1, 1)⟩, ⟨0, (1, 2)⟩, ⟨1, (2, 0)⟩, ⟨1, (2, 1)⟩, ⟨1, (2, 2)⟩, ⟨2, (1, 0)⟩, ⟨2, (1, 1)⟩, ⟨2, (1, 2)⟩]  -- (s, c)
def flatCols_26 : Fin 9 → Coord9 := ![(1, 0), (1, 1), (1, 2), (0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]  -- b coords

theorem flatContain_26 : ∀ s : Fin 3, flatW_26 ≤ kerEvalFunc (flatLs_26 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_26 : multiContractionMinorCB flatLs_26 flatRows_26 flatCols_26 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_26 : QuotientRankAtLeast flatW_26 9 :=
  multi_contraction_seed_CB_of_le_kernels flatW_26 flatLs_26 flatContain_26
    flatRows_26 flatCols_26 1 (by rw [Matrix.one_mul]; exact flatMinor_26)


-- ============================================================================
-- Orbit 42 : dim=6, lb=9, BC orientation
-- ============================================================================

def flatW_42 : Submodule F2 Mat3 := spanCodes [256, 128, 32, 8, 2, 1]
def flatLs_42 : Fin 3 → Mat3 := ![codeMat 4, codeMat 16, codeMat 64]
def flatRows_42 : Fin 9 → Fin 3 × Coord9 := ![⟨0, (2, 0)⟩, ⟨0, (2, 1)⟩, ⟨0, (2, 2)⟩, ⟨1, (1, 0)⟩, ⟨1, (1, 1)⟩, ⟨1, (1, 2)⟩, ⟨2, (0, 0)⟩, ⟨2, (0, 1)⟩, ⟨2, (0, 2)⟩]  -- (s, b)
def flatCols_42 : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]  -- c coords

theorem flatContain_42 : ∀ s : Fin 3, flatW_42 ≤ kerEvalFunc (flatLs_42 s) := by
  intro s; apply spanCodes_le_kerEvalFunc_of_gens'
  intro n hn; fin_cases s <;> fin_cases hn <;> decide

theorem flatMinor_42 : multiContractionMinor flatLs_42 flatRows_42 flatCols_42 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

theorem flatSeed_42 : QuotientRankAtLeast flatW_42 9 :=
  multi_contraction_seed_of_le_kernels flatW_42 flatLs_42 flatContain_42
    flatRows_42 flatCols_42 1 (by rw [Matrix.one_mul]; exact flatMinor_42)

end QiushiMatmul