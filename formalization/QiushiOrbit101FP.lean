import QiushiGenericDeletion

/-! # Orbit-101 forced-product seed (lb = 15)

Axis: C (swapped), k = 6, f = 9, qdim = 4
Perp codes: [20, 68, 128, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V4_101 := Fin 4 → F2

/-- Orbit-101 annihilator functionals. -/
def orbit101Ls : Fin 4 → Mat3 := ![codeMat 20, codeMat 68, codeMat 128, codeMat 256]

/-- Orbit-101 coordinate map. -/
def orbit101Pi : Mat3 →ₗ[F2] V4_101 := piOfLs orbit101Ls

/-- Orbit-101 subspace W (kernel of annihilators). -/
def orbit101W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 32, 84]

/-- Orbit-101 canonical slice family (C-axis: swapped). -/
def orbit101S : Coord9 → Coord9 → V4_101 :=
  fun b c => orbit101Pi (tensorASlice c b)

/-- Selected deletion coordinates (k=6). -/
def orbit101Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=9). -/
def orbit101Cols : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit101Pi` annihilates `orbit101W`. -/
theorem orbit101Pi_kills_W (X : Mat3) (hX : X ∈ orbit101W) :
    orbit101Pi X = 0 :=
  piOfLs_kills_span orbit101Ls [1, 2, 8, 32, 84]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit101_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 4),
        ∑ l : Fin 6, z l * orbit101S (orbit101Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit101_selected_independent :
    SelectedIndependent orbit101S orbit101Sels :=
  selected_independent_of_fin_check orbit101S orbit101Sels
    orbit101_selected_independent_fin

private def orbit101Index (i k : Fin 3) : Fin 9 :=
  ⟨3 * i.val + k.val, by omega⟩

private theorem orbit101_tail_coeff : ∀ (k i : Fin 3) (j : Fin 9),
    orbit101S (2, k) (orbit101Cols j) i.succ =
      if j = orbit101Index i k then 1 else 0 := by
  decide +kernel

private theorem orbit101_selected_coeff1 : ∀ (l : Fin 6) (j : Fin 9),
    orbit101S (orbit101Sels l) (orbit101Cols j) 1 =
      if l.val < 3 ∧ j.val = 6 + l.val then 1 else 0 := by
  decide +kernel

private theorem orbit101_selected_coeff2 : ∀ (l : Fin 6) (j : Fin 9),
    orbit101S (orbit101Sels l) (orbit101Cols j) 2 = 0 := by
  decide +kernel

private theorem orbit101_selected_coeff3 : ∀ (l : Fin 6) (j : Fin 9),
    orbit101S (orbit101Sels l) (orbit101Cols j) 3 = 0 := by
  decide +kernel

private theorem orbit101_tail_eval (y : Fin 9 → F2) (i k : Fin 3) :
    (∑ j : Fin 9, y j * orbit101S (2, k) (orbit101Cols j) i.succ) =
      y (orbit101Index i k) := by
  simp_rw [orbit101_tail_coeff]
  simp

private theorem orbit101_selected_zero1 (y : Fin 9 → F2)
    (h : ∀ k : Fin 3, y (orbit101Index 2 k) = 0) (l : Fin 6) :
    (∑ j : Fin 9, y j * orbit101S (orbit101Sels l) (orbit101Cols j) 1) = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [orbit101Index] at h0 h1 h2
  simp_rw [orbit101_selected_coeff1]
  fin_cases l <;> norm_num [Fin.sum_univ_succ, h0, h1, h2]
  all_goals first | exact h0 | exact h1 | exact h2

/-- Choose a coordinate in the last nonzero row of `y`; its tail functional
annihilates all six selected slices. -/
theorem orbit101_fold_uniform_witness_fin :
    ∀ y : Fin 9 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 4),
        (∀ l : Fin 6, ∑ j : Fin 9, y j * orbit101S (orbit101Sels l) (orbit101Cols j) i = 0) ∧
        (∑ j : Fin 9, y j * orbit101S b (orbit101Cols j) i ≠ 0) := by
  intro y hy
  by_cases h2 : ∀ k : Fin 3, y (orbit101Index 2 k) = 0
  · by_cases h1 : ∀ k : Fin 3, y (orbit101Index 1 k) = 0
    · have h0 : ¬ ∀ k : Fin 3, y (orbit101Index 0 k) = 0 := by
        intro h0
        apply hy
        funext j
        fin_cases j <;> first
          | exact h0 0 | exact h0 1 | exact h0 2
          | exact h1 0 | exact h1 1 | exact h1 2
          | exact h2 0 | exact h2 1 | exact h2 2
      obtain ⟨k, hk⟩ := not_forall.mp h0
      exact ⟨(2, k), 1, orbit101_selected_zero1 y h2,
        by
          rw [← show (0 : Fin 3).succ = (1 : Fin 4) by decide, orbit101_tail_eval]
          exact hk⟩
    · obtain ⟨k, hk⟩ := not_forall.mp h1
      refine ⟨(2, k), 2, ?_, ?_⟩
      · intro l
        simp_rw [orbit101_selected_coeff2]
        simp
      · rw [← show (1 : Fin 3).succ = (2 : Fin 4) by decide, orbit101_tail_eval]
        exact hk
  · obtain ⟨k, hk⟩ := not_forall.mp h2
    refine ⟨(2, k), 3, ?_, ?_⟩
    · intro l
      simp_rw [orbit101_selected_coeff3]
      simp
    · rw [← show (2 : Fin 3).succ = (3 : Fin 4) by decide, orbit101_tail_eval]
      exact hk

/-- Fold-uniform witness condition. -/
theorem orbit101_fold_uniform_witness :
    FoldUniformWitness orbit101S orbit101Sels orbit101Cols :=
  fold_uniform_witness_of_fin_check orbit101S orbit101Sels orbit101Cols
    orbit101_fold_uniform_witness_fin

/-- No decomposition shorter than 15. -/
theorem orbit101_slice_no_short :
    ∀ r, r < 15 → BSliceFamilyDecomp orbit101S r → False :=
  no_short_of_deletions 6 9 orbit101S orbit101Sels orbit101Cols
    orbit101_selected_independent orbit101_fold_uniform_witness

/-- Orbit-101 forced-product bound (C-axis). -/
theorem orbit101_lb15 : QuotientRankAtLeast orbit101W 15 :=
  quotientRankAtLeast_of_swapped_sliceFamily_no_short
    orbit101Pi orbit101Pi_kills_W orbit101_slice_no_short

end QiushiMatmul
