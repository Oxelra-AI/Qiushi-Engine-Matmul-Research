import QiushiGenericDeletion

/-! # Orbit-35 forced-product seed (lb = 15)

Axis: B, k = 6, f = 9, qdim = 3
Perp codes: [20, 96, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_35 := Fin 3 → F2

/-- Orbit-35 annihilator functionals. -/
def orbit35Ls : Fin 3 → Mat3 := ![codeMat 20, codeMat 96, codeMat 256]

/-- Orbit-35 coordinate map. -/
def orbit35Pi : Mat3 →ₗ[F2] V3_35 := piOfLs orbit35Ls

/-- Orbit-35 subspace W (kernel of annihilators). -/
def orbit35W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 96, 128]

/-- Orbit-35 canonical slice family. -/
def orbit35S : Coord9 → Coord9 → V3_35 :=
  fun b c => orbit35Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit35Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=9). -/
def orbit35Cols : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit35Pi` annihilates `orbit35W`. -/
theorem orbit35Pi_kills_W (X : Mat3) (hX : X ∈ orbit35W) :
    orbit35Pi X = 0 :=
  piOfLs_kills_span orbit35Ls [1, 2, 8, 20, 96, 128]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit35_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 6, z l * orbit35S (orbit35Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit35_selected_independent :
    SelectedIndependent orbit35S orbit35Sels :=
  selected_independent_of_fin_check orbit35S orbit35Sels
    orbit35_selected_independent_fin

private def orbit35Index (i k : Fin 3) : Fin 9 :=
  ⟨3 * i.val + k.val, by omega⟩

private theorem orbit35_tail_coeff : ∀ (k i : Fin 3) (j : Fin 9),
    orbit35S (2, k) (orbit35Cols j) i =
      if j = orbit35Index i k then 1 else 0 := by
  decide +kernel

private theorem orbit35_selected_coeff0 : ∀ (l : Fin 6) (j : Fin 9),
    orbit35S (orbit35Sels l) (orbit35Cols j) 0 =
      if 3 ≤ l.val ∧ j.val = l.val then 1 else 0 := by
  decide +kernel

private theorem orbit35_selected_coeff1 : ∀ (l : Fin 6) (j : Fin 9),
    orbit35S (orbit35Sels l) (orbit35Cols j) 1 =
      if l.val < 3 ∧ j.val = 6 + l.val then 1 else 0 := by
  decide +kernel

private theorem orbit35_selected_coeff2 : ∀ (l : Fin 6) (j : Fin 9),
    orbit35S (orbit35Sels l) (orbit35Cols j) 2 = 0 := by
  decide +kernel

private theorem orbit35_tail_eval (y : Fin 9 → F2) (i k : Fin 3) :
    (∑ j : Fin 9, y j * orbit35S (2, k) (orbit35Cols j) i) =
      y (orbit35Index i k) := by
  simp_rw [orbit35_tail_coeff]
  simp

private theorem orbit35_selected_zero0 (y : Fin 9 → F2)
    (h : ∀ k : Fin 3, y (orbit35Index 1 k) = 0) (l : Fin 6) :
    (∑ j : Fin 9, y j * orbit35S (orbit35Sels l) (orbit35Cols j) 0) = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [orbit35Index] at h0 h1 h2
  simp_rw [orbit35_selected_coeff0]
  fin_cases l <;> norm_num [Fin.sum_univ_succ, h0, h1, h2]
  all_goals first | exact h0 | exact h1 | exact h2

private theorem orbit35_selected_zero1 (y : Fin 9 → F2)
    (h : ∀ k : Fin 3, y (orbit35Index 2 k) = 0) (l : Fin 6) :
    (∑ j : Fin 9, y j * orbit35S (orbit35Sels l) (orbit35Cols j) 1) = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [orbit35Index] at h0 h1 h2
  simp_rw [orbit35_selected_coeff1]
  fin_cases l <;> norm_num [Fin.sum_univ_succ, h0, h1, h2]
  all_goals first | exact h0 | exact h1 | exact h2

/-- Choose a nonzero coordinate in the last nonzero row of `y`.
Its functional annihilates the six selected slices. -/
theorem orbit35_fold_uniform_witness_fin :
    ∀ y : Fin 9 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 6, ∑ j : Fin 9, y j * orbit35S (orbit35Sels l) (orbit35Cols j) i = 0) ∧
        (∑ j : Fin 9, y j * orbit35S b (orbit35Cols j) i ≠ 0) := by
  intro y hy
  by_cases h2 : ∀ k : Fin 3, y (orbit35Index 2 k) = 0
  · by_cases h1 : ∀ k : Fin 3, y (orbit35Index 1 k) = 0
    · have h0 : ¬ ∀ k : Fin 3, y (orbit35Index 0 k) = 0 := by
        intro h0
        apply hy
        funext j
        fin_cases j <;> first
          | exact h0 0 | exact h0 1 | exact h0 2
          | exact h1 0 | exact h1 1 | exact h1 2
          | exact h2 0 | exact h2 1 | exact h2 2
      obtain ⟨k, hk⟩ := not_forall.mp h0
      exact ⟨(2, k), 0, orbit35_selected_zero0 y h1,
        by simpa only [orbit35_tail_eval] using hk⟩
    · obtain ⟨k, hk⟩ := not_forall.mp h1
      exact ⟨(2, k), 1, orbit35_selected_zero1 y h2,
        by simpa only [orbit35_tail_eval] using hk⟩
  · obtain ⟨k, hk⟩ := not_forall.mp h2
    refine ⟨(2, k), 2, ?_, by simpa only [orbit35_tail_eval] using hk⟩
    intro l
    simp_rw [orbit35_selected_coeff2]
    simp

/-- Fold-uniform witness condition. -/
theorem orbit35_fold_uniform_witness :
    FoldUniformWitness orbit35S orbit35Sels orbit35Cols :=
  fold_uniform_witness_of_fin_check orbit35S orbit35Sels orbit35Cols
    orbit35_fold_uniform_witness_fin

/-- No decomposition shorter than 15. -/
theorem orbit35_slice_no_short :
    ∀ r, r < 15 → BSliceFamilyDecomp orbit35S r → False :=
  no_short_of_deletions 6 9 orbit35S orbit35Sels orbit35Cols
    orbit35_selected_independent orbit35_fold_uniform_witness

/-- Orbit-35 forced-product bound. -/
theorem orbit35_lb15 : QuotientRankAtLeast orbit35W 15 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit35Pi orbit35Pi_kills_W orbit35_slice_no_short

end QiushiMatmul
