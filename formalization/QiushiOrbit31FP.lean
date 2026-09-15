import QiushiGenericDeletion

/-! # Orbit-31 forced-product seed (lb = 15)

Axis: C (swapped), k = 6, f = 9, qdim = 3
Perp codes: [84, 128, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_31 := Fin 3 → F2

/-- Orbit-31 annihilator functionals. -/
def orbit31Ls : Fin 3 → Mat3 := ![codeMat 84, codeMat 128, codeMat 256]

/-- Orbit-31 coordinate map. -/
def orbit31Pi : Mat3 →ₗ[F2] V3_31 := piOfLs orbit31Ls

/-- Orbit-31 subspace W (kernel of annihilators). -/
def orbit31W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 32, 68]

/-- Orbit-31 canonical slice family (C-axis: swapped). -/
def orbit31S : Coord9 → Coord9 → V3_31 :=
  fun b c => orbit31Pi (tensorASlice c b)

/-- Selected deletion coordinates (k=6). -/
def orbit31Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=9). -/
def orbit31Cols : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit31Pi` annihilates `orbit31W`. -/
theorem orbit31Pi_kills_W (X : Mat3) (hX : X ∈ orbit31W) :
    orbit31Pi X = 0 :=
  piOfLs_kills_span orbit31Ls [1, 2, 8, 20, 32, 68]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit31_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 6, z l * orbit31S (orbit31Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit31_selected_independent :
    SelectedIndependent orbit31S orbit31Sels :=
  selected_independent_of_fin_check orbit31S orbit31Sels
    orbit31_selected_independent_fin

/-- Fold-uniform witness (finite check, 511 nonzero y). -/
theorem orbit31_fold_uniform_witness_fin :
    ∀ y : Fin 9 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 6, ∑ j : Fin 9, y j * orbit31S (orbit31Sels l) (orbit31Cols j) i = 0) ∧
        (∑ j : Fin 9, y j * orbit31S b (orbit31Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit31_fold_uniform_witness :
    FoldUniformWitness orbit31S orbit31Sels orbit31Cols :=
  fold_uniform_witness_of_fin_check orbit31S orbit31Sels orbit31Cols
    orbit31_fold_uniform_witness_fin

/-- No decomposition shorter than 15. -/
theorem orbit31_slice_no_short :
    ∀ r, r < 15 → BSliceFamilyDecomp orbit31S r → False :=
  no_short_of_deletions 6 9 orbit31S orbit31Sels orbit31Cols
    orbit31_selected_independent orbit31_fold_uniform_witness

/-- Orbit-31 forced-product bound (C-axis). -/
theorem orbit31_lb15 : QuotientRankAtLeast orbit31W 15 :=
  quotientRankAtLeast_of_swapped_sliceFamily_no_short
    orbit31Pi orbit31Pi_kills_W orbit31_slice_no_short

end QiushiMatmul
