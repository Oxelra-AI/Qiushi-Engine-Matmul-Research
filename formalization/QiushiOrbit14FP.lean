import QiushiGenericDeletion

/-! # Orbit-14 forced-product seed (lb = 12)

Axis: B, k = 6, f = 6, qdim = 2
Perp codes: [20, 96]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 3, 4, 5]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V2_14 := Fin 2 → F2

/-- Orbit-14 annihilator functionals. -/
def orbit14Ls : Fin 2 → Mat3 := ![codeMat 20, codeMat 96]

/-- Orbit-14 coordinate map. -/
def orbit14Pi : Mat3 →ₗ[F2] V2_14 := piOfLs orbit14Ls

/-- Orbit-14 subspace W (kernel of annihilators). -/
def orbit14W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 96, 128, 256]

/-- Orbit-14 canonical slice family. -/
def orbit14S : Coord9 → Coord9 → V2_14 :=
  fun b c => orbit14Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit14Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit14Cols : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- `orbit14Pi` annihilates `orbit14W`. -/
theorem orbit14Pi_kills_W (X : Mat3) (hX : X ∈ orbit14W) :
    orbit14Pi X = 0 :=
  piOfLs_kills_span orbit14Ls [1, 2, 8, 20, 96, 128, 256]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit14_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 2),
        ∑ l : Fin 6, z l * orbit14S (orbit14Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit14_selected_independent :
    SelectedIndependent orbit14S orbit14Sels :=
  selected_independent_of_fin_check orbit14S orbit14Sels
    orbit14_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit14_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 2),
        (∀ l : Fin 6, ∑ j : Fin 6, y j * orbit14S (orbit14Sels l) (orbit14Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit14S b (orbit14Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit14_fold_uniform_witness :
    FoldUniformWitness orbit14S orbit14Sels orbit14Cols :=
  fold_uniform_witness_of_fin_check orbit14S orbit14Sels orbit14Cols
    orbit14_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit14_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit14S r → False :=
  no_short_of_deletions 6 6 orbit14S orbit14Sels orbit14Cols
    orbit14_selected_independent orbit14_fold_uniform_witness

/-- Orbit-14 forced-product bound. -/
theorem orbit14_lb12 : QuotientRankAtLeast orbit14W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit14Pi orbit14Pi_kills_W orbit14_slice_no_short

end QiushiMatmul
