import QiushiGenericDeletion

/-! # Orbit-5 forced-product seed (lb = 9)

Axis: B, k = 3, f = 6, qdim = 2
Perp codes: [160, 256]
Selected: [3, 4, 5], Columns: [3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V2_5 := Fin 2 → F2

/-- Orbit-5 annihilator functionals. -/
def orbit5Ls : Fin 2 → Mat3 := ![codeMat 160, codeMat 256]

/-- Orbit-5 coordinate map. -/
def orbit5Pi : Mat3 →ₗ[F2] V2_5 := piOfLs orbit5Ls

/-- Orbit-5 subspace W (kernel of annihilators). -/
def orbit5W : Submodule F2 Mat3 := spanCodes [1, 2, 4, 8, 16, 64, 160]

/-- Orbit-5 canonical slice family. -/
def orbit5S : Coord9 → Coord9 → V2_5 :=
  fun b c => orbit5Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=3). -/
def orbit5Sels : Fin 3 → Coord9 := ![(1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit5Cols : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit5Pi` annihilates `orbit5W`. -/
theorem orbit5Pi_kills_W (X : Mat3) (hX : X ∈ orbit5W) :
    orbit5Pi X = 0 :=
  piOfLs_kills_span orbit5Ls [1, 2, 4, 8, 16, 64, 160]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit5_selected_independent_fin :
    ∀ z : Fin 3 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 2),
        ∑ l : Fin 3, z l * orbit5S (orbit5Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit5_selected_independent :
    SelectedIndependent orbit5S orbit5Sels :=
  selected_independent_of_fin_check orbit5S orbit5Sels
    orbit5_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit5_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 2),
        (∀ l : Fin 3, ∑ j : Fin 6, y j * orbit5S (orbit5Sels l) (orbit5Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit5S b (orbit5Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit5_fold_uniform_witness :
    FoldUniformWitness orbit5S orbit5Sels orbit5Cols :=
  fold_uniform_witness_of_fin_check orbit5S orbit5Sels orbit5Cols
    orbit5_fold_uniform_witness_fin

/-- No decomposition shorter than 9. -/
theorem orbit5_slice_no_short :
    ∀ r, r < 9 → BSliceFamilyDecomp orbit5S r → False :=
  no_short_of_deletions 3 6 orbit5S orbit5Sels orbit5Cols
    orbit5_selected_independent orbit5_fold_uniform_witness

/-- Orbit-5 forced-product bound. -/
theorem orbit5_lb9 : QuotientRankAtLeast orbit5W 9 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit5Pi orbit5Pi_kills_W orbit5_slice_no_short

end QiushiMatmul
