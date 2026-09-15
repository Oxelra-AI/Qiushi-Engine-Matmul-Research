import QiushiGenericDeletion

/-! # Orbit-23 forced-product seed (lb = 12)

Axis: B, k = 6, f = 6, qdim = 3
Perp codes: [32, 80, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_23 := Fin 3 → F2

/-- Orbit-23 annihilator functionals. -/
def orbit23Ls : Fin 3 → Mat3 := ![codeMat 32, codeMat 80, codeMat 256]

/-- Orbit-23 coordinate map. -/
def orbit23Pi : Mat3 →ₗ[F2] V3_23 := piOfLs orbit23Ls

/-- Orbit-23 subspace W (kernel of annihilators). -/
def orbit23W : Submodule F2 Mat3 := spanCodes [1, 2, 4, 8, 80, 128]

/-- Orbit-23 canonical slice family. -/
def orbit23S : Coord9 → Coord9 → V3_23 :=
  fun b c => orbit23Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit23Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit23Cols : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit23Pi` annihilates `orbit23W`. -/
theorem orbit23Pi_kills_W (X : Mat3) (hX : X ∈ orbit23W) :
    orbit23Pi X = 0 :=
  piOfLs_kills_span orbit23Ls [1, 2, 4, 8, 80, 128]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit23_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 6, z l * orbit23S (orbit23Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit23_selected_independent :
    SelectedIndependent orbit23S orbit23Sels :=
  selected_independent_of_fin_check orbit23S orbit23Sels
    orbit23_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit23_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 6, ∑ j : Fin 6, y j * orbit23S (orbit23Sels l) (orbit23Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit23S b (orbit23Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit23_fold_uniform_witness :
    FoldUniformWitness orbit23S orbit23Sels orbit23Cols :=
  fold_uniform_witness_of_fin_check orbit23S orbit23Sels orbit23Cols
    orbit23_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit23_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit23S r → False :=
  no_short_of_deletions 6 6 orbit23S orbit23Sels orbit23Cols
    orbit23_selected_independent orbit23_fold_uniform_witness

/-- Orbit-23 forced-product bound. -/
theorem orbit23_lb12 : QuotientRankAtLeast orbit23W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit23Pi orbit23Pi_kills_W orbit23_slice_no_short

end QiushiMatmul
