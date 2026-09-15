import QiushiGenericDeletion

/-! # Orbit-41 forced-product seed (lb = 12)

Axis: B, k = 3, f = 9, qdim = 3
Perp codes: [20, 68, 384]
Selected: [0, 1, 2], Columns: [0, 1, 2, 3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_41 := Fin 3 → F2

/-- Orbit-41 annihilator functionals. -/
def orbit41Ls : Fin 3 → Mat3 := ![codeMat 20, codeMat 68, codeMat 384]

/-- Orbit-41 coordinate map. -/
def orbit41Pi : Mat3 →ₗ[F2] V3_41 := piOfLs orbit41Ls

/-- Orbit-41 subspace W (kernel of annihilators). -/
def orbit41W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 32, 84, 384]

/-- Orbit-41 canonical slice family. -/
def orbit41S : Coord9 → Coord9 → V3_41 :=
  fun b c => orbit41Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=3). -/
def orbit41Sels : Fin 3 → Coord9 := ![(0, 0), (0, 1), (0, 2)]

/-- Fold-uniform column coordinates (f=9). -/
def orbit41Cols : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit41Pi` annihilates `orbit41W`. -/
theorem orbit41Pi_kills_W (X : Mat3) (hX : X ∈ orbit41W) :
    orbit41Pi X = 0 :=
  piOfLs_kills_span orbit41Ls [1, 2, 8, 32, 84, 384]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit41_selected_independent_fin :
    ∀ z : Fin 3 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 3, z l * orbit41S (orbit41Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit41_selected_independent :
    SelectedIndependent orbit41S orbit41Sels :=
  selected_independent_of_fin_check orbit41S orbit41Sels
    orbit41_selected_independent_fin

/-- Fold-uniform witness (finite check, 511 nonzero y). -/
theorem orbit41_fold_uniform_witness_fin :
    ∀ y : Fin 9 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 3, ∑ j : Fin 9, y j * orbit41S (orbit41Sels l) (orbit41Cols j) i = 0) ∧
        (∑ j : Fin 9, y j * orbit41S b (orbit41Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit41_fold_uniform_witness :
    FoldUniformWitness orbit41S orbit41Sels orbit41Cols :=
  fold_uniform_witness_of_fin_check orbit41S orbit41Sels orbit41Cols
    orbit41_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit41_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit41S r → False :=
  no_short_of_deletions 3 9 orbit41S orbit41Sels orbit41Cols
    orbit41_selected_independent orbit41_fold_uniform_witness

/-- Orbit-41 forced-product bound. -/
theorem orbit41_lb12 : QuotientRankAtLeast orbit41W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit41Pi orbit41Pi_kills_W orbit41_slice_no_short

end QiushiMatmul
