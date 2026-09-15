import QiushiGenericDeletion

/-! # Orbit-10 forced-product seed (lb = 12)

Axis: B, k = 6, f = 6, qdim = 2
Perp codes: [68, 160]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 3, 4, 5]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V2_10 := Fin 2 → F2

/-- Orbit-10 annihilator functionals. -/
def orbit10Ls : Fin 2 → Mat3 := ![codeMat 68, codeMat 160]

/-- Orbit-10 coordinate map. -/
def orbit10Pi : Mat3 →ₗ[F2] V2_10 := piOfLs orbit10Ls

/-- Orbit-10 subspace W (kernel of annihilators). -/
def orbit10W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 16, 68, 160, 256]

/-- Orbit-10 canonical slice family. -/
def orbit10S : Coord9 → Coord9 → V2_10 :=
  fun b c => orbit10Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit10Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit10Cols : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- `orbit10Pi` annihilates `orbit10W`. -/
theorem orbit10Pi_kills_W (X : Mat3) (hX : X ∈ orbit10W) :
    orbit10Pi X = 0 :=
  piOfLs_kills_span orbit10Ls [1, 2, 8, 16, 68, 160, 256]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit10_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 2),
        ∑ l : Fin 6, z l * orbit10S (orbit10Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit10_selected_independent :
    SelectedIndependent orbit10S orbit10Sels :=
  selected_independent_of_fin_check orbit10S orbit10Sels
    orbit10_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit10_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 2),
        (∀ l : Fin 6, ∑ j : Fin 6, y j * orbit10S (orbit10Sels l) (orbit10Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit10S b (orbit10Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit10_fold_uniform_witness :
    FoldUniformWitness orbit10S orbit10Sels orbit10Cols :=
  fold_uniform_witness_of_fin_check orbit10S orbit10Sels orbit10Cols
    orbit10_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit10_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit10S r → False :=
  no_short_of_deletions 6 6 orbit10S orbit10Sels orbit10Cols
    orbit10_selected_independent orbit10_fold_uniform_witness

/-- Orbit-10 forced-product bound. -/
theorem orbit10_lb12 : QuotientRankAtLeast orbit10W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit10Pi orbit10Pi_kills_W orbit10_slice_no_short

end QiushiMatmul
