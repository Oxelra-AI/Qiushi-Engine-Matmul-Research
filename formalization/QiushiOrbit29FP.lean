import QiushiGenericDeletion

/-! # Orbit-29 forced-product seed (lb = 15)

Axis: B, k = 6, f = 9, qdim = 3
Perp codes: [68, 160, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_29 := Fin 3 → F2

/-- Orbit-29 annihilator functionals. -/
def orbit29Ls : Fin 3 → Mat3 := ![codeMat 68, codeMat 160, codeMat 256]

/-- Orbit-29 coordinate map. -/
def orbit29Pi : Mat3 →ₗ[F2] V3_29 := piOfLs orbit29Ls

/-- Orbit-29 subspace W (kernel of annihilators). -/
def orbit29W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 16, 68, 160]

/-- Orbit-29 canonical slice family. -/
def orbit29S : Coord9 → Coord9 → V3_29 :=
  fun b c => orbit29Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit29Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=9). -/
def orbit29Cols : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit29Pi` annihilates `orbit29W`. -/
theorem orbit29Pi_kills_W (X : Mat3) (hX : X ∈ orbit29W) :
    orbit29Pi X = 0 :=
  piOfLs_kills_span orbit29Ls [1, 2, 8, 16, 68, 160]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit29_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 6, z l * orbit29S (orbit29Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit29_selected_independent :
    SelectedIndependent orbit29S orbit29Sels :=
  selected_independent_of_fin_check orbit29S orbit29Sels
    orbit29_selected_independent_fin

/-- Fold-uniform witness (finite check, 511 nonzero y). -/
theorem orbit29_fold_uniform_witness_fin :
    ∀ y : Fin 9 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 6, ∑ j : Fin 9, y j * orbit29S (orbit29Sels l) (orbit29Cols j) i = 0) ∧
        (∑ j : Fin 9, y j * orbit29S b (orbit29Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit29_fold_uniform_witness :
    FoldUniformWitness orbit29S orbit29Sels orbit29Cols :=
  fold_uniform_witness_of_fin_check orbit29S orbit29Sels orbit29Cols
    orbit29_fold_uniform_witness_fin

/-- No decomposition shorter than 15. -/
theorem orbit29_slice_no_short :
    ∀ r, r < 15 → BSliceFamilyDecomp orbit29S r → False :=
  no_short_of_deletions 6 9 orbit29S orbit29Sels orbit29Cols
    orbit29_selected_independent orbit29_fold_uniform_witness

/-- Orbit-29 forced-product bound. -/
theorem orbit29_lb15 : QuotientRankAtLeast orbit29W 15 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit29Pi orbit29Pi_kills_W orbit29_slice_no_short

end QiushiMatmul
