import QiushiGenericDeletion

/-! # Orbit-13 forced-product seed (lb = 12)

Axis: B, k = 3, f = 9, qdim = 2
Perp codes: [84, 160]
Selected: [0, 1, 2], Columns: [0, 1, 2, 3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V2_13 := Fin 2 → F2

/-- Orbit-13 annihilator functionals. -/
def orbit13Ls : Fin 2 → Mat3 := ![codeMat 84, codeMat 160]

/-- Orbit-13 coordinate map. -/
def orbit13Pi : Mat3 →ₗ[F2] V2_13 := piOfLs orbit13Ls

/-- Orbit-13 subspace W (kernel of annihilators). -/
def orbit13W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 68, 160, 256]

/-- Orbit-13 canonical slice family. -/
def orbit13S : Coord9 → Coord9 → V2_13 :=
  fun b c => orbit13Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=3). -/
def orbit13Sels : Fin 3 → Coord9 := ![(0, 0), (0, 1), (0, 2)]

/-- Fold-uniform column coordinates (f=9). -/
def orbit13Cols : Fin 9 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit13Pi` annihilates `orbit13W`. -/
theorem orbit13Pi_kills_W (X : Mat3) (hX : X ∈ orbit13W) :
    orbit13Pi X = 0 :=
  piOfLs_kills_span orbit13Ls [1, 2, 8, 20, 68, 160, 256]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit13_selected_independent_fin :
    ∀ z : Fin 3 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 2),
        ∑ l : Fin 3, z l * orbit13S (orbit13Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit13_selected_independent :
    SelectedIndependent orbit13S orbit13Sels :=
  selected_independent_of_fin_check orbit13S orbit13Sels
    orbit13_selected_independent_fin

/-- Fold-uniform witness (finite check, 511 nonzero y). -/
theorem orbit13_fold_uniform_witness_fin :
    ∀ y : Fin 9 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 2),
        (∀ l : Fin 3, ∑ j : Fin 9, y j * orbit13S (orbit13Sels l) (orbit13Cols j) i = 0) ∧
        (∑ j : Fin 9, y j * orbit13S b (orbit13Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit13_fold_uniform_witness :
    FoldUniformWitness orbit13S orbit13Sels orbit13Cols :=
  fold_uniform_witness_of_fin_check orbit13S orbit13Sels orbit13Cols
    orbit13_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit13_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit13S r → False :=
  no_short_of_deletions 3 9 orbit13S orbit13Sels orbit13Cols
    orbit13_selected_independent orbit13_fold_uniform_witness

/-- Orbit-13 forced-product bound. -/
theorem orbit13_lb12 : QuotientRankAtLeast orbit13W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit13Pi orbit13Pi_kills_W orbit13_slice_no_short

end QiushiMatmul
