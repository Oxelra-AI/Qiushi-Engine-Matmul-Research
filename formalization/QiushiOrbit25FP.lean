import QiushiGenericDeletion

/-! # Orbit-25 forced-product seed (lb = 12)

Axis: B, k = 6, f = 6, qdim = 3
Perp codes: [128, 80, 32]
Selected: [0, 1, 2, 6, 7, 8], Columns: [3, 4, 5, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_25 := Fin 3 → F2

/-- Orbit-25 annihilator functionals. -/
def orbit25Ls : Fin 3 → Mat3 := ![codeMat 128, codeMat 80, codeMat 32]

/-- Orbit-25 coordinate map. -/
def orbit25Pi : Mat3 →ₗ[F2] V3_25 := piOfLs orbit25Ls

/-- Orbit-25 subspace W (kernel of annihilators). -/
def orbit25W : Submodule F2 Mat3 := spanCodes [1, 2, 4, 8, 80, 256]

/-- Orbit-25 canonical slice family. -/
def orbit25S : Coord9 → Coord9 → V3_25 :=
  fun b c => orbit25Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit25Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit25Cols : Fin 6 → Coord9 := ![(1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit25Pi` annihilates `orbit25W`. -/
theorem orbit25Pi_kills_W (X : Mat3) (hX : X ∈ orbit25W) :
    orbit25Pi X = 0 :=
  piOfLs_kills_span orbit25Ls [1, 2, 4, 8, 80, 256]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit25_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 6, z l * orbit25S (orbit25Sels l) c i ≠ 0 := by
  decide +revert +kernel

/-- Selected slices are independent. -/
theorem orbit25_selected_independent :
    SelectedIndependent orbit25S orbit25Sels :=
  selected_independent_of_fin_check orbit25S orbit25Sels
    orbit25_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit25_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 6, ∑ j : Fin 6, y j * orbit25S (orbit25Sels l) (orbit25Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit25S b (orbit25Cols j) i ≠ 0) := by
  decide +revert +kernel

/-- Fold-uniform witness condition. -/
theorem orbit25_fold_uniform_witness :
    FoldUniformWitness orbit25S orbit25Sels orbit25Cols :=
  fold_uniform_witness_of_fin_check orbit25S orbit25Sels orbit25Cols
    orbit25_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit25_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit25S r → False :=
  no_short_of_deletions 6 6 orbit25S orbit25Sels orbit25Cols
    orbit25_selected_independent orbit25_fold_uniform_witness

/-- Orbit-25 forced-product bound. -/
theorem orbit25_lb12 : QuotientRankAtLeast orbit25W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit25Pi orbit25Pi_kills_W orbit25_slice_no_short

end QiushiMatmul
