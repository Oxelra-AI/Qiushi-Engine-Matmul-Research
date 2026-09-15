import QiushiGenericDeletion

/-! # Orbit-40 forced-product seed (lb = 12)

Axis: B, k = 6, f = 6, qdim = 3
Perp codes: [20, 68, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V3_40 := Fin 3 → F2

/-- Orbit-40 annihilator functionals. -/
def orbit40Ls : Fin 3 → Mat3 := ![codeMat 20, codeMat 68, codeMat 256]

/-- Orbit-40 coordinate map. -/
def orbit40Pi : Mat3 →ₗ[F2] V3_40 := piOfLs orbit40Ls

/-- Orbit-40 subspace W (kernel of annihilators). -/
def orbit40W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 32, 84, 128]

/-- Orbit-40 canonical slice family. -/
def orbit40S : Coord9 → Coord9 → V3_40 :=
  fun b c => orbit40Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit40Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit40Cols : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit40Pi` annihilates `orbit40W`. -/
theorem orbit40Pi_kills_W (X : Mat3) (hX : X ∈ orbit40W) :
    orbit40Pi X = 0 :=
  piOfLs_kills_span orbit40Ls [1, 2, 8, 32, 84, 128]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit40_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 3),
        ∑ l : Fin 6, z l * orbit40S (orbit40Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit40_selected_independent :
    SelectedIndependent orbit40S orbit40Sels :=
  selected_independent_of_fin_check orbit40S orbit40Sels
    orbit40_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit40_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 3),
        (∀ l : Fin 6, ∑ j : Fin 6, y j * orbit40S (orbit40Sels l) (orbit40Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit40S b (orbit40Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit40_fold_uniform_witness :
    FoldUniformWitness orbit40S orbit40Sels orbit40Cols :=
  fold_uniform_witness_of_fin_check orbit40S orbit40Sels orbit40Cols
    orbit40_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit40_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit40S r → False :=
  no_short_of_deletions 6 6 orbit40S orbit40Sels orbit40Cols
    orbit40_selected_independent orbit40_fold_uniform_witness

/-- Orbit-40 forced-product bound. -/
theorem orbit40_lb12 : QuotientRankAtLeast orbit40W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit40Pi orbit40Pi_kills_W orbit40_slice_no_short

end QiushiMatmul
