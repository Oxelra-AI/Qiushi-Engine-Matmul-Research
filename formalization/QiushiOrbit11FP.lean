import QiushiGenericDeletion

/-! # Orbit-11 forced-product seed (lb = 12)

Axis: B, k = 6, f = 6, qdim = 2
Perp codes: [84, 256]
Selected: [0, 1, 2, 3, 4, 5], Columns: [0, 1, 2, 6, 7, 8]
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace QiushiMatmul

abbrev V2_11 := Fin 2 → F2

/-- Orbit-11 annihilator functionals. -/
def orbit11Ls : Fin 2 → Mat3 := ![codeMat 84, codeMat 256]

/-- Orbit-11 coordinate map. -/
def orbit11Pi : Mat3 →ₗ[F2] V2_11 := piOfLs orbit11Ls

/-- Orbit-11 subspace W (kernel of annihilators). -/
def orbit11W : Submodule F2 Mat3 := spanCodes [1, 2, 8, 20, 32, 68, 128]

/-- Orbit-11 canonical slice family. -/
def orbit11S : Coord9 → Coord9 → V2_11 :=
  fun b c => orbit11Pi (tensorASlice b c)

/-- Selected deletion coordinates (k=6). -/
def orbit11Sels : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- Fold-uniform column coordinates (f=6). -/
def orbit11Cols : Fin 6 → Coord9 := ![(0, 0), (0, 1), (0, 2), (2, 0), (2, 1), (2, 2)]

/-- `orbit11Pi` annihilates `orbit11W`. -/
theorem orbit11Pi_kills_W (X : Mat3) (hX : X ∈ orbit11W) :
    orbit11Pi X = 0 :=
  piOfLs_kills_span orbit11Ls [1, 2, 8, 20, 32, 68, 128]
    (by intro n hn; fin_cases hn <;> ext q <;> fin_cases q <;> decide) X hX

/-- Selected independence (finite check). -/
theorem orbit11_selected_independent_fin :
    ∀ z : Fin 6 → F2, z ≠ 0 →
      ∃ (c : Coord9) (i : Fin 2),
        ∑ l : Fin 6, z l * orbit11S (orbit11Sels l) c i ≠ 0 := by
  decide +revert

/-- Selected slices are independent. -/
theorem orbit11_selected_independent :
    SelectedIndependent orbit11S orbit11Sels :=
  selected_independent_of_fin_check orbit11S orbit11Sels
    orbit11_selected_independent_fin

/-- Fold-uniform witness (finite check, 63 nonzero y). -/
theorem orbit11_fold_uniform_witness_fin :
    ∀ y : Fin 6 → F2, y ≠ 0 →
      ∃ (b : Coord9) (i : Fin 2),
        (∀ l : Fin 6, ∑ j : Fin 6, y j * orbit11S (orbit11Sels l) (orbit11Cols j) i = 0) ∧
        (∑ j : Fin 6, y j * orbit11S b (orbit11Cols j) i ≠ 0) := by
  decide +revert

/-- Fold-uniform witness condition. -/
theorem orbit11_fold_uniform_witness :
    FoldUniformWitness orbit11S orbit11Sels orbit11Cols :=
  fold_uniform_witness_of_fin_check orbit11S orbit11Sels orbit11Cols
    orbit11_fold_uniform_witness_fin

/-- No decomposition shorter than 12. -/
theorem orbit11_slice_no_short :
    ∀ r, r < 12 → BSliceFamilyDecomp orbit11S r → False :=
  no_short_of_deletions 6 6 orbit11S orbit11Sels orbit11Cols
    orbit11_selected_independent orbit11_fold_uniform_witness

/-- Orbit-11 forced-product bound. -/
theorem orbit11_lb12 : QuotientRankAtLeast orbit11W 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short
    orbit11Pi orbit11Pi_kills_W orbit11_slice_no_short

end QiushiMatmul
