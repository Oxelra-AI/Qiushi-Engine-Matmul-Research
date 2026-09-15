import QiushiGenericDeletion
import QiushiFrozenWangData
import QiushiMonotonicity

/-! Unused Wang forced-product node 20, using the existing deletion theorem. -/

open BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace QiushiMatmul.GlobalOrbit.Unused

def node20Ls : Fin 3 → Mat3 := ![codeMat 96, codeMat 128, codeMat 256]
def node20Pi : Mat3 →ₗ[F2] (Fin 3 → F2) := piOfLs node20Ls
def node20S (b c : Coord9) : Fin 3 → F2 := node20Pi (tensorASlice b c)
def node20Sels : Fin 6 → Coord9 := ![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)]
def node20Cols : Fin 6 → Coord9 := ![(1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]

theorem node20Pi_kills (X : Mat3) (hX : X ∈ spanCodes [96,16,8,4,2,1]) :
    node20Pi X = 0 :=
  piOfLs_kills_span node20Ls [96,16,8,4,2,1]
    (by intro n hn; fin_cases hn <;> ext i <;> fin_cases i <;> decide +kernel) X hX

theorem node20_independent_check :
    ∀ z : Fin 6 → F2, z ≠ 0 → ∃ (c : Coord9) (i : Fin 3),
      ∑ l : Fin 6, z l * node20S (node20Sels l) c i ≠ 0 := by
  decide +kernel +revert

theorem node20_fold_check :
    ∀ y : Fin 6 → F2, y ≠ 0 → ∃ (b : Coord9) (i : Fin 3),
      (∀ l : Fin 6, ∑ j : Fin 6, y j * node20S (node20Sels l) (node20Cols j) i = 0) ∧
      (∑ j : Fin 6, y j * node20S b (node20Cols j) i ≠ 0) := by
  decide +kernel +revert

theorem node20_bound : QuotientRankAtLeast (spanCodes [96,16,8,4,2,1]) 12 :=
  quotientRankAtLeast_of_sliceFamily_no_short node20Pi node20Pi_kills
    (no_short_of_deletions 6 6 node20S node20Sels node20Cols
      (selected_independent_of_fin_check _ _ node20_independent_check)
      (fold_uniform_witness_of_fin_check _ _ _ node20_fold_check))

theorem rep020 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 20))
      (frozenWangTable.lower 20) := by
  rw [show frozenWangTable.basis 20 = [96,16,8,4,2,1] by decide +kernel,
      show frozenWangTable.lower 20 = 12 by decide +kernel]
  exact node20_bound

theorem rep086 :
    QuotientRankAtLeast (spanCodes (frozenWangTable.basis 86))
      (frozenWangTable.lower 86) := by
  rw [show frozenWangTable.basis 86 = [16,8,4,2,1] by decide +kernel,
      show frozenWangTable.lower 86 = 12 by decide +kernel]
  apply quotientRankAtLeast_mono (U := spanCodes [96,16,8,4,2,1]) ?_ node20_bound
  apply Submodule.span_le.mpr
  rintro M ⟨c, hc, rfl⟩
  exact Submodule.subset_span ⟨c, List.mem_cons_of_mem 96 hc, rfl⟩

end QiushiMatmul.GlobalOrbit.Unused
