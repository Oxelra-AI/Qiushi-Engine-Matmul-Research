import QiushiFrozenLabelCore

namespace QiushiMatmul.FrozenLabel

open FrozenL0Report

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem rank_one_plane_upper_check : ∀ i : Fin 496,
    frozenWangLower i ≤ 17 ∨ (spanEnum (frozenWangBasis i)).card ≠ 4 ∨
      codeRankCount (frozenWangBasis i) 1 ≠ 3 := by
  decide +kernel +revert

theorem plane_labels_check (i : Fin 14) :
    (spanEnum (frozenWangBasis ⟨478 + i.val, by omega⟩)).card = 4 ∧
    frozenWangLower ⟨478 + i.val, by omega⟩ = (if i.val = 0 then 17 else 18) := by
  fin_cases i <;> decide +kernel

theorem plane478_exact : frozenWangTable.L0 (spanCodes (frozenWangBasis 478)) = 17 := by
  have hc : Nat.card (spanCodes (frozenWangBasis 478)) = 4 :=
    (spanEnum_card _).symm.trans (plane_labels_check 0).1
  have hr : rankCount (spanCodes (frozenWangBasis 478)) 1 = 3 := by
    rw [← codeRankCount_correct]
    decide +kernel
  apply le_antisymm
  · apply L0_le_of_orbit_labels
    intro j hj
    obtain ⟨hjc, hjr⟩ := orbit_counts _ _ hj
    rcases rank_one_plane_upper_check j with h | h | h
    · exact h
    · exact False.elim (h (hjc.symm.trans hc))
    · exact False.elim (h ((hjr 1).symm.trans hr))
  · exact frozenWangTable.lower_le_L0 478 (representative_orbit 478)

theorem plane_representative_exact (i : Fin 14) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis ⟨478 + i.val, by omega⟩)) =
      frozenWangLower ⟨478 + i.val, by omega⟩ := by
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    exact plane478_exact
  · apply le_antisymm
    · rw [(plane_labels_check i).2, if_neg hi]
      apply L0_le_eighteen_of_card_four
      exact (spanEnum_card _).symm.trans (plane_labels_check i).1
    · exact frozenWangTable.lower_le_L0 _ (representative_orbit _)

theorem empty_representative_exact :
    frozenWangTable.L0 (spanCodes (frozenWangBasis 495)) = frozenWangLower 495 := by
  have hmax : ∀ i : Fin 496, frozenWangLower i ≤ 20 := by decide +kernel +revert
  apply le_antisymm
  · exact L0_le_of_orbit_labels _ 20 (fun i _ => hmax i)
  · exact frozenWangTable.lower_le_L0 495 (representative_orbit 495)

theorem small_representative_exact (i : Fin 496) (hi : 478 ≤ i.val) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i := by
  by_cases hp : i.val < 492
  · let k : Fin 14 := ⟨i.val - 478, by omega⟩
    have he : (⟨478 + k.val, by omega⟩ : Fin 496) = i := Fin.ext (by dsimp [k]; omega)
    simpa only [he] using plane_representative_exact k
  · have hcases : i = 492 ∨ i = 493 ∨ i = 494 ∨ i = 495 := by
      have := i.isLt
      omega
    rcases hcases with rfl | rfl | rfl | rfl
    · change frozenWangTable.L0 (spanCodes [1]) = 19
      rw [singleton_spanCodes]
      exact nonzero_line_L0_exact (codeMat 1) (by decide)
    · change frozenWangTable.L0 (spanCodes [10]) = 19
      rw [singleton_spanCodes]
      exact nonzero_line_L0_exact (codeMat 10) (by decide)
    · change frozenWangTable.L0 (spanCodes [84]) = 19
      rw [singleton_spanCodes]
      exact nonzero_line_L0_exact (codeMat 84) (by decide)
    · exact empty_representative_exact

theorem labels_eq_of_small_overlap (i j : Fin 496) (hi : 478 ≤ i.val) (hj : 478 ≤ j.val)
    (W : Submodule F2 Mat3) (hWi : frozenWangTable.OrbitImage i W)
    (hWj : frozenWangTable.OrbitImage j W) : frozenWangLower i = frozenWangLower j :=
  labels_eq_of_exact_representatives i j (small_representative_exact i hi)
    (small_representative_exact j hj) W hWi hWj

end QiushiMatmul.FrozenLabel
