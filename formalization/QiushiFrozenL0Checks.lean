import QiushiFrozenL0Profile

namespace QiushiMatmul.FrozenL0Report

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem normalized_upper_check : ∀ i : Fin 496,
    frozenWangLower i ≤ 14 ∨ (spanEnum (frozenWangBasis i)).card ≠ 16 ∨
      codeRankCount (frozenWangBasis i) 1 ≠ 7 ∨
      codeRankCount (frozenWangBasis i) 3 ≠ 4 := by
  decide +kernel +revert

theorem first_row_upper_check : ∀ i : Fin 496,
    frozenWangLower i ≤ 15 ∨ (spanEnum (frozenWangBasis i)).card ≠ 8 ∨
      codeRankCount (frozenWangBasis i) 1 ≠ 7 := by
  decide +kernel +revert

theorem plane_upper_check : ∀ i : Fin 496,
    frozenWangLower i ≤ 18 ∨ (spanEnum (frozenWangBasis i)).card ≠ 4 := by
  decide +kernel +revert

theorem normalized_profile_check :
    (spanEnum [272,4,2,1]).card = 16 ∧ codeRankCount [272,4,2,1] 1 = 7 ∧
      codeRankCount [272,4,2,1] 3 = 4 := by
  decide +kernel

theorem first_row_profile_check :
    (spanEnum [4,2,1]).card = 8 ∧ codeRankCount [4,2,1] 1 = 7 := by
  decide +kernel

theorem all_high_basis_labels (i : Fin 8) :
    frozenWangBasis ⟨484 + i.val, by omega⟩ = [ahPlaneCode1 i, ahPlaneCode2 i] ∧
      frozenWangLower ⟨484 + i.val, by omega⟩ = 18 := by
  fin_cases i <;> decide +kernel

theorem all_high_card_check (i : Fin 8) :
    (spanEnum [ahPlaneCode1 i, ahPlaneCode2 i]).card = 4 := by
  fin_cases i <;> decide +kernel

theorem normalized_basis_label :
    frozenWangTable.basis 249 = [80,4,2,1] ∧ frozenWangTable.lower 249 = 14 := by
  decide +kernel

theorem first_row_basis_label :
    frozenWangTable.basis 410 = [4,2,1] ∧ frozenWangTable.lower 410 = 15 := by
  decide +kernel

end QiushiMatmul.FrozenL0Report
