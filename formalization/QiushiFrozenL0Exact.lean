import QiushiFrozenL0Checks
import QiushiAllHighPlaneGeometry

namespace QiushiMatmul.FrozenL0Report

theorem representative_orbit (i : Fin 496) :
    frozenWangTable.OrbitImage i (spanCodes (frozenWangBasis i)) := by
  refine ⟨1, 1, ⟨⟨1, by simp, by simp⟩⟩, ⟨⟨1, by simp, by simp⟩⟩, false, ?_⟩
  have hid : actionALinearMap 1 1 = LinearMap.id (R := F2) (M := Mat3) := by
    ext M a b
    simp [actionALinearMap, actionA]
  simp [actionW, hid, frozenWangTable]

theorem normalized_orbit : frozenWangTable.OrbitImage 249 normalizedCosetSpan := by
  exact frozenOrbitImage_of_code_transport frozenWangTable 249
    [(272,80), (4,1), (2,2), (1,4)]
    (codeMat 273) (codeMat 84) (codeMat 84) false
    (by decide) (by decide) (by decide)
    (by rw [normalized_basis_label.1]; decide +kernel)
    (by rw [normalized_basis_label.1]; decide +kernel)

theorem normalized_L0_ge : 14 ≤ frozenWangTable.L0 normalizedCosetSpan := by
  simpa only [normalized_basis_label.2] using
    frozenWangTable.lower_le_L0 249 normalized_orbit

theorem first_row_L0_ge : 15 ≤ frozenWangTable.L0 firstRowFamily := by
  have h := frozenWangTable.lower_le_L0 410 (representative_orbit 410)
  change frozenWangTable.lower 410 ≤
    frozenWangTable.L0 (spanCodes (frozenWangTable.basis 410)) at h
  simpa only [first_row_basis_label.1, first_row_basis_label.2, firstRowFamily] using h

theorem normalized_L0_exact : frozenWangTable.L0 normalizedCosetSpan = 14 := by
  apply le_antisymm _ normalized_L0_ge
  apply L0_le_of_orbit_labels
  intro i hi
  obtain ⟨hc, hr⟩ := orbit_counts i normalizedCosetSpan hi
  have hn : Nat.card normalizedCosetSpan = 16 :=
    (spanEnum_card _).symm.trans normalized_profile_check.1
  have hnr : rankCount normalizedCosetSpan 1 = 7 :=
    (codeRankCount_correct _ _).symm.trans normalized_profile_check.2.1
  have hnr3 : rankCount normalizedCosetSpan 3 = 4 :=
    (codeRankCount_correct _ _).symm.trans normalized_profile_check.2.2
  rcases normalized_upper_check i with h | h | h | h
  · exact h
  · exact False.elim (h (hc.symm.trans hn))
  · exact False.elim (h ((hr 1).symm.trans hnr))
  · exact False.elim (h ((hr 3).symm.trans hnr3))

theorem first_row_L0_exact : frozenWangTable.L0 firstRowFamily = 15 := by
  apply le_antisymm _ first_row_L0_ge
  apply L0_le_of_orbit_labels
  intro i hi
  obtain ⟨hc, hr⟩ := orbit_counts i firstRowFamily hi
  have hn : Nat.card firstRowFamily = 8 :=
    (spanEnum_card _).symm.trans first_row_profile_check.1
  have hnr : rankCount firstRowFamily 1 = 7 :=
    (codeRankCount_correct _ _).symm.trans first_row_profile_check.2
  rcases first_row_upper_check i with h | h | h
  · exact h
  · exact False.elim (h (hc.symm.trans hn))
  · exact False.elim (h ((hr 1).symm.trans hnr))

theorem L0_le_eighteen_of_card_four (W : Submodule F2 Mat3) (hW : Nat.card W = 4) :
    frozenWangTable.L0 W ≤ 18 := by
  apply L0_le_of_orbit_labels
  intro i hi
  rcases plane_upper_check i with h | h
  · exact h
  · exact False.elim (h ((orbit_counts i W hi).1.symm.trans hW))

theorem all_high_actual_basis (i : Fin 8) :
    ahPlaneW i = spanCodes (frozenWangBasis ⟨484 + i.val, by omega⟩) := by
  rw [(all_high_basis_labels i).1, ah_spanCodes_pair]
  rfl

theorem all_high_representative_L0_exact (i : Fin 8) :
    frozenWangTable.L0 (ahPlaneW i) = 18 := by
  apply le_antisymm
  · apply L0_le_eighteen_of_card_four
    rw [all_high_actual_basis, ← spanEnum_card, (all_high_basis_labels i).1]
    exact all_high_card_check i
  · rw [all_high_actual_basis]
    have h := frozenWangTable.lower_le_L0 ⟨484 + i.val, by omega⟩
      (representative_orbit ⟨484 + i.val, by omega⟩)
    change frozenWangLower _ ≤ _ at h
    simpa only [(all_high_basis_labels i).2] using h

end QiushiMatmul.FrozenL0Report
