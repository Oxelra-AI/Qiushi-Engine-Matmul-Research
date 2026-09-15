import Orbit279Split.QiushiStep104Orbit279Base

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 10000
open BigOperators Finset Matrix
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

theorem contain279_32 (D : QuotientTensorDecomp o279W 16)
    (t : Fin 16)
    (ht : label279 (D.A t) ∈ (activeSet279 ⟨32, by decide⟩).image Fin.succ) :
    D.A t ∈ step103o279ActualSource32 := by
  obtain ⟨j, hj, hjl⟩ := Finset.mem_image.mp ht
  -- Rewrite the set itself; converting membership unfolds costly decision trees.
  have hset : activeSet279 ⟨32, by decide⟩ =
      ({⟨3, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩} : Finset (Fin 31)) := rfl
  rw [hset] at hj
  simp only [mem_insert, mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨3, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨8, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨12, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨17, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨21, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨26, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))
  · exact contain279_of_sec step103o279ActualSource32
      step103_o279_row32_W_le_source (D.A t) ⟨30, by decide⟩ hjl.symm
      (by
      exact spanContainsCodeCore_implies_mem_spanCodes _ _ (by decide))

theorem rowBound279_32 (D : QuotientTensorDecomp o279W 16) :
    ∑ j ∈ activeSet279 ⟨32, by decide⟩,
      occVectorInt (fun t : Fin 16 => label279 (D.A t)) 31 (Nat.le_refl _) j
    ≤ S_279.occRhs ⟨32, by decide⟩ := by
  have h := @live_labeled_fiber_occ_row_int o279W step103o279ActualSource32
    step103_o279_row32_W_le_source 16 31 D
    (fun t => label279 (D.A t))
    (activeSet279 ⟨32, by decide⟩)
    (contain279_32 D)
    (m := 12) step103_o279_row32_qr (by decide) (target := 16) (by decide)
  simp only [S_279, occRhs_279]
  exact h

theorem coeffMatch279_32 (j : Fin 31) :
    S_279.occCoeff ⟨32, by decide⟩ j = if j ∈ activeSet279 ⟨32, by decide⟩ then 1 else 0 := by
  revert j
  decide

end QiushiMatmul
