import QiushiCalibrationActual
import QiushiCalibrationSingletons

namespace QiushiMatmul.Calibration

open OccupationSystemBridge

theorem singleton_row_exists (q : Fin 127) : ∃ j : Fin 29210, tableRow j = singletonRow q := by
  have hm : singletonRow q ∈ table := by
    apply List.mem_flatten.mpr
    refine ⟨tableChunks 0, List.mem_ofFn.mpr ⟨0, rfl⟩, ?_⟩
    exact List.get_mem _ _
  have hs : singletonRow q ∈ orderedTable := List.mem_mergeSort.mpr hm
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hs
  exact ⟨⟨j.val, by rw [← orderedTable_length]; exact j.isLt⟩, hj⟩

noncomputable def singletonIndex (q : Fin 127) : Fin 29210 :=
  Classical.choose (singleton_row_exists q)

theorem singletonIndex_spec (q : Fin 127) : tableRow (singletonIndex q) = singletonRow q :=
  Classical.choose_spec (singleton_row_exists q)

noncomputable def singletonSpace (i : Fin 8) (q : Fin 127) : Submodule F2 Mat3 :=
  (actualRows i (singletonIndex q)).space

theorem singletonSpace_strict (i : Fin 8) (q : Fin 127) : W i < singletonSpace i q :=
  (actualRows i (singletonIndex q)).strict

theorem singletonSpace_proper (i : Fin 8) (q : Fin 127) : singletonSpace i q < ⊤ :=
  (actualRows i (singletonIndex q)).proper

/-- This is the actual superspace whose quotient has exactly the one specified
nonzero direction, not merely a row with a singleton numeric mask. -/
theorem singletonSpace_directions (i : Fin 8) (q d : Fin 127) :
    (directionSection i d).val ∈ (singletonSpace i q).map (W i).mkQ ↔ d = q := by
  calc
    _ ↔ (actualRows i (singletonIndex q)).mask.testBit d.val = true :=
      (actualRows i (singletonIndex q)).membership d |>.symm
    _ ↔ d = q := ?_
  rw [actualRows_mask, singletonIndex_spec, singleton_masks,
    Nat.testBit_two_pow, decide_eq_true_eq]
  exact ⟨fun h => Fin.ext h.symm, fun h => congrArg Fin.val h.symm⟩

noncomputable def L0SingletonCap (i : Fin 8) (q : Direction (W i)) : Int :=
  18 - (frozenWangTable.L0 (singletonSpace i ((coordinates i).directionEquiv.symm q)) : Int)

theorem L0SingletonCap_eq_stored (hExact : ExactL0) (i : Fin 8) (q : Direction (W i)) :
    L0SingletonCap i q = actualSingletonCap i q := by
  unfold L0SingletonCap singletonSpace
  rw [hExact, singletonIndex_spec]
  rfl

theorem L0_cap_count (hExact : ExactL0) (i : Fin 8) (cap : Int) :
    Nat.card {q : Direction (W i) // L0SingletonCap i q = cap} = capCount i cap := by
  simp_rw [L0SingletonCap_eq_stored hExact]
  exact actual_cap_count i cap

theorem L0_cap_distribution (hExact : ExactL0) (i : Fin 8) :
    Nat.card {q : Direction (W i) // L0SingletonCap i q = 0} =
      ![84, 86, 87, 79, 86, 95, 84, 78] i ∧
    Nat.card {q : Direction (W i) // L0SingletonCap i q = 1} =
      ![43, 41, 40, 48, 41, 31, 43, 49] i ∧
    Nat.card {q : Direction (W i) // L0SingletonCap i q = 2} = (if i = 5 then 1 else 0) := by
  simpa only [L0_cap_count hExact] using singleton_cap_distribution i

theorem L0_seven_boolean_caps (hExact : ExactL0) (i : Fin 8) (hi : i ≠ 5)
    (q : Direction (W i)) : L0SingletonCap i q = 0 ∨ L0SingletonCap i q = 1 := by
  simpa only [L0SingletonCap_eq_stored hExact, actualSingletonCap] using
    seven_boolean_caps i hi ((coordinates i).directionEquiv.symm q)

theorem L0_orbit489_unique_cap_two (hExact : ExactL0) (q : Direction (W 5)) :
    L0SingletonCap 5 q = 2 ↔ q = directionSection 5 1 := by
  rw [L0SingletonCap_eq_stored hExact]
  change singletonCap 5 ((coordinates 5).directionEquiv.symm q) = 2 ↔
    q = (coordinates 5).directionEquiv 1
  rw [orbit489_unique_cap_two]
  constructor
  · intro h
    exact ((coordinates 5).directionEquiv.apply_symm_apply q).symm.trans
      (congrArg (coordinates 5).directionEquiv h)
  · rintro rfl
    exact (coordinates 5).directionEquiv.symm_apply_apply 1

end QiushiMatmul.Calibration
