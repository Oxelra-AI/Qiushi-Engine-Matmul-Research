import QiushiCalibrationControls
import QiushiCalibrationTable000

namespace QiushiMatmul.Calibration

set_option maxHeartbeats 24000000
set_option maxRecDepth 200000

/-- The first 127 RREF-ordered rows are the singleton quotient subspaces. -/
def singletonRow (q : Fin 127) : TableRow :=
  tableChunk000.get ⟨q.val, by rw [tableChunk000_length]; omega⟩

theorem singleton_masks : ∀ q, (singletonRow q).mask = 2 ^ q.val := by decide +kernel

/-- Integer subtraction keeps even an incorrectly oversized label visible. -/
def singletonCap (i : Fin 8) (q : Fin 127) : Int :=
  18 - ((singletonRow q).storedLabel i : Int)

def capCount (i : Fin 8) (cap : Int) : Nat :=
  (Finset.univ.filter fun q => singletonCap i q = cap).card

theorem singleton_cap_distribution : ∀ i : Fin 8,
    capCount i 0 = ![84, 86, 87, 79, 86, 95, 84, 78] i ∧
    capCount i 1 = ![43, 41, 40, 48, 41, 31, 43, 49] i ∧
    capCount i 2 = (if i = 5 then 1 else 0) := by decide +kernel

theorem seven_boolean_caps : ∀ i : Fin 8, i ≠ 5 → ∀ q,
    singletonCap i q = 0 ∨ singletonCap i q = 1 := by decide +kernel

theorem orbit489_unique_cap_two : ∀ q, singletonCap 5 q = 2 ↔ q = 1 := by decide +kernel

noncomputable def actualSingletonCap (i : Fin 8)
    (q : OccupationSystemBridge.Direction (W i)) : Int :=
  singletonCap i ((coordinates i).directionEquiv.symm q)

/-- Counts on actual quotient directions, still of stored labels, not assumed L0 values. -/
theorem actual_cap_count (i : Fin 8) (cap : Int) :
    Nat.card {q : OccupationSystemBridge.Direction (W i) // actualSingletonCap i q = cap} =
      capCount i cap := by
  classical
  let e := (coordinates i).directionEquiv.subtypeEquiv (p := fun q => singletonCap i q = cap)
    (q := fun q => actualSingletonCap i q = cap) (by
      intro j
      change singletonCap i j = cap ↔
        singletonCap i ((coordinates i).directionEquiv.symm ((coordinates i).directionEquiv j)) = cap
      exact (congrArg (fun q => singletonCap i q = cap)
        ((coordinates i).directionEquiv.symm_apply_apply j)).symm.to_iff)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype _

end QiushiMatmul.Calibration
