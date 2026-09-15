import QiushiCalibrationRowsTransport

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report OccupationSystemBridge

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Duplicate-tolerant list enumeration, used only to evaluate a row mask. -/
def spanList : List Nat → List (Fin 512)
  | [] => [0]
  | b :: bs => spanList bs ++ (spanList bs).map (xorCode (clampCode b))

theorem mem_spanList (bs : List Nat) (c : Fin 512) :
    c ∈ spanList bs ↔ c ∈ spanEnum bs := by
  induction bs generalizing c with
  | nil => simp [spanList, spanEnum]
  | cons b bs ih =>
    simp only [spanList, spanEnum, List.mem_append, List.mem_map,
      Finset.mem_union, Finset.mem_image]
    simp_all

/-- Ignore zero and codes outside the seven-bit quotient section. -/
def codesMask : List Nat → Nat
  | [] => 0
  | c :: cs =>
    if 0 < c ∧ c < 128 then (2 ^ (c - 1)) ||| codesMask cs else codesMask cs

theorem codesMask_bit (cs : List Nat) (j : Fin 127) :
    (codesMask cs).testBit j.val = true ↔ j.val + 1 ∈ cs := by
  induction cs with
  | nil => simp [codesMask]
  | cons c cs ih =>
    by_cases h : 0 < c ∧ c < 128
    · simp only [codesMask, if_pos h, Nat.testBit_or, Nat.testBit_two_pow,
        Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
      have he : c - 1 = j.val ↔ j.val + 1 = c := by omega
      rw [he]
    · have he : j.val + 1 ≠ c := by have := j.isLt; omega
      simp [codesMask, h, ih, he]

def spanMask (bs : List Nat) : Nat := codesMask ((spanList bs).map Fin.val)

theorem spanMask_bit (bs : List Nat) (j : Fin 127) :
    (spanMask bs).testBit j.val =
      decide (standardLift ⟨j.val + 1, by omega⟩ ∈ spanEnum bs) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, spanMask, codesMask_bit, List.mem_map]
  constructor
  · rintro ⟨c, hc, he⟩
    have he' : c = standardLift ⟨j.val + 1, by omega⟩ := Fin.ext he
    exact (mem_spanList bs _).mp (he' ▸ hc)
  · intro h
    exact ⟨_, (mem_spanList bs _).mpr h, rfl⟩

structure RowData where
  basis : List Nat
  mask : Nat
  present : Fin 127
  absent : Fin 127
  deriving DecidableEq

def RowData.Valid (d : RowData) : Prop :=
  spanMask ([256, 128] ++ d.basis) = d.mask ∧
    d.mask.testBit d.present.val = true ∧ d.mask.testBit d.absent.val = false ∧
      d.mask < 2 ^ 127

instance (d : RowData) : Decidable d.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem RowData.above (d : RowData) :
    spanCodes [256, 128] ≤ spanCodes ([256, 128] ++ d.basis) := by
  apply Submodule.span_mono
  rintro M ⟨b, hb, rfl⟩
  exact ⟨b, List.mem_append_left _ hb, rfl⟩

theorem RowData.membership (d : RowData) (h : d.Valid) (j : Fin 127) :
    d.mask.testBit j.val = true ↔ (standardCoordinates.directionEquiv j).val ∈
      (spanCodes ([256, 128] ++ d.basis)).map (spanCodes [256, 128]).mkQ := by
  rw [← h.1, spanMask_bit, decide_eq_true_eq, mem_spanEnum,
    standardCoordinates.direction_mem_iff _ d.above]
  rfl

def RowData.row (d : RowData) (h : d.Valid) : Row standardCoordinates where
  mask := d.mask
  space := spanCodes ([256, 128] ++ d.basis)
  membership := d.membership h
  strict := by
    apply lt_of_le_of_ne d.above
    intro he
    have hm := (d.membership h d.present).mp h.2.1
    rw [← he] at hm
    obtain ⟨M, hM, hq⟩ := hm
    have hz : (standardCoordinates.directionEquiv d.present).val = 0 := by
      rw [← hq]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hM
    exact (standardCoordinates.directionEquiv d.present).property hz
  proper := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hm : (standardCoordinates.directionEquiv d.absent).val ∈
        (spanCodes ([256, 128] ++ d.basis)).map (spanCodes [256, 128]).mkQ := by
      rw [standardCoordinates.direction_mem_iff _ d.above, he]
      trivial
    have ht := (d.membership h d.absent).mpr hm
    rw [h.2.2.1] at ht
    cases ht

theorem mask_eq_of_bits {a b : Nat} (ha : a < 2 ^ 127) (hb : b < 2 ^ 127)
    (h : ∀ j : Fin 127, a.testBit j.val = b.testBit j.val) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 127
  · exact h ⟨i, hi⟩
  · have hp : 2 ^ 127 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

def catalogueRows (data : List RowData) (hLength : data.length = 29210)
    (hValid : ∀ d ∈ data, d.Valid) : Fin 29210 → Row standardCoordinates :=
  fun i => (data.get ⟨i.val, by omega⟩).row (hValid _ (List.get_mem ..))

theorem catalogueRows_distinct (data : List RowData) (hLength : data.length = 29210)
    (hValid : ∀ d ∈ data, d.Valid) (hSorted : (data.map RowData.mask).IsChain (· < ·)) :
    Function.Injective (fun i j =>
      (catalogueRows data hLength hValid i).mask.testBit j.val :
        Fin 29210 → Fin 127 → Bool) := by
  intro a b he
  have ha := hValid (data.get ⟨a.val, by omega⟩) (List.get_mem ..)
  have hb := hValid (data.get ⟨b.val, by omega⟩) (List.get_mem ..)
  have hm : (data.get ⟨a.val, by omega⟩).mask = (data.get ⟨b.val, by omega⟩).mask :=
    mask_eq_of_bits ha.2.2.2 hb.2.2.2 (fun j => congrFun he j)
  have hn : (data.map RowData.mask).Nodup :=
    (List.isChain_iff_pairwise.mp hSorted).imp (fun h => Nat.ne_of_lt h)
  have hg : (data.map RowData.mask).get ⟨a.val, by simpa [hLength] using a.isLt⟩ =
      (data.map RowData.mask).get ⟨b.val, by simpa [hLength] using b.isLt⟩ := by
    simpa only [List.get_eq_getElem, List.getElem_map] using hm
  have hv := congrArg Fin.val (hn.get_inj_iff.mp hg)
  exact Fin.ext hv

theorem catalogueRows_complete (data : List RowData) (hLength : data.length = 29210)
    (hValid : ∀ d ∈ data, d.Valid) (hSorted : (data.map RowData.mask).IsChain (· < ·))
    (U : Submodule F2 Mat3) (hWU : spanCodes [256, 128] < U) (hU : U < ⊤) :
    ∃! i, (catalogueRows data hLength hValid i).space = U :=
  rows_complete standardCoordinates.plane_finrank _
    (catalogueRows_distinct data hLength hValid hSorted) U hWU hU

end QiushiMatmul.CalibrationRows
