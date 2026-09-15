import QiushiFrozenL0Profile
import QiushiFullOccupationSystemBridge
import QiushiPlaneQuotientCount

/-!
# Calibration row semantics

Quotient labels are 0..127; occupation position j denotes label j+1.
The finite certificates below identify these labels with the actual quotient,
and identify row-mask sums with its occupation masses. No numeric L0 assertion,
positive witness, or equality with a historical lookup table is assumed here.
-/

open BigOperators

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report OccupationSystemBridge FullSubspaceCount

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem matrix_neg_eq_self (M : Mat3) : -M = M := by
  ext i j
  have h : -(M i j) = M i j := by
    rcases scalar_cases (M i j) with h | h <;> rw [h] <;> decide
  exact h

theorem code_quotient_eq_iff (bs : List Nat) (a b : Fin 512) :
    (spanCodes bs).mkQ (codeMat a.val) = (spanCodes bs).mkQ (codeMat b.val) ↔
      xorCode a b ∈ spanEnum bs := by
  rw [mem_spanEnum]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ ↔ _
  rw [Submodule.Quotient.eq, sub_eq_add_neg, matrix_neg_eq_self]
  exact (congrArg (fun M => M ∈ spanCodes bs) (codeMat_xor a.val b.val)).symm.to_iff

/-- The whole quotient, including zero. `lift` and `label` are executable data. -/
structure Coordinates (bs : List Nat) where
  lift : Fin 128 → Fin 512
  label : Fin 512 → Fin 128
  zero : lift 0 = 0
  separate : ∀ a b, xorCode (lift a) (lift b) ∈ spanEnum bs ↔ a = b
  cover : ∀ c, xorCode c (lift (label c)) ∈ spanEnum bs

namespace Coordinates

variable {bs : List Nat} (C : Coordinates bs)

noncomputable def quotientEquiv : Fin 128 ≃ Mat3 ⧸ spanCodes bs :=
  Equiv.ofBijective (fun q => (spanCodes bs).mkQ (codeMat (C.lift q).val)) (by
    constructor
    · intro a b h
      exact (C.separate a b).mp ((code_quotient_eq_iff bs _ _).mp h)
    · intro q
      obtain ⟨M, rfl⟩ := (spanCodes bs).mkQ_surjective q
      let c := matrixCodeEquiv.symm M
      refine ⟨C.label c, ?_⟩
      have h := (code_quotient_eq_iff bs c (C.lift (C.label c))).mpr (C.cover c)
      have hc : codeMat c.val = M := matrixCodeEquiv.apply_symm_apply M
      rw [hc] at h
      exact h.symm)

@[simp] theorem quotientEquiv_apply (q : Fin 128) :
    C.quotientEquiv q = (spanCodes bs).mkQ (codeMat (C.lift q).val) := rfl

@[simp] theorem quotientEquiv_zero : C.quotientEquiv 0 = 0 := by
  simp [C.zero, codeMat_zero]

theorem label_correct (c : Fin 512) :
    C.quotientEquiv (C.label c) = (spanCodes bs).mkQ (codeMat c.val) :=
  ((code_quotient_eq_iff bs c _).mpr (C.cover c)).symm

theorem label_eq_zero_iff (c : Fin 512) :
    C.label c = 0 ↔ codeMat c.val ∈ spanCodes bs := by
  rw [← C.quotientEquiv.injective.eq_iff, C.label_correct, C.quotientEquiv_zero]
  exact Submodule.Quotient.mk_eq_zero _

noncomputable def directionEquiv : Fin 127 ≃ Direction (spanCodes bs) where
  toFun j := ⟨C.quotientEquiv ⟨j.val + 1, by omega⟩, by
    intro h
    have hz := C.quotientEquiv_zero
    have he := C.quotientEquiv.injective (h.trans hz.symm)
    have := congrArg Fin.val he
    simp at this⟩
  invFun q := ⟨(C.quotientEquiv.symm q.val).val - 1, by
    have hn : C.quotientEquiv.symm q.val ≠ 0 := by
      intro h
      have := congrArg C.quotientEquiv h
      exact q.property (by simpa only [Equiv.apply_symm_apply, C.quotientEquiv_zero] using this)
    have hp := (C.quotientEquiv.symm q.val).isLt
    have hv : (C.quotientEquiv.symm q.val).val ≠ 0 := fun h => hn (Fin.ext h)
    omega⟩
  left_inv j := by
    apply Fin.ext
    change (C.quotientEquiv.symm (C.quotientEquiv ⟨j.val + 1, _⟩)).val - 1 = j.val
    rw [Equiv.symm_apply_apply]
    simp
  right_inv q := by
    apply Subtype.ext
    have hn : (C.quotientEquiv.symm q.val).val ≠ 0 := by
      intro h
      have hz : C.quotientEquiv.symm q.val = 0 := Fin.ext h
      have := congrArg C.quotientEquiv hz
      exact q.property (by simpa only [Equiv.apply_symm_apply, C.quotientEquiv_zero] using this)
    have he : (⟨(C.quotientEquiv.symm q.val).val - 1 + 1, by omega⟩ : Fin 128) =
        C.quotientEquiv.symm q.val := by apply Fin.ext; dsimp; omega
    change C.quotientEquiv _ = q.val
    rw [he, Equiv.apply_symm_apply]

@[simp] theorem directionEquiv_val (j : Fin 127) :
    (C.directionEquiv j).val =
      (spanCodes bs).mkQ (codeMat (C.lift ⟨j.val + 1, by omega⟩).val) := rfl

noncomputable def weight (x : Fin 127 → Int) : Direction (spanCodes bs) → Int :=
  fun q => x (C.directionEquiv.symm q)

@[simp] theorem weight_direction (x : Fin 127 → Int) (j : Fin 127) :
    C.weight x (C.directionEquiv j) = x j := by simp [weight]

theorem weight_nonneg_iff (x : Fin 127 → Int) :
    (∀ q, 0 ≤ C.weight x q) ↔ ∀ j, 0 ≤ x j := by
  constructor
  · intro h j
    simpa using h (C.directionEquiv j)
  · intro h q
    exact h _

theorem weight_total (x : Fin 127 → Int) :
    (∑ q, C.weight x q) = ∑ j, x j := by
  exact (Equiv.sum_comp C.directionEquiv (C.weight x)).symm.trans
    (Finset.sum_congr rfl (fun j _ => C.weight_direction x j))

theorem direction_mem_iff (U : Submodule F2 Mat3) (hWU : spanCodes bs ≤ U)
    (j : Fin 127) :
    (C.directionEquiv j).val ∈ U.map (spanCodes bs).mkQ ↔
      codeMat (C.lift ⟨j.val + 1, by omega⟩).val ∈ U := by
  change (spanCodes bs).mkQ _ ∈ U.map (spanCodes bs).mkQ ↔ _
  change _ ∈ (U.map (spanCodes bs).mkQ).comap (spanCodes bs).mkQ ↔ _
  rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr hWU]

end Coordinates

/-- Only the 127 meaningful bits of the public integer mask contribute. -/
def maskMass (mask : Nat) (x : Fin 127 → Int) : Int :=
  ∑ j with mask.testBit j.val = true, x j

theorem maskMass_eq_quotientMass {bs : List Nat} (C : Coordinates bs)
    (mask : Nat) (U : Submodule F2 Mat3)
    (hMask : ∀ j, mask.testBit j.val = true ↔
      (C.directionEquiv j).val ∈ U.map (spanCodes bs).mkQ)
    (x : Fin 127 → Int) :
    maskMass mask x = quotientMass (C.weight x) U := by
  classical
  unfold maskMass quotientMass
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp C.directionEquiv]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hMask j, C.weight_direction]
  by_cases h : mask.testBit j.val = true <;> simp [h]

/-- Finite checks against the actual matrix span, not a presumed row table. -/
theorem mask_membership_of_check {bs : List Nat} (C : Coordinates bs)
    (rowBasis : List Nat) (mask : Nat)
    (hAbove : ∀ b ∈ bs, spanContainsCode rowBasis b = true)
    (hMask : ∀ j : Fin 127, mask.testBit j.val =
      decide (C.lift ⟨j.val + 1, by omega⟩ ∈ spanEnum rowBasis)) :
    spanCodes bs ≤ spanCodes rowBasis ∧
      ∀ j, mask.testBit j.val = true ↔
        (C.directionEquiv j).val ∈ (spanCodes rowBasis).map (spanCodes bs).mkQ := by
  have hWU : spanCodes bs ≤ spanCodes rowBasis := by
    apply Submodule.span_le.mpr
    rintro M ⟨b, hb, rfl⟩
    exact spanContainsCode_implies_mem_spanCodes rowBasis b (hAbove b hb)
  refine ⟨hWU, fun j => ?_⟩
  rw [hMask, decide_eq_true_eq, mem_spanEnum, C.direction_mem_iff _ hWU]

/-- A semantic row includes both strict endpoints and exact incidence. -/
structure Row {bs : List Nat} (C : Coordinates bs) where
  mask : Nat
  space : Submodule F2 Mat3
  strict : spanCodes bs < space
  proper : space < ⊤
  membership : ∀ j, mask.testBit j.val = true ↔
    (C.directionEquiv j).val ∈ space.map (spanCodes bs).mkQ

theorem Row.maskMass_eq {bs : List Nat} {C : Coordinates bs} (row : Row C)
    (x : Fin 127 → Int) : maskMass row.mask x = quotientMass (C.weight x) row.space :=
  maskMass_eq_quotientMass C row.mask row.space row.membership x

/-- Nonempty and nonfull masks certify the strict endpoints as well. -/
def Row.ofCheck {bs : List Nat} (C : Coordinates bs)
    (rowBasis : List Nat) (mask : Nat)
    (hAbove : ∀ b ∈ bs, spanContainsCode rowBasis b = true)
    (hMask : ∀ j : Fin 127, mask.testBit j.val =
      decide (C.lift ⟨j.val + 1, by omega⟩ ∈ spanEnum rowBasis))
    (hNonempty : ∃ j : Fin 127, mask.testBit j.val = true)
    (hNonfull : ∃ j : Fin 127, mask.testBit j.val = false) : Row C where
  mask := mask
  space := spanCodes rowBasis
  membership := (mask_membership_of_check C rowBasis mask hAbove hMask).2
  strict := by
    have h := mask_membership_of_check C rowBasis mask hAbove hMask
    apply lt_of_le_of_ne h.1
    intro he
    obtain ⟨j, hj⟩ := hNonempty
    have hm := (h.2 j).mp hj
    rw [← he] at hm
    have hz : (C.directionEquiv j).val = 0 := by
      obtain ⟨M, hM, hq⟩ := hm
      rw [← hq]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hM
    exact (C.directionEquiv j).property hz
  proper := by
    apply lt_top_iff_ne_top.mpr
    intro he
    obtain ⟨j, hj⟩ := hNonfull
    have hmem : (C.directionEquiv j).val ∈
        (spanCodes rowBasis).map (spanCodes bs).mkQ := by
      rw [C.direction_mem_iff _ (mask_membership_of_check C rowBasis mask hAbove hMask).1]
      rw [he]
      trivial
    have ht := (mask_membership_of_check C rowBasis mask hAbove hMask).2 j |>.mpr hmem
    rw [hj] at ht
    cases ht

/-- Distinct signatures, not merely distinct integer masks, force distinct spaces. -/
theorem row_space_injective {bs : List Nat} {C : Coordinates bs} {n : Nat}
    (rows : Fin n → Row C)
    (hDistinct : Function.Injective (fun i j => (rows i).mask.testBit j.val :
      Fin n → Fin 127 → Bool)) : Function.Injective (fun i => (rows i).space) := by
  intro a b h
  change (rows a).space = (rows b).space at h
  apply hDistinct
  funext j
  apply Bool.eq_iff_iff.mpr
  rw [(rows a).membership, (rows b).membership, h]

/-- Cardinality closes coverage of an arbitrary concrete ordering of all rows. -/
theorem rows_complete {bs : List Nat} {C : Coordinates bs}
    (hDim : Module.finrank F2 (spanCodes bs) = 2)
    (rows : Fin 29210 → Row C)
    (hDistinct : Function.Injective (fun i j => (rows i).mask.testBit j.val :
      Fin 29210 → Fin 127 → Bool))
    (U : Submodule F2 Mat3) (hWU : spanCodes bs < U) (hU : U < ⊤) :
    ∃! i, (rows i).space = U := by
  let f : Fin 29210 → {V : Submodule F2 Mat3 // spanCodes bs < V ∧ V < ⊤} :=
    fun i => ⟨(rows i).space, (rows i).strict, (rows i).proper⟩
  have hf : Function.Injective f := fun _ _ h =>
    row_space_injective rows hDistinct (congrArg Subtype.val h)
  have hc : Nat.card (Fin 29210) =
      Nat.card {V : Submodule F2 Mat3 // spanCodes bs < V ∧ V < ⊤} := by
    rw [plane_strict_supermodule_count _ hDim]
    simp
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2
  obtain ⟨i, hi⟩ := hs ⟨U, hWU, hU⟩
  refine ⟨i, congrArg Subtype.val hi, ?_⟩
  intro j hj
  exact hf (Subtype.ext (hj.trans (congrArg Subtype.val hi).symm))

/-- Exact finite/all-subspace cap equivalence, for any labels and any target. -/
theorem row_caps_iff {bs : List Nat} {C : Coordinates bs}
    (rows : Fin 29210 → Row C)
    (hCover : ∀ U : Submodule F2 Mat3, spanCodes bs < U → U < ⊤ →
      ∃ i, (rows i).space = U)
    (L : Submodule F2 Mat3 → Nat) (target : Int) (x : Fin 127 → Int) :
    (∀ i, maskMass (rows i).mask x ≤ target - (L (rows i).space : Int)) ↔
      ∀ U : Submodule F2 Mat3, spanCodes bs < U → U < ⊤ →
        quotientMass (C.weight x) U ≤ target - (L U : Int) := by
  constructor
  · intro h U hWU hU
    obtain ⟨i, rfl⟩ := hCover U hWU hU
    rw [← (rows i).maskMass_eq]
    exact h i
  · intro h i
    rw [(rows i).maskMass_eq]
    exact h _ (rows i).strict (rows i).proper

/-- A direct consumer interface for the existing full-occupation predicate. -/
theorem fullOccupation_iff (cfg : PlaneExtConfig) (C : Coordinates cfg.planeBasis)
    (rows : Fin 29210 → Row C)
    (hCover : ∀ U : Submodule F2 Mat3, cfg.W < U → U < ⊤ →
      ∃ i, (rows i).space = U)
    (L : Submodule F2 Mat3 → Nat) (x : Fin 127 → Int) :
    FullOccupation cfg L (C.weight x) ↔
      (∀ j, 0 ≤ x j) ∧ (∑ j, x j) = (cfg.target : Int) ∧
        ∀ i, maskMass (rows i).mask x ≤ (cfg.target : Int) - (L (rows i).space : Int) := by
  constructor
  · intro h
    exact ⟨(C.weight_nonneg_iff x).mp h.nonneg,
      (C.weight_total x).symm.trans h.total,
      (row_caps_iff rows hCover L cfg.target x).mpr h.cap⟩
  · rintro ⟨hn, ht, hc⟩
    exact ⟨(C.weight_nonneg_iff x).mpr hn, (C.weight_total x).trans ht,
      (row_caps_iff rows hCover L cfg.target x).mp hc⟩

end QiushiMatmul.CalibrationRows
