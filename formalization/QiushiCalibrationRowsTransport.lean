import QiushiCalibrationRows

namespace QiushiMatmul.CalibrationRows

open AllHighCount FrozenL0Report OccupationSystemBridge FullSubspaceCount
open BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem Coordinates.plane_finrank {bs : List Nat} (C : Coordinates bs) :
    Module.finrank F2 (spanCodes bs) = 2 := by
  have hc : Nat.card (Mat3 ⧸ spanCodes bs) = 128 := by
    rw [← Nat.card_congr C.quotientEquiv]
    simp
  have hpow := Module.natCard_eq_pow_finrank (K := F2) (V := Mat3 ⧸ spanCodes bs)
  rw [hc] at hpow
  have hd : Module.finrank F2 (Mat3 ⧸ spanCodes bs) = 7 := by
    apply Nat.pow_right_injective (a := 2) (by decide)
    simpa [F2] using hpow.symm
  have h := Submodule.finrank_quotient_add_finrank (spanCodes bs)
  rw [hd, mat3_finrank] at h
  omega

theorem Coordinates.row_count {bs : List Nat} (C : Coordinates bs) :
    Nat.card {U : Submodule F2 Mat3 // spanCodes bs < U ∧ U < ⊤} = 29210 :=
  plane_strict_supermodule_count _ C.plane_finrank

/-- Changing the complement only transports geometry, not ranks or L0. -/
structure RowTransport {bs bt : List Nat} (C : Coordinates bs) (D : Coordinates bt) where
  linear : Mat3 ≃ₗ[F2] Mat3
  base : (spanCodes bs).map linear.toLinearMap = spanCodes bt
  lift_eq : ∀ j : Fin 127,
    linear (codeMat (C.lift ⟨j.val + 1, by omega⟩).val) =
      codeMat (D.lift ⟨j.val + 1, by omega⟩).val

noncomputable def Row.transport {bs bt : List Nat} {C : Coordinates bs}
    {D : Coordinates bt} (T : RowTransport C D) (row : Row C) : Row D where
  mask := row.mask
  space := row.space.map T.linear.toLinearMap
  strict := by
    rw [← T.base]
    exact (Submodule.orderIsoMapComap T.linear).strictMono row.strict
  proper := by
    have h := (Submodule.orderIsoMapComap T.linear).strictMono row.proper
    simpa using h
  membership := by
    intro j
    have hle : spanCodes bt ≤ row.space.map T.linear.toLinearMap := by
      rw [← T.base]
      exact Submodule.map_mono row.strict.le
    rw [row.membership, C.direction_mem_iff _ row.strict.le,
      D.direction_mem_iff _ hle, ← T.lift_eq]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨M, hM, he⟩
      have h := T.linear.injective he
      rw [← h]
      exact hM

/-- Row signatures are unchanged, so a single checked catalogue suffices. -/
theorem transported_rows_complete {bs bt : List Nat} {C : Coordinates bs}
    {D : Coordinates bt} (T : RowTransport C D) (rows : Fin 29210 → Row C)
    (hDistinct : Function.Injective (fun i j => (rows i).mask.testBit j.val :
      Fin 29210 → Fin 127 → Bool))
    (U : Submodule F2 Mat3) (hWU : spanCodes bt < U) (hU : U < ⊤) :
    ∃! i, ((rows i).transport T).space = U :=
  rows_complete D.plane_finrank (fun i => (rows i).transport T) hDistinct U hWU hU

/-- A matrix linear map specified by the images of its nine coordinate units. -/
def codeLinear (images : Fin 9 → Nat) : Mat3 →ₗ[F2] Mat3 where
  toFun M := ∑ k : Fin 9,
    M ⟨k.val / 3, by omega⟩ ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ • codeMat (images k)
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a M := by simp [Finset.smul_sum, smul_smul]

theorem codeLinear_injective (images : Fin 9 → Nat)
    (h : ∀ c : Fin 512, codeLinear images (codeMat c.val) = 0 → c = 0) :
    Function.Injective (codeLinear images) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro M hM
  change M = 0
  let c := matrixCodeEquiv.symm M
  have hc : codeMat c.val = M := matrixCodeEquiv.apply_symm_apply M
  have hz : c = 0 := h c (by rw [hc]; exact hM)
  rw [← hc, hz]
  exact codeMat_zero

noncomputable def codeLinearEquiv (images : Fin 9 → Nat)
    (h : ∀ c : Fin 512, codeLinear images (codeMat c.val) = 0 → c = 0) :
    Mat3 ≃ₗ[F2] Mat3 :=
  LinearEquiv.ofBijective (codeLinear images)
    ⟨codeLinear_injective images h,
      Finite.surjective_of_injective (codeLinear_injective images h)⟩

/-- Canonical chart: bits 0..6 survive and bits 7,8 are quotiented out. -/
def standardLift (q : Fin 128) : Fin 512 := ⟨q.val, by omega⟩

def standardLabel (c : Fin 512) : Fin 128 := ⟨c.val % 128, Nat.mod_lt _ (by decide)⟩

def standardCoordinates : Coordinates [256, 128] where
  lift := standardLift
  label := standardLabel
  zero := rfl
  separate := by decide
  cover := by decide

end QiushiMatmul.CalibrationRows
