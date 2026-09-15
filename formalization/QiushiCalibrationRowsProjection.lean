import QiushiCalibrationRows

open BigOperators

namespace QiushiMatmul.CalibrationRows

open OccupationSystemBridge

theorem Coordinates.label_eq_direction_iff {bs : List Nat} (C : Coordinates bs)
    (c : Fin 512) (j : Fin 127) :
    C.label c = (⟨j.val + 1, by omega⟩ : Fin 128) ↔
      (spanCodes bs).mkQ (codeMat c.val) = (C.directionEquiv j).val := by
  rw [← C.quotientEquiv.injective.eq_iff, C.label_correct]
  rfl

/-- Weighted projection of a finite list; quotient-zero terms are discarded. -/
def Coordinates.labelCounts {bs : List Nat} (C : Coordinates bs)
    {ι : Type*} [Fintype ι] (codes : ι → Fin 512) (weights : ι → Int)
    (j : Fin 127) : Int :=
  ∑ t with C.label (codes t) = (⟨j.val + 1, by omega⟩ : Fin 128), weights t

attribute [local instance] Classical.propDecidable

theorem Coordinates.labelCounts_correct {bs : List Nat} (C : Coordinates bs)
    {ι : Type*} [Fintype ι] (codes : ι → Fin 512) (weights : ι → Int)
    (q : Direction (spanCodes bs)) :
    C.weight (C.labelCounts codes weights) q =
      ∑ t with (spanCodes bs).mkQ (codeMat (codes t).val) = q.val, weights t := by
  classical
  obtain ⟨j, rfl⟩ := C.directionEquiv.surjective q
  rw [C.weight_direction]
  unfold labelCounts
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      C.label_eq_direction_iff]
  · intro _ _
    rfl

theorem Coordinates.labelCounts_nonneg {bs : List Nat} (C : Coordinates bs)
    {ι : Type*} [Fintype ι] (codes : ι → Fin 512) (weights : ι → Int)
    (h : ∀ t, 0 ≤ weights t) (j : Fin 127) : 0 ≤ C.labelCounts codes weights j :=
  Finset.sum_nonneg (fun t _ => h t)

theorem Coordinates.labelCounts_total {bs : List Nat} (C : Coordinates bs)
    {ι : Type*} [Fintype ι] (codes : ι → Fin 512) (weights : ι → Int) :
    (∑ j, C.labelCounts codes weights j) =
      (∑ t, weights t) - ∑ t with codeMat (codes t).val ∈ spanCodes bs, weights t := by
  classical
  have h := labelMass_total (fun t => C.label (codes t)) weights
  rw [Fin.sum_univ_succ] at h
  have hz : labelMass (fun t => C.label (codes t)) weights 0 =
      ∑ t with codeMat (codes t).val ∈ spanCodes bs, weights t := by
    unfold labelMass
    apply Finset.sum_congr
    · ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, C.label_eq_zero_iff]
    · intro _ _
      rfl
  have hs : (∑ j : Fin 127, labelMass (fun t => C.label (codes t)) weights j.succ) =
      ∑ j, C.labelCounts codes weights j := by
    apply Finset.sum_congr rfl
    intro j _
    unfold labelMass labelCounts
    apply Finset.sum_congr
    · ext t
      rfl
    · intro _ _
      rfl
  rw [hz, hs] at h
  omega

end QiushiMatmul.CalibrationRows
