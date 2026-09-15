import QiushiDefs
import QiushiHuaCoset
import QiushiLineOrbit

/-!
# Rank bridge: `Matrix.rank (codeMat c) = rankCode c`
-/

open Matrix BigOperators

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

-- ════════════════════════════════════════════════════════════════
-- § GL invariance of Matrix.rank
-- ════════════════════════════════════════════════════════════════

theorem rank_mul_left_unit (P M : Mat3) (hP : IsUnit P.det) :
    (P * M).rank = M.rank := by
  apply le_antisymm
  · exact rank_mul_le_right P M
  · calc M.rank = (P⁻¹ * (P * M)).rank := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul P hP, Matrix.one_mul]
      _ ≤ (P * M).rank := rank_mul_le_right P⁻¹ (P * M)

theorem rank_mul_right_unit (M Q : Mat3) (hQ : IsUnit Q.det) :
    (M * Q).rank = M.rank := by
  apply le_antisymm
  · exact rank_mul_le_left M Q
  · calc M.rank = ((M * Q) * Q⁻¹).rank := by
          rw [Matrix.mul_assoc, mul_nonsing_inv Q hQ, Matrix.mul_one]
      _ ≤ (M * Q).rank := rank_mul_le_left (M * Q) Q⁻¹

-- ════════════════════════════════════════════════════════════════
-- § Representative ranks
-- ════════════════════════════════════════════════════════════════

private lemma codeMat_273_eq_one : codeMat 273 = (1 : Mat3) := by decide
theorem rank_rep273 : (codeMat 273).rank = 3 := by rw [codeMat_273_eq_one, rank_one]; decide

private def E1 : Matrix I3 (Fin 1) F2 := fun i _ => if i = 0 then 1 else 0
private def F1 : Matrix (Fin 1) I3 F2 := fun _ j => if j = 0 then 1 else 0
set_option maxHeartbeats 800000 in
private lemma codeMat_1_factor : codeMat 1 = E1 * F1 := by decide
private def embed1 : Fin 1 → I3 := fun _ => 0
set_option maxHeartbeats 800000 in
private lemma codeMat_1_sub_one : (codeMat 1).submatrix embed1 embed1 = 1 := by decide

theorem rank_rep1 : (codeMat 1).rank = 1 := by
  apply le_antisymm
  · calc (codeMat 1).rank = (E1 * F1).rank := by rw [codeMat_1_factor]
      _ ≤ E1.rank := rank_mul_le_left E1 F1
      _ ≤ Module.finrank F2 (Fin 1 → F2) := by unfold rank; exact LinearMap.finrank_range_le _
      _ = 1 := Module.finrank_fin_fun F2
  · calc 1 = Fintype.card (Fin 1) := by decide
      _ = (1 : Matrix (Fin 1) (Fin 1) F2).rank := rank_one.symm
      _ = ((codeMat 1).submatrix embed1 embed1).rank := by rw [codeMat_1_sub_one]
      _ ≤ (codeMat 1).rank := rank_submatrix_le _ _ _

private def E17 : Matrix I3 (Fin 2) F2 := fun i k => if i.val = k.val then 1 else 0
private def F17 : Matrix (Fin 2) I3 F2 := fun k j => if k.val = j.val then 1 else 0
set_option maxHeartbeats 800000 in
private lemma codeMat_17_factor : codeMat 17 = E17 * F17 := by decide
private def embed2 : Fin 2 → I3 := Fin.castSucc
set_option maxHeartbeats 800000 in
private lemma codeMat_17_sub_one : (codeMat 17).submatrix embed2 embed2 = 1 := by decide

theorem rank_rep17 : (codeMat 17).rank = 2 := by
  apply le_antisymm
  · calc (codeMat 17).rank = (E17 * F17).rank := by rw [codeMat_17_factor]
      _ ≤ E17.rank := rank_mul_le_left E17 F17
      _ ≤ Module.finrank F2 (Fin 2 → F2) := by unfold rank; exact LinearMap.finrank_range_le _
      _ = 2 := Module.finrank_fin_fun F2
  · calc 2 = Fintype.card (Fin 2) := by decide
      _ = (1 : Matrix (Fin 2) (Fin 2) F2).rank := rank_one.symm
      _ = ((codeMat 17).submatrix embed2 embed2).rank := by rw [codeMat_17_sub_one]
      _ ≤ (codeMat 17).rank := rank_submatrix_le _ _ _

-- ════════════════════════════════════════════════════════════════
-- § Orbit transport
-- ════════════════════════════════════════════════════════════════

private def representativeRank (k : Fin 3) : ℕ :=
  match k with | 0 => 1 | 1 => 2 | 2 => 3

set_option maxHeartbeats 800000 in
private lemma rank_representative (k : Fin 3) :
    (codeMat (lineRepresentativeCode k)).rank = representativeRank k := by
  fin_cases k
  · show (codeMat 1).rank = 1; exact rank_rep1
  · show (codeMat 17).rank = 2; exact rank_rep17
  · show (codeMat 273).rank = 3; exact rank_rep273

-- QTInv unit det (512-case decide)
set_option maxHeartbeats 24000000 in
private theorem lineOrbitQTInv_det_ne_zero_all : ∀ c : Fin 512,
    (lineOrbitQTInv c).det ≠ 0 := by decide

private lemma lineOrbitQTInv_isUnitDet (c : Fin 512) : IsUnit (lineOrbitQTInv c).det :=
  isUnit_iff_ne_zero.mpr (lineOrbitQTInv_det_ne_zero_all c)

private lemma lineOrbitPT_isUnitDet (c : Fin 512) : IsUnit (lineOrbitP c).transpose.det := by
  rw [det_transpose]; exact isUnit_iff_ne_zero.mpr (lineOrbitP_det_ne_zero_all c)

-- rank(codeMat c) = rank(representative) via orbit transport
theorem rank_codeMat_eq_representative (c : Fin 512) (hc : c.val ≠ 0) :
    (codeMat c.val).rank = representativeRank (lineOrbitRank c) := by
  have hact := lineOrbit_action_explicit_all c hc
  let rep := lineRepresentativeCode (lineOrbitRank c)
  rw [← hact]
  calc ((lineOrbitP c).transpose * codeMat rep * lineOrbitQTInv c).rank
      = ((lineOrbitP c).transpose * codeMat rep).rank :=
          rank_mul_right_unit _ _ (lineOrbitQTInv_isUnitDet c)
    _ = (codeMat rep).rank :=
          rank_mul_left_unit _ _ (lineOrbitPT_isUnitDet c)
    _ = representativeRank (lineOrbitRank c) :=
          rank_representative (lineOrbitRank c)

-- ════════════════════════════════════════════════════════════════
-- § rankCode agreement
-- ════════════════════════════════════════════════════════════════

set_option maxHeartbeats 24000000 in
private theorem rankCode_eq_representativeRank_all : ∀ (c : Fin 512),
    c.val ≠ 0 → rankCode c.val = representativeRank (lineOrbitRank c) := by decide

-- ════════════════════════════════════════════════════════════════
-- § Main bridge
-- ════════════════════════════════════════════════════════════════

private lemma rank_zero_mat : (0 : Mat3).rank = 0 := by simp [rank]
private lemma codeMat_zero_eq : codeMat 0 = (0 : Mat3) := by decide
private lemma rankCode_zero : rankCode 0 = 0 := by decide

/-- Rank bridge for codes. -/
theorem rank_eq_rankCode_code (c : Fin 512) :
    (codeMat c.val).rank = rankCode c.val := by
  by_cases hc : c.val = 0
  · -- Zero case
    conv_lhs => rw [show c.val = 0 from hc]
    conv_rhs => rw [show c.val = 0 from hc]
    rw [codeMat_zero_eq, rankCode_zero]; exact rank_zero_mat
  · rw [rank_codeMat_eq_representative c hc]
    exact (rankCode_eq_representativeRank_all c hc).symm

/-- **Rank bridge.** `Matrix.rank M = rankCode (matrixCodeNat M)` for all `M : Mat3`. -/
theorem rank_eq_rankCode (M : Mat3) :
    M.rank = rankCode (matrixCodeNat M) := by
  conv_lhs => rw [← codeMat_matrixCode M]
  exact rank_eq_rankCode_code (matrixCode M)

end QiushiMatmul
end
