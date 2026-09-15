import QiushiAllHighRankCodeBridge

/-!
Public, kernel-checked aliases for the private finite line-orbit witnesses in
`QiushiLineOrbit`.  This avoids duplicating and re-elaborating the already
strict-checked 512-case certificate.
-/

open Lean Elab Term

syntax (name := ahPrivateConstTerm) "ah_private_const% " str : term

elab_rules : term
  | `(ah_private_const% $s:str) => do
      let n := s.getString.toName
      let env ← getEnv
      unless env.contains n do
        throwError "unknown private constant {n}"
      pure (mkConst n)

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

def ahLineP : Fin 512 → Mat3 :=
  lineOrbitP

def ahLineQ : Fin 512 → Mat3 :=
  ah_private_const% "_private.QiushiLineOrbit.0.QiushiMatmul.lineOrbitQ"

def ahLineRank : Fin 512 → Fin 3 :=
  lineOrbitRank

def ahLineRepCode : Fin 3 → Nat :=
  lineRepresentativeCode

theorem ahLineRepCode_lt (k : Fin 3) : ahLineRepCode k < 2 ^ 9 := by
  fin_cases k <;> decide

theorem ahLineP_isUnitDet (c : Fin 512) : IsUnit (ahLineP c).det := by
  exact isUnit_iff_ne_zero.mpr (lineOrbitP_det_ne_zero_all c)

theorem ahLineQ_isUnitDet (c : Fin 512) : IsUnit (ahLineQ c).det := by
  exact (ah_private_const%
    "_private.QiushiLineOrbit.0.QiushiMatmul.lineOrbitQ_isUnitDet") c

theorem ahLineActionRaw : ∀ (c : Fin 512) [Invertible (ahLineQ c)], c.val ≠ 0 →
    actionA (ahLineP c) (ahLineQ c) (codeMat (ahLineRepCode (ahLineRank c))) =
      codeMat c.val :=
  ah_private_const% "_private.QiushiLineOrbit.0.QiushiMatmul.lineOrbit_action"

theorem ahLineAction (c : Fin 512) [Invertible (ahLineQ c)] (hc : c.val ≠ 0) :
    actionA (ahLineP c) (ahLineQ c) (codeMat (ahLineRepCode (ahLineRank c))) =
      codeMat c.val :=
  ahLineActionRaw c hc

lemma ah_product_rank_le_middle (L X R : Mat3) : (L * X * R).rank ≤ X.rank := by
  exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)

lemma ah_action_rank_eq (P Q X : Mat3) [Invertible P] [Invertible Q] :
    (actionA P Q X).rank = X.rank := by
  rw [actionA,
    Matrix.rank_mul_eq_left_of_isUnit_det Q.transpose⁻¹ (P.transpose * X)
      (Matrix.isUnit_det_of_invertible Q.transpose⁻¹),
    Matrix.rank_mul_eq_right_of_isUnit_det P.transpose X
      (Matrix.isUnit_det_of_invertible P.transpose)]

lemma ah_pullback_rank_eq (P Q X : Mat3) [Invertible P] [Invertible Q] :
    (pullbackA P Q X).rank = X.rank := by
  rw [pullbackA,
    Matrix.rank_mul_eq_left_of_isUnit_det Q.transpose (P⁻¹.transpose * X)
      (Matrix.isUnit_det_of_invertible Q.transpose),
    Matrix.rank_mul_eq_right_of_isUnit_det P⁻¹.transpose X
      (Matrix.isUnit_det_of_invertible P⁻¹.transpose)]

end QiushiMatmul
end
