import QiushiDegenerateExcess
import QiushiHuaSunflower
import QiushiRankBridge

/-!
Kernel-checked finite normalization data for the affine-coset profile step.
It internalizes the seven direction witnesses and all forty-two rank-two
residual witnesses produced by `step85_profile_normalization_table.py`.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

def codexDirectionPCode (u : Fin 7) : Nat :=
  match u.val with
  | 0 => 161
  | 1 => 140
  | 2 => 165
  | 3 => 84
  | 4 => 163
  | 5 => 156
  | _ => 167

def codexDirectionPInvCode (u : Fin 7) : Nat :=
  match u.val with
  | 0 => 161
  | 1 => 98
  | 2 => 163
  | 3 => 84
  | 4 => 165
  | 5 => 102
  | _ => 167

def codexVecFromFin8 (w : Fin 8) : I3 → F2 := fun i =>
  if Nat.testBit w.val i.val then 1 else 0

theorem codex_vec_has_fin8 (v : I3 → F2) :
    ∃ w : Fin 8, codexVecFromFin8 w = v := by
  revert v
  decide

/-- Right-action witness for each of the 42 zero-first-row, rank-two residuals.
The default is the identity and is irrelevant under the theorem hypotheses. -/
def codexResidualQCode (p : Fin 512) : Nat :=
  match p.val with
  | 80 => 98 | 88 => 102 | 96 => 266 | 104 => 270 | 112 => 298 | 120 => 302
  | 136 => 84 | 152 => 116 | 160 => 273 | 168 => 277 | 176 => 305 | 184 => 309
  | 200 => 86 | 208 => 114 | 224 => 275 | 232 => 279 | 240 => 307 | 248 => 311
  | 264 => 140 | 272 => 161 | 280 => 165 | 296 => 396 | 304 => 417 | 312 => 421
  | 328 => 142 | 336 => 163 | 344 => 167 | 352 => 394 | 368 => 419 | 376 => 423
  | 392 => 156 | 400 => 177 | 408 => 181 | 416 => 401 | 424 => 405 | 440 => 444
  | 456 => 158 | 464 => 179 | 472 => 183 | 480 => 403 | 488 => 407 | 496 => 442
  | _ => 273

def codexResidualQInvCode (p : Fin 512) : Nat :=
  match p.val with
  | 80 => 140 | 88 => 156 | 96 => 266 | 104 => 298 | 112 => 270 | 120 => 302
  | 136 => 84 | 152 => 92 | 160 => 273 | 168 => 277 | 176 => 305 | 184 => 309
  | 200 => 212 | 208 => 204 | 224 => 275 | 232 => 279 | 240 => 311 | 248 => 307
  | 264 => 98 | 272 => 161 | 280 => 163 | 296 => 106 | 304 => 177 | 312 => 179
  | 328 => 354 | 336 => 165 | 344 => 167 | 352 => 330 | 368 => 183 | 376 => 181
  | 392 => 102 | 400 => 417 | 408 => 423 | 416 => 401 | 424 => 407 | 440 => 110
  | 456 => 358 | 464 => 421 | 472 => 419 | 480 => 403 | 488 => 405 | 496 => 334
  | _ => 273

/-- The explicit matrix action used by the table.  `qInvCode` is the code of
`Q⁻¹`, so the last factor is `Q⁻ᵀ`, exactly as in `actionA`. -/
def codexRawActionCode (pCode qInvCode aCode : Nat) : Nat :=
  matrixCodeNat ((codeMat pCode).transpose * codeMat aCode *
    (codeMat qInvCode).transpose)

/-- The seven `P` tables are genuine two-sided inverses. -/
theorem codex_direction_inverse_data : ∀ u : Fin 7,
    codeMat (codexDirectionPCode u) * codeMat (codexDirectionPInvCode u) = 1 ∧
    codeMat (codexDirectionPInvCode u) * codeMat (codexDirectionPCode u) = 1 := by
  decide +revert

theorem codex_direction_det_ne_zero : ∀ u : Fin 7,
    (codeMat (codexDirectionPCode u) : Mat3).det ≠ 0 := by
  decide +revert

/-- Each direction witness sends the complete nonzero outer-product family
with left direction `u` to the standard first-row family. -/
theorem codex_direction_normalization_data : ∀ u v : Fin 7,
    codexRawActionCode (codexDirectionPCode u) 273 (outerCode u v) =
      outerCode 0 v := by
  decide +revert

/-- Matrix-level form, including the zero right vector. -/
theorem codex_direction_normalization_matrix : ∀ u : Fin 7, ∀ v : Fin 8,
    (codeMat (codexDirectionPCode u)).transpose *
      outerMat (vecFromFin7 u) (codexVecFromFin8 v) *
        (codeMat 273).transpose =
        outerMat (vecFromFin7 0) (codexVecFromFin8 v) := by
  decide +revert

/-- The forty-two selected `Q` matrices are genuine two-sided inverses. -/
theorem codex_residual_inverse_data : ∀ p : Fin 512,
    p.val &&& 7 = 0 → residualRank p.val = 2 →
    codeMat (codexResidualQCode p) * codeMat (codexResidualQInvCode p) = 1 ∧
    codeMat (codexResidualQInvCode p) * codeMat (codexResidualQCode p) = 1 := by
  decide +revert

theorem codex_residual_det_ne_zero : ∀ p : Fin 512,
    p.val &&& 7 = 0 → residualRank p.val = 2 →
    (codeMat (codexResidualQCode p) : Mat3).det ≠ 0 := by
  decide +revert

/-- Every zero-first-row residual of rank two is sent to code 272. -/
theorem codex_rank2_residual_base_normalization : ∀ p : Fin 512,
    p.val &&& 7 = 0 → residualRank p.val = 2 →
    codexRawActionCode 161 (codexResidualQInvCode p) p.val = 272 := by
  decide +revert

/-- Full coset form of the 42-witness table: the action bijects the eight
points of the residual coset with the eight points `272 xor w`. -/
theorem codex_rank2_residual_coset_normalization : ∀ p : Fin 512,
    p.val &&& 7 = 0 → residualRank p.val = 2 →
    (∀ v : Fin 8, ∃ w : Fin 8,
      codexRawActionCode 161 (codexResidualQInvCode p) (Nat.xor p.val v.val) =
        Nat.xor 272 w.val) ∧
    (∀ w : Fin 8, ∃ v : Fin 8,
      codexRawActionCode 161 (codexResidualQInvCode p) (Nat.xor p.val v.val) =
        Nat.xor 272 w.val) := by
  decide +revert

/-- The same 42 coset bijections stated as explicit matrix products. -/
theorem codex_rank2_residual_matrix_normalization : ∀ p : Fin 512,
    p.val &&& 7 = 0 → residualRank p.val = 2 →
    ∀ v : Fin 8, ∃ w : Fin 8,
      (codeMat 161).transpose * codeMat (Nat.xor p.val v.val) *
          (codeMat (codexResidualQInvCode p)).transpose =
        codeMat (Nat.xor 272 w.val) := by
  decide +revert

theorem codex_zero_first_row_residual_rank_le_two : ∀ p : Fin 512,
    p.val &&& 7 = 0 → residualRank p.val ≤ 2 := by
  decide +revert

theorem codex_degenerate_coset_rank_le_two : ∀ p : Fin 512,
    residualRank p.val ≤ 1 → ∀ v : Fin 8,
      rankCode (Nat.xor p.val v.val) ≤ 2 := by
  decide +revert

theorem codex_degenerate_high_label_cap : ∀ p : Fin 512,
    residualRank p.val ≤ 1 →
    (Finset.univ.filter fun v : Fin 8 =>
      2 ≤ rankCode (Nat.xor p.val v.val)).card ≤ 6 := by
  decide +revert

/-- In a degenerate residual coset every high point has rank exactly two, so
the finite high-label count is exactly the `cosetExcess` used by
`degenerate_excess_contradiction`. -/
theorem codex_degenerate_high_label_card_eq_excess : ∀ p : Fin 512,
    residualRank p.val ≤ 1 →
    (Finset.univ.filter fun v : Fin 8 =>
      2 ≤ rankCode (Nat.xor p.val v.val)).card = cosetExcess p.val := by
  decide +revert

/-- The already checked degenerate-excess theorem, exposed in the same module
as the normalization split so the next symbolic layer has one interface. -/
theorem codex_degenerate_branch_excess_lt_seven (p : Fin 512)
    (h : residualRank p.val ≤ 1) : cosetExcess p.val < 7 :=
  degenerate_excess_contradiction p h

end QiushiMatmul
end
