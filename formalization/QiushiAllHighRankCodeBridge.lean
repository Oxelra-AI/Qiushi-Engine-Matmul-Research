import QiushiLineOrbit
import QiushiHuaCoset

/-! Bit-rank to Mathlib matrix-rank bridge for the all-high-plane proof. -/

open Matrix BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

def ahVecOfNonzeroCode (u : Fin 7) : I3 → F2 :=
  fun i => if Nat.testBit (u.val + 1) i.val then 1 else 0

/-- The bit-rank test has exactly zero and the 49 nonzero outer products below
rank two.  `decide +revert` produces a kernel proof, not a native axiom. -/
theorem ah_rankCode_le_one_cases : ∀ c : Fin 512, rankCode c.val ≤ 1 →
    c.val = 0 ∨ ∃ u v : Fin 7, c.val = outerCode u v := by
  decide +revert

/-- The bit-coded outer product agrees entrywise with Mathlib's matrix outer
product. -/
theorem ah_codeMat_outerCode : ∀ u v : Fin 7,
    codeMat (outerCode u v) =
      Matrix.vecMulVec (ahVecOfNonzeroCode u) (ahVecOfNonzeroCode v) := by
  decide +revert

lemma ah_matrix_rank_le_one_of_code_rank_le_one (c : Fin 512)
    (h : rankCode c.val ≤ 1) : (codeMat c.val : Mat3).rank ≤ 1 := by
  rcases ah_rankCode_le_one_cases c h with hc | ⟨u, v, hc⟩
  · rw [hc]
    have hz : (codeMat 0 : Mat3) = 0 := by decide
    rw [hz]
    simp
  · rw [hc, ah_codeMat_outerCode]
    exact Matrix.rank_vecMulVec_le _ _

lemma ah_code_rank_high_of_matrix_rank_high (M : Mat3)
    (h : 2 ≤ M.rank) : 2 ≤ rankCode (matrixCodeNat M) := by
  by_contra hn
  push Not at hn
  have hlow : rankCode (matrixCodeNat M) ≤ 1 := by omega
  let c := matrixCode M
  have hr := ah_matrix_rank_le_one_of_code_rank_le_one c
    (by simpa [c, matrixCode] using hlow)
  have hc : codeMat c.val = M := by
    simpa [c, matrixCode] using codeMat_matrixCode M
  rw [hc] at hr
  omega

/-- Direct form of the preceding bridge when a bounded bit code is already
available.  This avoids decoding and then re-encoding a matrix. -/
lemma ah_code_rank_high_of_codeMat_rank_high (c : Fin 512)
    (h : 2 ≤ (codeMat c.val : Mat3).rank) : 2 ≤ rankCode c.val := by
  by_contra hn
  push Not at hn
  have hr := ah_matrix_rank_le_one_of_code_rank_le_one c (by omega)
  omega

end QiushiMatmul
end
