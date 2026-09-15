import QiushiAllHighCountSemantics
import QiushiAllHighCountData

open Matrix BigOperators

namespace QiushiMatmul.AllHighCount

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem matrixCodeNat_codeMat : ∀ c : Fin 512, matrixCodeNat (codeMat c.val) = c.val := by
  decide +revert

noncomputable def matrixCodeEquiv : Fin 512 ≃ Mat3 where
  toFun c := codeMat c.val
  invFun := matrixCode
  left_inv c := Fin.ext (matrixCodeNat_codeMat c)
  right_inv M := codeMat_matrixCode M

/-- The executable classifier is equivalent to the actual three matrix-rank tests. -/
theorem fastEligible_iff_highPair (a b : Fin 512) :
    fastEligible a b = true ↔ HighPair (codeMat a.val) (codeMat b.val) := by
  have hxor : (codeMat a.val + codeMat b.val).rank = rankCode (xorCode a b).val := by
    rw [← codeMat_xor]
    exact rank_eq_rankCode_code (xorCode a b)
  simp only [fastEligible, highCode_correct, Bool.and_eq_true, decide_eq_true_eq,
    HighPair, rank_eq_rankCode_code a, rank_eq_rankCode_code b, hxor, and_assoc]

abbrev EligibleCodePairs := {p : Fin 512 × Fin 512 // fastEligible p.1 p.2 = true}

noncomputable def eligibleCodeEquiv : EligibleCodePairs ≃ HighPairs :=
  (Equiv.prodCongr matrixCodeEquiv matrixCodeEquiv).subtypeEquiv
    (fun p => fastEligible_iff_highPair p.1 p.2)

theorem rowCount_card (a : Fin 512) :
    Nat.card {b : Fin 512 // fastEligible a b = true} = rowCount a := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := (List.nodup_finRange 512).card_eq_countP
    (P := fun b => fastEligible a b = true)
  simpa [rowCount] using h

theorem eligible_code_count_eq_rows :
    Nat.card EligibleCodePairs = ((List.finRange 512).map rowCount).sum := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun a b : Fin 512 => fastEligible a b = true)), Nat.card_sigma]
  simp_rw [rowCount_card]
  exact Fin.sum_univ_def rowCount

end QiushiMatmul.AllHighCount
