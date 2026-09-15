import QiushiAllHighPlaneGeometry
import QiushiConversion
import QiushiOccupation

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul
set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

theorem allHighPlane_pair_lb19 (P : FinitePremises) (A B : Mat3)
    (hA : 2 ≤ A.rank) (hB : 2 ≤ B.rank) (hAB : 2 ≤ (A + B).rank) :
    QuotientRankAtLeast (Submodule.span F2 ({A, B} : Set Mat3)) 19 := by
  have hA0 : A ≠ 0 := by
    intro h
    subst A
    simpa using hA
  let a := matrixCode A
  have ha0 : a.val ≠ 0 := by
    intro ha
    apply hA0
    exact (codeMat_matrixCode A).symm.trans (by change codeMat a.val = 0; rw [ha]; decide)
  letI : Invertible (ahLineP a) := Matrix.invertibleOfIsUnitDet _ (ahLineP_isUnitDet a)
  letI : Invertible (ahLineQ a) := Matrix.invertibleOfIsUnitDet _ (ahLineQ_isUnitDet a)
  let k := ahLineRank a
  let R : Mat3 := codeMat (ahLineRepCode k)
  have hRA : actionA (ahLineP a) (ahLineQ a) R = A := by
    change actionA (ahLineP a) (ahLineQ a) (codeMat (ahLineRepCode (ahLineRank a))) = A
    rw [ahLineAction a ha0]
    simpa [a, matrixCode] using codeMat_matrixCode A
  let N := pullbackA (ahLineP a) (ahLineQ a) B
  have hNB : actionA (ahLineP a) (ahLineQ a) N = B := by
    exact actionA_pullbackA B
  have hRrank : 2 ≤ R.rank := by
    have heq := ah_action_rank_eq (ahLineP a) (ahLineQ a) R
    rw [hRA] at heq
    omega
  have hNrank : 2 ≤ N.rank := by
    have heq := ah_action_rank_eq (ahLineP a) (ahLineQ a) N
    rw [hNB] at heq
    omega
  have hRNrank : 2 ≤ (R + N).rank := by
    have heq := ah_action_rank_eq (ahLineP a) (ahLineQ a) (R + N)
    have hact : actionA (ahLineP a) (ahLineQ a) (R + N) = A + B := by
      rw [actionA_add, hRA, hNB]
    rw [hact] at heq
    omega
  let b := matrixCode N
  have hNcode : N = codeMat b.val := by
    symm
    simpa [b, matrixCode] using codeMat_matrixCode N
  have hv : ahSecValid k b := by
    refine ⟨?_, ?_, ?_⟩
    · let rcode : Fin 512 := ⟨ahLineRepCode k, by simpa using ahLineRepCode_lt k⟩
      have hrank : 2 ≤ (codeMat rcode.val : Mat3).rank := by simpa [rcode, R] using hRrank
      simpa [rcode] using ah_code_rank_high_of_codeMat_rank_high rcode hrank
    · have hbRank : 2 ≤ (codeMat b.val : Mat3).rank := by rwa [← hNcode]
      exact ah_code_rank_high_of_codeMat_rank_high b hbRank
    · have hklt : ahLineRepCode k < 2 ^ 9 := ahLineRepCode_lt k
      let x : Fin 512 :=
        ⟨Nat.xor (ahLineRepCode k) b.val,
          by simpa using Nat.xor_lt_two_pow hklt b.isLt⟩
      have hx : codeMat x.val = R + N := by
        change codeMat (Nat.xor (ahLineRepCode k) b.val) = R + N
        rw [codeMat_xor, ← hNcode]
      have hxrank : 2 ≤ (codeMat x.val : Mat3).rank := by rwa [hx]
      simpa [x] using ah_code_rank_high_of_codeMat_rank_high x hxrank
  let pi := ahSecPlane k b
  let tr := ahSecTranspose k b
  have hbase : QuotientRankAtLeast (ahPlaneW pi) 19 := ah_plane_lb19 P pi
  have hsource : QuotientRankAtLeast (ahSourceW pi tr) 19 := by
    cases htr : tr
    · simpa [ahSourceW, htr] using hbase
    · simpa [ahSourceW, htr] using quotientRankAtLeast_transpose hbase
  letI : Invertible (ahSecP k b) := Matrix.invertibleOfIsUnitDet _ (ahSecP_isUnitDet k b)
  letI : Invertible (ahSecQ k b) := Matrix.invertibleOfIsUnitDet _ (ahSecQ_isUnitDet k b)
  have hnorm := quotientRankAtLeast_action (P := ahSecP k b) (Q := ahSecQ k b) hsource
  have hnormW : actionW (ahSecP k b) (ahSecQ k b) (ahSourceW pi tr) =
      Submodule.span F2 ({R, N} : Set Mat3) := by
    rw [ah_source_span_selected pi tr (ahSecSelA k b) (ahSecSelB k b)
      (ahSecSelectors_ne_all k b hv), ah_actionW_span_pair,
      ahSecActionA k b hv, ahSecActionB k b hv]
    change Submodule.span F2 ({codeMat (ahLineRepCode k), codeMat b.val} : Set Mat3) =
      Submodule.span F2 ({R, N} : Set Mat3)
    rw [← hNcode]
  rw [hnormW] at hnorm
  have hfinal := quotientRankAtLeast_action (P := ahLineP a) (Q := ahLineQ a) hnorm
  have hfinalW : actionW (ahLineP a) (ahLineQ a)
      (Submodule.span F2 ({R, N} : Set Mat3)) =
        Submodule.span F2 ({A, B} : Set Mat3) := by
    rw [ah_actionW_span_pair, hRA, hNB]
  rwa [hfinalW] at hfinal

/-- The requested all-high-plane exclusion in a length-20 decomposition. -/
theorem high_pair_difference_rank_le_one_from_plane_bounds
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (s t : Fin 20) (hst : s ≠ t)
    (hs : 2 ≤ (D.A s).rank) (ht : 2 ≤ (D.A t).rank) :
    (D.A s + D.A t).rank ≤ 1 := by
  by_contra hn
  push Not at hn
  have hsum : 2 ≤ (D.A s + D.A t).rank := by omega
  let W := Submodule.span F2 ({D.A s, D.A t} : Set Mat3)
  have hW : QuotientRankAtLeast W 19 := allHighPlane_pair_lb19 P _ _ hs ht hsum
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) 20 := entrywise_to_quotient D ⊥
  have hsW : D0.A s ∈ W := by
    change D.A s ∈ W
    exact Submodule.subset_span (by simp [W])
  have htW : D0.A t ∈ W := by
    change D.A t ∈ W
    exact Submodule.subset_span (by simp [W])
  have hsK : s ∈ killSet D0 W := by simp [killSet, hsW]
  have htK : t ∈ killSet D0 W := by simp [killSet, htW]
  have hpair : ({s, t} : Finset (Fin 20)) ⊆ killSet D0 W := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hsK
    · exact htK
  have hcardPair : ({s, t} : Finset (Fin 20)).card = 2 := by simp [hst]
  have hcardLe := Finset.card_le_card hpair
  have hocc : (killSet D0 W).card ≤ 20 - 19 :=
    occupation_inequality (show (⊥ : Submodule F2 Mat3) ≤ W from bot_le)
      D0 hW (by omega)
  omega

end QiushiMatmul
end
