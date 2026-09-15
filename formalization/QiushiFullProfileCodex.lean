import QiushiNormalizedCosetCapsCodex
import QiushiProfileNormalizationCodex

/-!
Full profile forcing from an arbitrary Hua affine coset.  The proof normalizes
the common direction, clears the first row of the base, excludes residual rank
at most one by the finite excess bound, applies the 42 rank-two normalization
witnesses, and invokes the normalized occupation/cap theorem.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

set_option maxRecDepth 200000
set_option maxHeartbeats 100000

def codexFirstRow (M : Mat3) : I3 → F2 := fun j => M 0 j

def codexClearFirstRow (M : Mat3) : Mat3 :=
  M + outerMat (vecFromFin7 0) (codexFirstRow M)

theorem codex_clear_first_row_code (M : Mat3) :
    matrixCodeNat (codexClearFirstRow M) &&& 7 = 0 := by
  have hrow : ∀ j : I3, codexClearFirstRow M 0 j = 0 := by
    intro j
    simp [codexClearFirstRow, codexFirstRow, outerMat, vecFromFin7,
      CharTwo.add_self_eq_zero]
  have hlower : ∀ i : I3, i ≠ 0 → ∀ j : I3,
      codexClearFirstRow M i j = M i j := by
    intro i hi j
    have hb1 : Nat.testBit 1 1 = false := by decide
    have hb2 : Nat.testBit 1 2 = false := by decide
    fin_cases i <;>
      simp_all [codexClearFirstRow, outerMat, vecFromFin7, hb1, hb2]
  unfold matrixCodeNat
  rw [hrow 0, hrow 1, hrow 2,
    hlower 1 (by decide) 0, hlower 1 (by decide) 1, hlower 1 (by decide) 2,
    hlower 2 (by decide) 0, hlower 2 (by decide) 1, hlower 2 (by decide) 2]
  rw [show 7 = 2 ^ 3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have h10 : (if M 1 0 = 1 then 8 else 0) % 8 = 0 := by
    split <;> decide
  have h11 : (if M 1 1 = 1 then 16 else 0) % 8 = 0 := by
    split <;> decide
  have h12 : (if M 1 2 = 1 then 32 else 0) % 8 = 0 := by
    split <;> decide
  have h20 : (if M 2 0 = 1 then 64 else 0) % 8 = 0 := by
    split <;> decide
  have h21 : (if M 2 1 = 1 then 128 else 0) % 8 = 0 := by
    split <;> decide
  have h22 : (if M 2 2 = 1 then 256 else 0) % 8 = 0 := by
    split <;> decide
  simp only [if_neg zero_ne_one, Nat.zero_add]
  omega

theorem codex_codeMat_fin8_outer : ∀ w : Fin 8,
    codeMat w.val = outerMat (vecFromFin7 0) (codexVecFromFin8 w) := by
  decide +revert

lemma codex_clear_coset_as_code (M : Mat3) (v : I3 → F2) :
    ∃ w : Fin 8,
      M + outerMat (vecFromFin7 0) v =
        codeMat (Nat.xor (matrixCodeNat (codexClearFirstRow M)) w.val) := by
  obtain ⟨w, hw⟩ := codex_vec_has_fin8 (v + codexFirstRow M)
  refine ⟨w, ?_⟩
  rw [codeMat_xor]
  have hdecode : codeMat (matrixCodeNat (codexClearFirstRow M)) =
      codexClearFirstRow M := by
    simpa [matrixCode] using codeMat_matrixCode (codexClearFirstRow M)
  rw [hdecode, codex_codeMat_fin8_outer, hw]
  have hb1 : Nat.testBit 1 1 = false := by decide
  have hb2 : Nat.testBit 1 2 = false := by decide
  ext i j
  fin_cases i <;>
    simp [codexClearFirstRow, codexFirstRow, outerMat, vecFromFin7,
      Pi.add_apply, hb1, hb2, CharTwo.add_self_eq_zero,
      add_assoc, add_comm, add_left_comm]

lemma codex_direction_action (u : Fin 7) (v : Fin 8) :
    actionA (codeMat (codexDirectionPCode u)) (1 : Mat3)
        (outerMat (vecFromFin7 u) (codexVecFromFin8 v)) =
      outerMat (vecFromFin7 0) (codexVecFromFin8 v) := by
  have h273 : (codeMat 273 : Mat3) = 1 := by decide
  have h := codex_direction_normalization_matrix u v
  simpa [actionA, h273] using h

def codexDoublePreimageW (P1 P2 Q2 : Mat3) (W : Submodule F2 Mat3) :
    Submodule F2 Mat3 :=
  actionW P1⁻¹ (1 : Mat3) (actionW P2⁻¹ Q2⁻¹ W)

lemma codex_double_preimage_lb {P1 P2 Q2 : Mat3}
    [Invertible P1] [Invertible P2] [Invertible Q2]
    {W : Submodule F2 Mat3} {n : Nat} (hW : QuotientRankAtLeast W n) :
    QuotientRankAtLeast (codexDoublePreimageW P1 P2 Q2 W) n := by
  letI : Invertible (1 : Mat3) := invertibleOne
  letI : Invertible (P1⁻¹ : Mat3) :=
    { invOf := P1
      invOf_mul_self := mul_inv_of_invertible P1
      mul_invOf_self := inv_mul_of_invertible P1 }
  letI : Invertible (P2⁻¹ : Mat3) :=
    { invOf := P2
      invOf_mul_self := mul_inv_of_invertible P2
      mul_invOf_self := inv_mul_of_invertible P2 }
  letI : Invertible (Q2⁻¹ : Mat3) :=
    { invOf := Q2
      invOf_mul_self := mul_inv_of_invertible Q2
      mul_invOf_self := inv_mul_of_invertible Q2 }
  exact quotientRankAtLeast_action (P := P1⁻¹) (Q := (1 : Mat3))
    (quotientRankAtLeast_action (P := P2⁻¹) (Q := Q2⁻¹) hW)

lemma codex_mem_double_preimage {P1 P2 Q2 : Mat3}
    [Invertible P1] [Invertible P2] [Invertible Q2]
    {W : Submodule F2 Mat3} {M : Mat3}
    (hM : actionA P2 Q2 (actionA P1 1 M) ∈ W) :
    M ∈ codexDoublePreimageW P1 P2 Q2 W := by
  letI : Invertible (1 : Mat3) := invertibleOne
  letI : Invertible (P1⁻¹ : Mat3) :=
    { invOf := P1
      invOf_mul_self := mul_inv_of_invertible P1
      mul_invOf_self := inv_mul_of_invertible P1 }
  letI : Invertible (P2⁻¹ : Mat3) :=
    { invOf := P2
      invOf_mul_self := mul_inv_of_invertible P2
      mul_invOf_self := inv_mul_of_invertible P2 }
  letI : Invertible (Q2⁻¹ : Mat3) :=
    { invOf := Q2
      invOf_mul_self := mul_inv_of_invertible Q2
      mul_invOf_self := inv_mul_of_invertible Q2 }
  unfold codexDoublePreimageW
  apply Submodule.mem_map.mpr
  refine ⟨actionA P1 1 M, ?_, ?_⟩
  · apply Submodule.mem_map.mpr
    refine ⟨actionA P2 Q2 (actionA P1 1 M), hM, actionA_inv_actionA _⟩
  · change actionA P1⁻¹ 1 (actionA P1 1 M) = M
    simpa only [inv_one] using
      (actionA_inv_actionA (P := P1) (Q := (1 : Mat3)) M)

/-- A degenerate standardized coset cannot contain the high-factor image of a
length-20 decomposition: it has at most six high labels and no rank-three
labels, while split rank requires excess at least seven. -/
theorem codex_degenerate_image_impossible
    (FP : FinitePremises) (D : TensorEntryDecomp 20)
    (q : Fin 512) (hq : residualRank q.val ≤ 1)
    (Φ : Mat3 → Mat3)
    (hΦrank : ∀ M : Mat3, (Φ M).rank = M.rank)
    (hΦinj : Function.Injective Φ)
    (hnorm : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
      ∃ v : Fin 8, Φ (D.A t) = codeMat (Nat.xor q.val v.val)) : False := by
  classical
  have hex : ∀ t : Fin 20, ∃ v : Fin 8,
      2 ≤ (D.A t).rank →
        Φ (D.A t) = codeMat (Nat.xor q.val v.val) := by
    intro t
    by_cases ht : 2 ≤ (D.A t).rank
    · rcases hnorm t ht with ⟨v, hv⟩
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => False.elim (ht h)⟩
  choose lab hlab using hex
  let H : Finset (Fin 20) := Finset.univ.filter fun t => 2 ≤ (D.A t).rank
  let L : Finset (Fin 8) := H.image lab
  have hHcard : H.card = highCount (fun t => (D.A t).rank) := by
    simp [H, highCount]
  have hlabInj : Set.InjOn lab (H : Set (Fin 20)) := by
    intro s hs t ht heq
    have hsHigh : 2 ≤ (D.A s).rank := (Finset.mem_filter.mp hs).2
    have htHigh : 2 ≤ (D.A t).rank := (Finset.mem_filter.mp ht).2
    have hphi : Φ (D.A s) = Φ (D.A t) := by
      rw [hlab s hsHigh, hlab t htHigh, heq]
    have hmat := hΦinj hphi
    exact A_line_distinct_from_line_bounds FP D s t
      (codex_high_ne_zero _ hsHigh) (codex_high_ne_zero _ htHigh) (by rw [hmat])
  have hLcard : L.card = H.card := Finset.card_image_of_injOn hlabInj
  let G : Finset (Fin 8) := Finset.univ.filter fun v =>
    2 ≤ rankCode (Nat.xor q.val v.val)
  have hLG : L ⊆ G := by
    intro v hvL
    rcases Finset.mem_image.mp hvL with ⟨t, htH, htv⟩
    have htHigh : 2 ≤ (D.A t).rank := (Finset.mem_filter.mp htH).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    let c : Fin 512 :=
      ⟨Nat.xor q.val v.val,
        by
          simpa using (Nat.xor_lt_two_pow
            (show q.val < 2 ^ 9 by simpa using q.isLt)
            (show v.val < 2 ^ 9 by omega))⟩
    change 2 ≤ rankCode c.val
    rw [← rank_eq_rankCode_code c]
    have hphiHigh : 2 ≤ (Φ (D.A t)).rank := by rw [hΦrank]; exact htHigh
    rw [hlab t htHigh, htv] at hphiHigh
    simpa [c] using hphiHigh
  have hhighCap : highCount (fun t => (D.A t).rank) ≤ 6 := by
    have hcardLG := Finset.card_le_card hLG
    have hGexcess : G.card = cosetExcess q.val := by
      simpa [G] using codex_degenerate_high_label_card_eq_excess q hq
    have hExcess : cosetExcess q.val < 7 :=
      codex_degenerate_branch_excess_lt_seven q hq
    have hGcap : G.card ≤ 6 := by omega
    omega
  have hnoThree : ∀ t : Fin 20, (D.A t).rank ≠ 3 := by
    intro t ht3
    have htHigh : 2 ≤ (D.A t).rank := by omega
    rcases hnorm t htHigh with ⟨v, hv⟩
    let c : Fin 512 :=
      ⟨Nat.xor q.val v.val,
        by
          simpa using (Nat.xor_lt_two_pow
            (show q.val < 2 ^ 9 by simpa using q.isLt)
            (show v.val < 2 ^ 9 by omega))⟩
    have hc3 : rankCode c.val = 3 := by
      rw [← rank_eq_rankCode_code c]
      have hp3 : (Φ (D.A t)).rank = 3 := by rw [hΦrank, ht3]
      rw [hv] at hp3
      simpa [c] using hp3
    have hcle := codex_degenerate_coset_rank_le_two q hq v
    change rankCode c.val ≤ 2 at hcle
    omega
  have hthreeZero : rankThreeCount (fun t => (D.A t).rank) = 0 := by
    simp [rankThreeCount, hnoThree]
  have hshort : ∀ m : Nat, m < 20 → TensorEntryDecomp m → False :=
    fun m hm E => no_decomp_below_20_from_finitePremises FP m hm E
  have hA0 : ∀ t : Fin 20, D.A t ≠ 0 :=
    codex_nonzero_A_of_noDecompBelow D hshort
  have hsumFormula := rank_sum_eq_card_plus_high_plus_rankThree
    (fun t : Fin 20 => (D.A t).rank)
    (fun t => codex_matrix_rank_positive (D.A t) (hA0 t))
    (fun t => codex_matrix_rank_le_three (D.A t))
  have hsplit := split_rank_bound_from_entrywise D
  have hcard : Fintype.card (Fin 20) = 20 := by decide
  omega

theorem profile_forcing_from_affine_left_coset_codex
    (FP : FinitePremises) (D : TensorEntryDecomp 20)
    (p : Mat3) (u : I3 → F2) (hu : u ≠ 0)
    (hcoset : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
      ∃ v : I3 → F2, D.A t = p + outerMat u v) :
    ∃ t s : Fin 20,
      t ≠ s ∧ (D.A t).det ≠ 0 ∧ (D.A s).det ≠ 0 ∧
      (∑ x : Fin 20, (D.A x).rank) = Fintype.card SIdx ∧
      (∀ x : Fin 20, D.B x ≠ 0) ∧ (∀ x : Fin 20, D.C x ≠ 0) := by
  classical
  obtain ⟨ku, hku⟩ := vec_has_fin7 u hu
  let P1 : Mat3 := codeMat (codexDirectionPCode ku)
  have hP1det : P1.det ≠ 0 := by
    simpa [P1] using codex_direction_det_ne_zero ku
  letI : Invertible P1 :=
    Matrix.invertibleOfIsUnitDet P1 (isUnit_iff_ne_zero.mpr hP1det)
  letI : Invertible (1 : Mat3) := invertibleOne
  let base : Mat3 := actionA P1 1 p
  let base0 : Mat3 := codexClearFirstRow base
  let q : Fin 512 := matrixCode base0
  have hqFirst : q.val &&& 7 = 0 := by
    simpa [q, matrixCode, base0] using codex_clear_first_row_code base
  have hfirst : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
      ∃ w : Fin 8, actionA P1 1 (D.A t) =
        codeMat (Nat.xor q.val w.val) := by
    intro t ht
    rcases hcoset t ht with ⟨v, hAt⟩
    obtain ⟨iv, hiv⟩ := codex_vec_has_fin8 v
    have houter : actionA P1 1 (outerMat u v) =
        outerMat (vecFromFin7 0) v := by
      rw [← hku, ← hiv]
      exact codex_direction_action ku iv
    obtain ⟨w, hw⟩ := codex_clear_coset_as_code base v
    refine ⟨w, ?_⟩
    calc
      actionA P1 1 (D.A t) = actionA P1 1 (p + outerMat u v) := by rw [hAt]
      _ = base + actionA P1 1 (outerMat u v) := by rw [actionA_add]
      _ = base + outerMat (vecFromFin7 0) v := by rw [houter]
      _ = codeMat (Nat.xor q.val w.val) := by
        change base + outerMat (vecFromFin7 0) v =
          codeMat (Nat.xor (matrixCodeNat base0) w.val)
        simpa [base0] using hw
  have hqle : residualRank q.val ≤ 2 :=
    codex_zero_first_row_residual_rank_le_two q hqFirst
  by_cases hqDeg : residualRank q.val ≤ 1
  · exact False.elim (codex_degenerate_image_impossible FP D q hqDeg
      (actionA P1 1) (fun M => ah_action_rank_eq P1 1 M)
      (fun X Y hXY => by
        have h := congrArg (pullbackA P1 1) hXY
        simpa only [pullbackA_actionA] using h)
      hfirst)
  · have hqRank : residualRank q.val = 2 := by omega
    let P2 : Mat3 := codeMat 161
    let Q2 : Mat3 := codeMat (codexResidualQCode q)
    have hP2det : P2.det ≠ 0 := by decide
    have hQ2det : Q2.det ≠ 0 := by
      simpa [Q2] using codex_residual_det_ne_zero q hqFirst hqRank
    letI : Invertible P2 :=
      Matrix.invertibleOfIsUnitDet P2 (isUnit_iff_ne_zero.mpr hP2det)
    letI : Invertible Q2 :=
      Matrix.invertibleOfIsUnitDet Q2 (isUnit_iff_ne_zero.mpr hQ2det)
    have hQ2inv : Q2.transpose⁻¹ =
        (codeMat (codexResidualQInvCode q)).transpose := by
      apply Matrix.inv_eq_right_inv
      have hdata := (codex_residual_inverse_data q hqFirst hqRank).2
      calc
        Q2.transpose * (codeMat (codexResidualQInvCode q)).transpose =
            (codeMat (codexResidualQInvCode q) * Q2).transpose :=
              (Matrix.transpose_mul _ _).symm
        _ = (1 : Mat3).transpose := by rw [hdata]
        _ = 1 := Matrix.transpose_one
    let Φ : Mat3 → Mat3 := fun M => actionA P2 Q2 (actionA P1 1 M)
    let U : Fin 14 → Submodule F2 Mat3 := fun i =>
      codexDoublePreimageW P1 P2 Q2 (affineHyperplane i)
    have hΦrank : ∀ M : Mat3, (Φ M).rank = M.rank := by
      intro M
      calc
        (Φ M).rank = (actionA P1 1 M).rank := ah_action_rank_eq P2 Q2 _
        _ = M.rank := ah_action_rank_eq P1 1 M
    have hΦinj : Function.Injective Φ := by
      intro X Y hXY
      have h2 := congrArg (pullbackA P2 Q2) hXY
      simp only [Φ, pullbackA_actionA] at h2
      have h1 := congrArg (pullbackA P1 1) h2
      simpa only [pullbackA_actionA] using h1
    have hU : ∀ i : Fin 14, QuotientRankAtLeast (U i) 17 := by
      intro i
      exact codex_double_preimage_lb (FP.affine_hyperplane_lb17 i)
    have hΦmem : ∀ (i : Fin 14) (M : Mat3),
        Φ M ∈ affineHyperplane i → M ∈ U i := by
      intro i M hM
      exact codex_mem_double_preimage hM
    have hnorm : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
        ∃ w : Fin 8, Φ (D.A t) = codeMat (Nat.xor 272 w.val) := by
      intro t ht
      rcases hfirst t ht with ⟨v, hv⟩
      rcases codex_rank2_residual_matrix_normalization q hqFirst hqRank v with
        ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [show Φ (D.A t) = actionA P2 Q2 (actionA P1 1 (D.A t)) by rfl, hv]
      unfold actionA
      rw [hQ2inv]
      simpa [P2] using hw
    rcases normalized_image_high_and_rankThree_caps_codex FP D Φ U
      hΦrank hΦinj hU hΦmem hnorm with ⟨hhigh, hthree⟩
    exact profile_endpoint_of_caps_codex FP D hhigh hthree

def codexTransposeEntryDecomp {r : Nat} (D : TensorEntryDecomp r) :
    TensorEntryDecomp r where
  A := fun t => (D.A t).transpose
  B := D.C
  C := D.B
  entry_identity := by
    intro a b c
    have hentry : tensorEntry a b c = tensorEntry (a.2, a.1) c b := by
      simp only [tensorEntry]
      congr 1
      aesop
    rw [hentry, D.entry_identity]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Matrix.transpose_apply]
    ring

/-- Full replacement for the root profile hole. -/
theorem profile_forcing_from_finitePremises_codex
    (FP : FinitePremises) (D : TensorEntryDecomp 20) :
    ∃ t s : Fin 20,
      t ≠ s ∧ (D.A t).det ≠ 0 ∧ (D.A s).det ≠ 0 ∧
      (∑ x : Fin 20, (D.A x).rank) = Fintype.card SIdx ∧
      (∀ x : Fin 20, D.B x ≠ 0) ∧ (∀ x : Fin 20, D.C x ≠ 0) := by
  rcases high_factors_affine_row_or_column_coset_codex FP D with hleft | hright
  · rcases hleft with ⟨p, u, hu, hcoset⟩
    exact profile_forcing_from_affine_left_coset_codex FP D p u hu hcoset
  · rcases hright with ⟨p, v, hv, hcoset⟩
    let DT := codexTransposeEntryDecomp D
    have htransCoset : ∀ t : Fin 20, 2 ≤ (DT.A t).rank →
        ∃ u : I3 → F2, DT.A t = p.transpose + outerMat v u := by
      intro t ht
      have ht' : 2 ≤ (D.A t).rank := by
        change 2 ≤ (D.A t).transpose.rank at ht
        simpa only [Matrix.rank_transpose] using ht
      rcases hcoset t ht' with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      change (D.A t).transpose = p.transpose + outerMat v u
      rw [hu, Matrix.transpose_add]
      congr 1
      ext i j
      simp [outerMat, mul_comm]
    rcases profile_forcing_from_affine_left_coset_codex FP DT p.transpose v hv
      htransCoset with ⟨t, s, hts, hAt, hAs, hsum, hB, hC⟩
    refine ⟨t, s, hts, ?_, ?_, ?_, ?_, ?_⟩
    · change (D.A t).transpose.det ≠ 0 at hAt
      simpa only [Matrix.det_transpose] using hAt
    · change (D.A s).transpose.det ≠ 0 at hAs
      simpa only [Matrix.det_transpose] using hAs
    · change (∑ x : Fin 20, (D.A x).transpose.rank) = Fintype.card SIdx at hsum
      simpa only [Matrix.rank_transpose] using hsum
    · change ∀ x : Fin 20, D.B x ≠ 0 at hC
      exact hC
    · change ∀ x : Fin 20, D.C x ≠ 0 at hB
      exact hB

end QiushiMatmul
end
