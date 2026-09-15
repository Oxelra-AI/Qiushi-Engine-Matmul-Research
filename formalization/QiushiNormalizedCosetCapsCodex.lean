import QiushiHuaAffineCosetCodex
import QiushiProfileEndpointCodex
import QiushiCodeSpanBridgeCore

/-!
Occupation/cap argument inside the normalized affine coset
`272 + spanCodes [4,2,1]`.  This closes the symbolic layer between a
normalized-coset hypothesis and the already checked profile endpoint.
-/

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

def codexAffineBasis (i : Fin 14) : List Nat :=
  match i.val with
  | 0 => [272,4,2] | 1 => [273,4,2]
  | 2 => [272,4,1] | 3 => [274,4,1]
  | 4 => [272,4,3] | 5 => [273,4,3]
  | 6 => [272,2,1] | 7 => [276,2,1]
  | 8 => [272,5,2] | 9 => [273,5,2]
  | 10 => [272,6,1] | 11 => [274,6,1]
  | 12 => [272,5,3] | _ => [273,5,3]

def codexAffineLabelPlane (i : Fin 14) : Finset (Fin 8) :=
  Finset.univ.filter fun v =>
    spanContainsCode (codexAffineBasis i) (Nat.xor 272 v.val) = true

theorem codex_affine_label_plane_card : ∀ i : Fin 14,
    (codexAffineLabelPlane i).card = 4 := by
  decide +revert

theorem codex_ag32_five_contains_affine_plane : ∀ L : Finset (Fin 8),
    5 ≤ L.card → ∃ i : Fin 14, codexAffineLabelPlane i ⊆ L := by
  decide +revert

lemma codex_affineHyperplane_eq_basis (i : Fin 14) :
    affineHyperplane i = spanCodes (codexAffineBasis i) := by
  fin_cases i <;> rfl

lemma codex_label_matrix_mem_affineHyperplane (i : Fin 14) (v : Fin 8)
    (hv : v ∈ codexAffineLabelPlane i) :
    codeMat (Nat.xor 272 v.val) ∈ affineHyperplane i := by
  rw [codex_affineHyperplane_eq_basis]
  apply spanContainsCode_implies_mem_spanCodes
  exact (Finset.mem_filter.mp hv).2

theorem codex_normalized_rank_three_labels : ∀ v : Fin 8,
    rankCode (Nat.xor 272 v.val) = 3 ↔
      v ∈ codexAffineLabelPlane (1 : Fin 14) := by
  decide +revert

lemma codex_occurrence_cap_three (P : FinitePremises)
    (D : TensorEntryDecomp 20) (i : Fin 14) :
    (Finset.univ.filter fun t : Fin 20 => D.A t ∈ affineHyperplane i).card ≤ 3 := by
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) 20 :=
    entrywise_to_quotient D ⊥
  have hocc : (killSet D0 (affineHyperplane i)).card ≤ 20 - 17 :=
    occupation_inequality (show (⊥ : Submodule F2 Mat3) ≤ affineHyperplane i from bot_le)
      D0 (P.affine_hyperplane_lb17 i) (by omega)
  simpa [killSet, D0, entrywise_to_quotient] using hocc

lemma codex_occurrence_cap_three_of_lb (D : TensorEntryDecomp 20)
    (W : Submodule F2 Mat3) (hW : QuotientRankAtLeast W 17) :
    (Finset.univ.filter fun t : Fin 20 => D.A t ∈ W).card ≤ 3 := by
  let D0 : QuotientTensorDecomp (⊥ : Submodule F2 Mat3) 20 :=
    entrywise_to_quotient D ⊥
  have hocc : (killSet D0 W).card ≤ 20 - 17 :=
    occupation_inequality (show (⊥ : Submodule F2 Mat3) ≤ W from bot_le)
      D0 hW (by omega)
  simpa [killSet, D0, entrywise_to_quotient] using hocc

/-- In the normalized coset, the fourteen quotient bounds and the finite
`AG(3,2)` cap force at most four high factors; the particular rank-three
label plane forces at most three invertible factors. -/
theorem normalized_image_high_and_rankThree_caps_codex
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (Φ : Mat3 → Mat3) (U : Fin 14 → Submodule F2 Mat3)
    (hΦrank : ∀ M : Mat3, (Φ M).rank = M.rank)
    (hΦinj : Function.Injective Φ)
    (hU : ∀ i : Fin 14, QuotientRankAtLeast (U i) 17)
    (hΦmem : ∀ (i : Fin 14) (M : Mat3),
      Φ M ∈ affineHyperplane i → M ∈ U i)
    (hnorm : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
      ∃ v : Fin 8, Φ (D.A t) = codeMat (Nat.xor 272 v.val)) :
    highCount (fun t => (D.A t).rank) ≤ 4 ∧
      rankThreeCount (fun t => (D.A t).rank) ≤ 3 := by
  classical
  have hex : ∀ t : Fin 20, ∃ v : Fin 8,
      2 ≤ (D.A t).rank → Φ (D.A t) = codeMat (Nat.xor 272 v.val) := by
    intro t
    by_cases ht : 2 ≤ (D.A t).rank
    · rcases hnorm t ht with ⟨v, hv⟩
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => False.elim (ht h)⟩
  choose lab hlab using hex
  let H : Finset (Fin 20) := Finset.univ.filter fun t => 2 ≤ (D.A t).rank
  have hHcard : H.card = highCount (fun t => (D.A t).rank) := by
    simp [H, highCount]
  have hlabInj : Set.InjOn lab (H : Set (Fin 20)) := by
    intro s hs t ht heq
    have hsHigh : 2 ≤ (D.A s).rank := (Finset.mem_filter.mp hs).2
    have htHigh : 2 ≤ (D.A t).rank := (Finset.mem_filter.mp ht).2
    have hmat : D.A s = D.A t := by
      apply hΦinj
      rw [hlab s hsHigh, hlab t htHigh, heq]
    exact A_line_distinct_from_line_bounds P D s t
      (codex_high_ne_zero _ hsHigh) (codex_high_ne_zero _ htHigh) (by rw [hmat])
  have hhighCap : highCount (fun t => (D.A t).rank) ≤ 4 := by
    by_contra hnot
    push Not at hnot
    let L : Finset (Fin 8) := H.image lab
    have hLcard : L.card = H.card :=
      Finset.card_image_of_injOn hlabInj
    obtain ⟨i, hi⟩ := codex_ag32_five_contains_affine_plane L (by omega)
    let K : Finset (Fin 20) := H.filter fun t => lab t ∈ codexAffineLabelPlane i
    have hplaneImage : codexAffineLabelPlane i ⊆ K.image lab := by
      intro v hv
      have hvL : v ∈ L := hi hv
      rcases Finset.mem_image.mp hvL with ⟨t, htH, htv⟩
      apply Finset.mem_image.mpr
      refine ⟨t, Finset.mem_filter.mpr ⟨htH, ?_⟩, htv⟩
      simpa [htv] using hv
    have hKfour : 4 ≤ K.card := by
      have h1 := Finset.card_le_card hplaneImage
      have h2 : (K.image lab).card ≤ K.card := Finset.card_image_le
      rw [codex_affine_label_plane_card i] at h1
      omega
    have hKocc : K ⊆ Finset.univ.filter (fun t : Fin 20 => D.A t ∈ U i) := by
      intro t htK
      have htData := Finset.mem_filter.mp htK
      have htHigh : 2 ≤ (D.A t).rank := (Finset.mem_filter.mp htData.1).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply hΦmem
      rw [hlab t htHigh]
      exact codex_label_matrix_mem_affineHyperplane i (lab t) htData.2
    have hKthree := le_trans (Finset.card_le_card hKocc)
      (codex_occurrence_cap_three_of_lb D (U i) (hU i))
    omega
  have hthreeCap : rankThreeCount (fun t => (D.A t).rank) ≤ 3 := by
    let R : Finset (Fin 20) := Finset.univ.filter fun t => (D.A t).rank = 3
    have hRcard : R.card = rankThreeCount (fun t => (D.A t).rank) := by
      simp [R, rankThreeCount]
    have hRocc : R ⊆ Finset.univ.filter
        (fun t : Fin 20 => D.A t ∈ U (1 : Fin 14)) := by
      intro t htR
      have htRank : (D.A t).rank = 3 := (Finset.mem_filter.mp htR).2
      have htHigh : 2 ≤ (D.A t).rank := by omega
      have hnormt := hlab t htHigh
      have htRankPhi : (Φ (D.A t)).rank = 3 := by rw [hΦrank, htRank]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply hΦmem
      rw [hnormt]
      apply codex_label_matrix_mem_affineHyperplane
      apply (codex_normalized_rank_three_labels (lab t)).mp
      let c : Fin 512 :=
        ⟨Nat.xor 272 (lab t).val,
          by
            simpa using (Nat.xor_lt_two_pow (show 272 < 2 ^ 9 by decide)
              (show (lab t).val < 2 ^ 9 by omega))⟩
      change rankCode c.val = 3
      rw [← rank_eq_rankCode_code c]
      rw [hnormt] at htRankPhi
      simpa [c] using htRankPhi
    have hRthree := le_trans (Finset.card_le_card hRocc)
      (codex_occurrence_cap_three_of_lb D (U (1 : Fin 14)) (hU 1))
    omega
  exact ⟨hhighCap, hthreeCap⟩

theorem normalized_coset_high_and_rankThree_caps_codex
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (hnorm : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
      ∃ v : Fin 8, D.A t = codeMat (Nat.xor 272 v.val)) :
    highCount (fun t => (D.A t).rank) ≤ 4 ∧
      rankThreeCount (fun t => (D.A t).rank) ≤ 3 := by
  exact normalized_image_high_and_rankThree_caps_codex P D id affineHyperplane
    (fun _ => rfl) Function.injective_id
    P.affine_hyperplane_lb17 (fun _ _ h => h) hnorm

theorem profile_forcing_from_normalized_coset_codex
    (P : FinitePremises) (D : TensorEntryDecomp 20)
    (hnorm : ∀ t : Fin 20, 2 ≤ (D.A t).rank →
      ∃ v : Fin 8, D.A t = codeMat (Nat.xor 272 v.val)) :
    ∃ t s : Fin 20,
      t ≠ s ∧ (D.A t).det ≠ 0 ∧ (D.A s).det ≠ 0 ∧
      (∑ u : Fin 20, (D.A u).rank) = Fintype.card SIdx ∧
      (∀ u : Fin 20, D.B u ≠ 0) ∧ (∀ u : Fin 20, D.C u ≠ 0) := by
  rcases normalized_coset_high_and_rankThree_caps_codex P D hnorm with
    ⟨hhigh, hthree⟩
  exact profile_endpoint_of_caps_codex P D hhigh hthree

end QiushiMatmul
end
