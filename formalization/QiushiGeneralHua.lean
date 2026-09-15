import QiushiHuaSunflower
import QiushiRankBridge
import QiushiAllHighRankCodeBridge
import QiushiCodeSpanBridgeCore

/-!
# Hua confinement for arbitrary finite matrix sets

This is the matrix-set statement of reports/en/main.tex, Lemma `lem:coset`.
The hypothesis uses actual `Matrix.rank`, not the finite code rank.  No tensor
decomposition or finite-premise certificate is required.
-/

open Matrix

namespace QiushiMatmul

private lemma general_hua_outerCode_lt (u v : Fin 7) : outerCode u v < 2 ^ 9 := by
  decide +revert

-- The rank-one decoder used by the profile proof, without importing its
-- decomposition-specific all-high-plane certificate chain.
private lemma general_hua_rank_one_factor (M : Mat3) (hM0 : M ≠ 0)
    (hM : M.rank ≤ 1) : ∃ f : RkOneFact, M = codeMat (outerCode f.u f.v) := by
  have hcode : rankCode (matrixCode M).val ≤ 1 := by
    simpa [matrixCode] using (rank_eq_rankCode M) ▸ hM
  rcases ah_rankCode_le_one_cases (matrixCode M) hcode with hc | ⟨u, v, hc⟩
  · exfalso
    apply hM0
    have hdecode : codeMat (matrixCode M).val = M := codeMat_matrixCode M
    rw [hc] at hdecode
    have hz : (codeMat 0 : Mat3) = 0 := by decide
    simpa [hz] using hdecode.symm
  · refine ⟨⟨u, v⟩, ?_⟩
    rw [← hc]
    exact (codeMat_matrixCode M).symm

private lemma general_hua_cancel_base (p X : Mat3) : X = p + (X + p) := by
  have hpp : p + p = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  calc
    X = X + (p + p) := by rw [hpp, add_zero]
    _ = p + (X + p) := by abel

private lemma general_hua_two_differences (p X Y : Mat3) :
    (X + p) + (Y + p) = X + Y := by
  have hpp : p + p = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  calc
    (X + p) + (Y + p) = (X + Y) + (p + p) := by abel
    _ = X + Y := by rw [hpp, add_zero]

/-- An arbitrary set of at least four distinct binary 3-by-3 matrices with
rank-one pairwise differences lies in an affine column or row coset.
The fixed direction is nonzero; the varying vector may be zero at the base.
-/
theorem finset_affine_row_or_column_coset
    (H : Finset Mat3) (hcard : 4 ≤ H.card)
    (hpair : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (a - b).rank = 1) :
    (∃ p : Mat3, ∃ u : I3 → F2, u ≠ 0 ∧
      ∀ a ∈ H, ∃ v : I3 → F2, a = p + outerMat u v) ∨
    (∃ p : Mat3, ∃ v : I3 → F2, v ≠ 0 ∧
      ∀ a ∈ H, ∃ u : I3 → F2, a = p + outerMat u v) := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  let S := H.erase p
  have hrank (a : Mat3) (ha : a ∈ H) (b : Mat3) (hb : b ∈ H)
      (hne : a ≠ b) : (a + b).rank ≤ 1 := by
    have hsub : a - b = a + b := by
      ext i j
      exact CharTwo.sub_eq_add _ _
    rw [← hsub, hpair a ha b hb hne]
  have hfactor (a : Mat3) (ha : a ∈ S) :
      ∃ f : RkOneFact, a + p = codeMat (outerCode f.u f.v) := by
    have haH : a ∈ H := (Finset.mem_erase.mp ha).2
    have hne : a ≠ p := (Finset.mem_erase.mp ha).1
    apply general_hua_rank_one_factor
    · intro hz
      apply hne
      calc
        a = p + (a + p) := general_hua_cancel_base p a
        _ = p := by rw [hz, add_zero]
    · exact hrank a haH p hp hne
  have hex : ∀ a : Mat3, ∃ f : RkOneFact,
      a ∈ S → a + p = codeMat (outerCode f.u f.v) := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨f, hf⟩ := hfactor a ha
      exact ⟨f, fun _ => hf⟩
    · exact ⟨⟨0, 0⟩, fun h => False.elim (ha h)⟩
  choose f hf using hex
  let fam : List RkOneFact := S.toList.map f
  have hfam : PairwiseRk1 fam := by
    intro x hx y hy
    obtain ⟨a, haList, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hbList, rfl⟩ := List.mem_map.mp hy
    have ha : a ∈ S := by simpa using haList
    have hb : b ∈ S := by simpa using hbList
    by_cases heq : f a = f b
    · exact Or.inl heq
    · apply Or.inr
      have hab : a ≠ b := fun h => heq (congrArg f h)
      let c : Fin 512 :=
        ⟨Nat.xor (outerCode (f a).u (f a).v) (outerCode (f b).u (f b).v),
          by simpa using (Nat.xor_lt_two_pow
            (general_hua_outerCode_lt (f a).u (f a).v)
            (general_hua_outerCode_lt (f b).u (f b).v))⟩
      have hmat : codeMat c.val = a + b := by
        change codeMat (Nat.xor (outerCode (f a).u (f a).v)
          (outerCode (f b).u (f b).v)) = a + b
        rw [codeMat_xor, ← hf a ha, ← hf b hb]
        exact general_hua_two_differences p a b
      change rankCode c.val ≤ 1
      rw [← rank_eq_rankCode_code c, hmat]
      exact hrank a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2 hab
  have hmem (a : Mat3) (ha : a ∈ S) : f a ∈ fam :=
    List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩
  rcases family_confinement fam hfam with ⟨u, hu⟩ | ⟨v, hv⟩
  · refine Or.inl ⟨p, vecFromFin7 u, vecFromFin7_ne_zero u, ?_⟩
    intro a ha
    by_cases hap : a = p
    · subst a
      refine ⟨0, ?_⟩
      ext i j
      simp [outerMat]
    · have haS : a ∈ S := Finset.mem_erase.mpr ⟨hap, ha⟩
      refine ⟨vecFromFin7 (f a).v, ?_⟩
      calc
        a = p + (a + p) := general_hua_cancel_base p a
        _ = p + codeMat (outerCode (f a).u (f a).v) := by rw [hf a haS]
        _ = p + outerMat (vecFromFin7 u) (vecFromFin7 (f a).v) := by
          rw [codeMat_outerCode_eq, hu (f a) (hmem a haS)]
  · refine Or.inr ⟨p, vecFromFin7 v, vecFromFin7_ne_zero v, ?_⟩
    intro a ha
    by_cases hap : a = p
    · subst a
      refine ⟨0, ?_⟩
      ext i j
      simp [outerMat]
    · have haS : a ∈ S := Finset.mem_erase.mpr ⟨hap, ha⟩
      refine ⟨vecFromFin7 (f a).u, ?_⟩
      calc
        a = p + (a + p) := general_hua_cancel_base p a
        _ = p + codeMat (outerCode (f a).u (f a).v) := by rw [hf a haS]
        _ = p + outerMat (vecFromFin7 (f a).u) (vecFromFin7 v) := by
          rw [codeMat_outerCode_eq, hv (f a) (hmem a haS)]

/-- Set form of the report's Hua lemma.  Every subset of `Mat3` is finite,
so no additional finiteness hypothesis is needed. -/
theorem set_affine_row_or_column_coset
    (H : Set Mat3) (hcard : 4 ≤ H.ncard)
    (hpair : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → (a - b).rank = 1) :
    (∃ p : Mat3, ∃ u : I3 → F2, u ≠ 0 ∧
      ∀ a ∈ H, ∃ v : I3 → F2, a = p + outerMat u v) ∨
    (∃ p : Mat3, ∃ v : I3 → F2, v ≠ 0 ∧
      ∀ a ∈ H, ∃ u : I3 → F2, a = p + outerMat u v) := by
  classical
  have hc : 4 ≤ H.toFinite.toFinset.card := by
    rwa [← Set.ncard_eq_toFinset_card H H.toFinite]
  have hp : ∀ a ∈ H.toFinite.toFinset, ∀ b ∈ H.toFinite.toFinset,
      a ≠ b → (a - b).rank = 1 := by
    simpa only [Set.Finite.mem_toFinset] using hpair
  simpa only [Set.Finite.mem_toFinset] using
    finset_affine_row_or_column_coset H.toFinite.toFinset hc hp

end QiushiMatmul
