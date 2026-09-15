import QiushiAllHighPlaneOrbit
import QiushiHuaSunflower
import QiushiRankBridge
import QiushiALineDistinct

open Matrix BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
namespace QiushiMatmul

set_option maxRecDepth 200000
set_option maxHeartbeats 24000000

lemma codex_outerCode_lt (u v : Fin 7) : outerCode u v < 2 ^ 9 := by
  decide +revert

lemma codex_high_ne_zero (M : Mat3) (hM : 2 ≤ M.rank) : M ≠ 0 := by
  intro h
  subst M
  simpa using hM

lemma codex_rank_one_factor (M : Mat3) (hM0 : M ≠ 0) (hM : M.rank ≤ 1) :
    ∃ f : RkOneFact, M = codeMat (outerCode f.u f.v) := by
  let c := matrixCode M
  have hcode : rankCode c.val ≤ 1 := by
    have hr := rank_eq_rankCode M
    simpa [c, matrixCode] using hr ▸ hM
  rcases ah_rankCode_le_one_cases c hcode with hc | ⟨u, v, hc⟩
  · exfalso
    apply hM0
    have hdecode : codeMat c.val = M := by
      simpa [c, matrixCode] using codeMat_matrixCode M
    rw [hc] at hdecode
    have hz : (codeMat 0 : Mat3) = 0 := by decide
    simpa [hz] using hdecode.symm
  · refine ⟨⟨u, v⟩, ?_⟩
    have hdecode : codeMat c.val = M := by
      simpa [c, matrixCode] using codeMat_matrixCode M
    rw [hc] at hdecode
    exact hdecode.symm

lemma codex_cancel_affine_base (p X : Mat3) : X = p + (X + p) := by
  have hpp : p + p = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  calc
    X = 0 + X := by rw [zero_add]
    _ = (p + p) + X := by rw [hpp]
    _ = p + (X + p) := by abel

lemma codex_two_affine_differences (p X Y : Mat3) :
    (X + p) + (Y + p) = X + Y := by
  have hpp : p + p = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero _
  calc
    (X + p) + (Y + p) = X + Y + (p + p) := by abel
    _ = X + Y := by rw [hpp, add_zero]

theorem high_factors_affine_row_or_column_coset_codex
    (P : FinitePremises) (D : TensorEntryDecomp 20) :
    (∃ p : Mat3, ∃ u : I3 → F2, u ≠ 0 ∧
      ∀ t : Fin 20, 2 ≤ (D.A t).rank →
        ∃ v : I3 → F2, D.A t = p + outerMat u v) ∨
    (∃ p : Mat3, ∃ v : I3 → F2, v ≠ 0 ∧
      ∀ t : Fin 20, 2 ≤ (D.A t).rank →
        ∃ u : I3 → F2, D.A t = p + outerMat u v) := by
  classical
  by_cases hsome : ∃ t : Fin 20, 2 ≤ (D.A t).rank
  · obtain ⟨t₀, ht₀⟩ := hsome
    let p := D.A t₀
    let S : Finset (Fin 20) := Finset.univ.filter fun t =>
      2 ≤ (D.A t).rank ∧ t ≠ t₀
    have hmatrix_ne (t : Fin 20) (ht : 2 ≤ (D.A t).rank) (hne : t ≠ t₀) :
        D.A t ≠ p := by
      intro heq
      have hline : Submodule.span F2 ({D.A t} : Set Mat3) =
          Submodule.span F2 ({D.A t₀} : Set Mat3) := by simpa [p, heq]
      have heqIndex := A_line_distinct_from_line_bounds P D t t₀
        (codex_high_ne_zero _ ht) (codex_high_ne_zero _ ht₀) hline
      exact hne heqIndex
    have hfactor (t : Fin 20) (htS : t ∈ S) :
        ∃ f : RkOneFact, D.A t + p = codeMat (outerCode f.u f.v) := by
      have htData : 2 ≤ (D.A t).rank ∧ t ≠ t₀ := by
        simpa [S] using (Finset.mem_filter.mp htS).2
      apply codex_rank_one_factor
      · intro hz
        have : D.A t = p := by
          calc
            D.A t = p + (D.A t + p) := codex_cancel_affine_base p (D.A t)
            _ = p + 0 := by rw [hz]
            _ = p := add_zero p
        exact hmatrix_ne t htData.1 htData.2 this
      · exact high_pair_difference_rank_le_one_from_plane_bounds
          P D t t₀ htData.2 htData.1 ht₀
    have hex : ∀ t : Fin 20, ∃ f : RkOneFact,
        t ∈ S → D.A t + p = codeMat (outerCode f.u f.v) := by
      intro t
      by_cases htS : t ∈ S
      · rcases hfactor t htS with ⟨f, hf⟩
        exact ⟨f, fun _ => hf⟩
      · exact ⟨⟨0, 0⟩, fun h => False.elim (htS h)⟩
    choose f hf using hex
    let fam : List RkOneFact := S.toList.map f
    have hfamPair : PairwiseRk1 fam := by
      intro x hx y hy
      rcases List.mem_map.mp hx with ⟨s, hsList, rfl⟩
      rcases List.mem_map.mp hy with ⟨t, htList, rfl⟩
      have hsS : s ∈ S := by simpa using hsList
      have htS : t ∈ S := by simpa using htList
      by_cases hfst : f s = f t
      · exact Or.inl hfst
      · apply Or.inr
        have hst : s ≠ t := by
          intro h
          subst t
          exact hfst rfl
        have hsHigh : 2 ≤ (D.A s).rank :=
          (Finset.mem_filter.mp hsS).2.1
        have htHigh : 2 ≤ (D.A t).rank :=
          (Finset.mem_filter.mp htS).2.1
        have hrank := high_pair_difference_rank_le_one_from_plane_bounds
          P D s t hst hsHigh htHigh
        let c : Fin 512 :=
          ⟨Nat.xor (outerCode (f s).u (f s).v) (outerCode (f t).u (f t).v),
            by
              simpa using (Nat.xor_lt_two_pow
                (codex_outerCode_lt (f s).u (f s).v)
                (codex_outerCode_lt (f t).u (f t).v))⟩
        have hmat : codeMat c.val = D.A s + D.A t := by
          change codeMat (Nat.xor (outerCode (f s).u (f s).v)
            (outerCode (f t).u (f t).v)) = D.A s + D.A t
          rw [codeMat_xor, ← hf s hsS, ← hf t htS]
          exact codex_two_affine_differences p (D.A s) (D.A t)
        have hrc : rankCode c.val ≤ 1 := by
          rw [← rank_eq_rankCode_code c, hmat]
          exact hrank
        simpa [c] using hrc
    rcases family_confinement fam hfamPair with hrow | hcol
    · rcases hrow with ⟨u₀, hu₀⟩
      exact Or.inl ⟨p, vecFromFin7 u₀, vecFromFin7_ne_zero u₀, fun t ht => by
        by_cases hEq : t = t₀
        · subst t
          refine ⟨0, ?_⟩
          simp only [p, add_eq_left]
          ext i j
          simp [outerMat]
        · have htS : t ∈ S := by simp [S, ht, hEq]
          have hmem : f t ∈ fam := by
            apply List.mem_map.mpr
            exact ⟨t, by simpa using htS, rfl⟩
          have hu : (f t).u = u₀ := hu₀ (f t) hmem
          refine ⟨vecFromFin7 (f t).v, ?_⟩
          calc
            D.A t = p + (D.A t + p) := codex_cancel_affine_base p (D.A t)
            _ = p + codeMat (outerCode (f t).u (f t).v) := by rw [hf t htS]
            _ = p + outerMat (vecFromFin7 (f t).u) (vecFromFin7 (f t).v) := by
              rw [codeMat_outerCode_eq]
            _ = p + outerMat (vecFromFin7 u₀) (vecFromFin7 (f t).v) := by rw [hu]⟩
    · rcases hcol with ⟨v₀, hv₀⟩
      exact Or.inr ⟨p, vecFromFin7 v₀, vecFromFin7_ne_zero v₀, fun t ht => by
        by_cases hEq : t = t₀
        · subst t
          refine ⟨0, ?_⟩
          simp only [p, add_eq_left]
          ext i j
          simp [outerMat]
        · have htS : t ∈ S := by simp [S, ht, hEq]
          have hmem : f t ∈ fam := by
            apply List.mem_map.mpr
            exact ⟨t, by simpa using htS, rfl⟩
          have hv : (f t).v = v₀ := hv₀ (f t) hmem
          refine ⟨vecFromFin7 (f t).u, ?_⟩
          calc
            D.A t = p + (D.A t + p) := codex_cancel_affine_base p (D.A t)
            _ = p + codeMat (outerCode (f t).u (f t).v) := by rw [hf t htS]
            _ = p + outerMat (vecFromFin7 (f t).u) (vecFromFin7 (f t).v) := by
              rw [codeMat_outerCode_eq]
            _ = p + outerMat (vecFromFin7 (f t).u) (vecFromFin7 v₀) := by rw [hv]⟩
  · exact Or.inl ⟨0, vecFromFin7 0, vecFromFin7_ne_zero 0, fun t ht =>
      False.elim (hsome ⟨t, ht⟩)⟩

end QiushiMatmul
end
