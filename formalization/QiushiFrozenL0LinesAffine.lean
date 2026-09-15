import QiushiFrozenL0Exact
import QiushiNormalizedCosetCapsCodex

namespace QiushiMatmul.FrozenL0Report

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem line_upper_check : ∀ i : Fin 496,
    frozenWangLower i ≤ 19 ∨ (spanEnum (frozenWangBasis i)).card ≠ 2 := by
  decide +kernel +revert

theorem affine_upper_check : ∀ i : Fin 496,
    frozenWangLower i ≤ 17 ∨ (spanEnum (frozenWangBasis i)).card ≠ 8 ∨
      codeRankCount (frozenWangBasis i) 1 ≠ 3 := by
  decide +kernel +revert

def frozenLineIndex (k : Fin 3) : Fin 496 := ⟨492 + k.val, by omega⟩

def frozenLineCode (k : Fin 3) : Nat := ![1,10,84] k

def frozenLineShift (k : Fin 3) : Mat3 := codeMat (![273,266,84] k)

theorem frozen_line_checks (k : Fin 3) :
    frozenWangBasis (frozenLineIndex k) = [frozenLineCode k] ∧
    frozenWangLower (frozenLineIndex k) = 19 ∧
    (spanEnum [frozenLineCode k]).card = 2 ∧
    (frozenLineShift k).det ≠ 0 ∧
    (frozenLineShift k).transpose * codeMat (frozenLineCode k) =
      codeMat (ahLineRepCode k) := by
  fin_cases k <;> decide +kernel

theorem singleton_spanCodes (n : Nat) :
    spanCodes [n] = Submodule.span F2 {codeMat n} := by
  unfold spanCodes
  congr 1
  ext M
  simp

theorem nonzero_line_orbit (M : Mat3) (hM : M ≠ 0) :
    ∃ k : Fin 3, frozenWangTable.OrbitImage (frozenLineIndex k)
      (Submodule.span F2 {M}) := by
  let c := matrixCode M
  let k := ahLineRank c
  have hc : c.val ≠ 0 := by
    intro h
    apply hM
    have he : codeMat c.val = M := codeMat_matrixCode M
    rw [h, codeMat_zero] at he
    exact he.symm
  let : Invertible (ahLineQ c) := Matrix.invertibleOfIsUnitDet _ (ahLineQ_isUnitDet c)
  have hP : (frozenLineShift k * ahLineP c).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (frozen_line_checks k).2.2.2.1
      (isUnit_iff_ne_zero.mp (ahLineP_isUnitDet c))
  have hQ : (ahLineQ c).det ≠ 0 := isUnit_iff_ne_zero.mp (ahLineQ_isUnitDet c)
  have hact : actionA (frozenLineShift k * ahLineP c) (ahLineQ c)
      (codeMat (frozenLineCode k)) = M := by
    calc
      _ = actionA (ahLineP c) (ahLineQ c) (codeMat (ahLineRepCode k)) := by
        unfold actionA
        rw [Matrix.transpose_mul, Matrix.mul_assoc (ahLineP c).transpose,
          (frozen_line_checks k).2.2.2.2]
      _ = codeMat c.val := ahLineAction c hc
      _ = M := codeMat_matrixCode M
  refine ⟨k, frozenLineShift k * ahLineP c, ahLineQ c,
    ⟨Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hP)⟩,
    ⟨Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hQ)⟩, false, ?_⟩
  change Submodule.span F2 {M} = actionW _ _ (spanCodes (frozenWangBasis _))
  rw [(frozen_line_checks k).1, singleton_spanCodes]
  simp only [actionW, Submodule.map_span, Set.image_singleton]
  change Submodule.span F2 {M} = Submodule.span F2 {actionA _ _ _}
  rw [hact]

theorem nonzero_line_L0_exact (M : Mat3) (hM : M ≠ 0) :
    frozenWangTable.L0 (Submodule.span F2 {M}) = 19 := by
  obtain ⟨k, hk⟩ := nonzero_line_orbit M hM
  have hc : Nat.card (Submodule.span F2 {M}) = 2 := by
    rw [(orbit_counts _ _ hk).1, (frozen_line_checks k).1]
    exact (frozen_line_checks k).2.2.1
  apply le_antisymm
  · apply L0_le_of_orbit_labels
    intro i hi
    rcases line_upper_check i with h | h
    · exact h
    · exact False.elim (h ((orbit_counts i _ hi).1.symm.trans hc))
  · have h := frozenWangTable.lower_le_L0 _ hk
    change frozenWangLower _ ≤ _ at h
    simpa only [(frozen_line_checks k).2.1] using h

theorem one_dimensional_L0_exact (W : Submodule F2 Mat3)
    (hW : Module.finrank F2 W = 1) : frozenWangTable.L0 W = 19 := by
  have hne : W ≠ ⊥ := (Submodule.isAtom_iff_finrank_eq_one.mpr hW).ne_bot
  obtain ⟨M, hMW, hM⟩ := W.ne_bot_iff.mp hne
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hW hMW hM]
  exact nonzero_line_L0_exact M hM

def affineFrozenIndex (i : Fin 14) : Fin 496 :=
  if i.val = 0 then 414 else if i.val = 1 then 415 else 416

-- These are the witness matrices of QiushiFinitePremisesReducer, composed
-- with the column permutations from the frozen bases to its first three bases.
def affineFrozenP (i : Fin 14) : Mat3 :=
  codeMat (![273,273,273,281,273,281,161,169,161,169,177,185,177,185] i)

def affineFrozenQ (i : Fin 14) : Mat3 :=
  if i.val < 2 then codeMat 84 else
    codeMat 140 * codeMat (![273,273,273,273,281,281,161,161,169,169,177,177,185,185] i)

def affineFrozenQinv (i : Fin 14) : Mat3 :=
  if i.val < 2 then codeMat 84 else
    codeMat (![273,273,273,273,281,281,161,161,225,225,417,417,481,481] i) * codeMat 98

def affineFrozenPairs (i : Fin 14) : List (Nat × Nat) :=
  match i.val with
  | 0 => [(272,80),(4,1),(2,2)]
  | 1 => [(273,84),(4,1),(2,2)]
  | 2 => [(272,96),(4,1),(1,2)]
  | 3 => [(274,96),(4,1),(1,2)]
  | 4 => [(272,96),(4,1),(3,2)]
  | 5 => [(273,98),(4,1),(3,2)]
  | 6 => [(272,96),(2,1),(1,2)]
  | 7 => [(276,96),(2,1),(1,2)]
  | 8 => [(272,96),(5,2),(2,1)]
  | 9 => [(273,98),(5,2),(2,1)]
  | 10 => [(272,96),(6,1),(1,2)]
  | 11 => [(274,97),(6,1),(1,2)]
  | 12 => [(272,96),(5,2),(3,3)]
  | _ => [(273,98),(5,2),(3,3)]

theorem affine_frozen_checks (i : Fin 14) :
    frozenWangLower (affineFrozenIndex i) = 17 ∧
    (affineFrozenPairs i).map Prod.fst = codexAffineBasis i ∧
    (affineFrozenP i).det ≠ 0 ∧ (affineFrozenQ i).det ≠ 0 ∧
    (affineFrozenQ i).transpose * (affineFrozenQinv i).transpose = 1 ∧
    (∀ e ∈ affineFrozenPairs i,
      spanContainsCode (frozenWangBasis (affineFrozenIndex i)) e.2 = true ∧
      (affineFrozenP i).transpose * codeMat e.2 * (affineFrozenQinv i).transpose = codeMat e.1) ∧
    (∀ c ∈ frozenWangBasis (affineFrozenIndex i),
      spanContainsCode ((affineFrozenPairs i).map Prod.snd) c = true) := by
  fin_cases i <;> decide +kernel

theorem affine_profile_check (i : Fin 14) :
    (spanEnum (codexAffineBasis i)).card = 8 ∧ codeRankCount (codexAffineBasis i) 1 = 3 := by
  fin_cases i <;> decide +kernel

theorem affine_hyperplane_orbit (i : Fin 14) :
    frozenWangTable.OrbitImage (affineFrozenIndex i) (affineHyperplane i) := by
  obtain ⟨_, hb, hP, hQ, hInv, hPairs, hCover⟩ := affine_frozen_checks i
  rw [codex_affineHyperplane_eq_basis, ← hb]
  exact frozenOrbitImage_of_code_transport frozenWangTable (affineFrozenIndex i)
    (affineFrozenPairs i) (affineFrozenP i) (affineFrozenQ i) (affineFrozenQinv i) false
    hP hQ hInv hPairs hCover

theorem affine_hyperplane_L0_exact (i : Fin 14) :
    frozenWangTable.L0 (affineHyperplane i) = 17 := by
  apply le_antisymm
  · apply L0_le_of_orbit_labels
    intro j hj
    obtain ⟨hc, hr⟩ := orbit_counts _ _ hj
    have hn : Nat.card (affineHyperplane i) = 8 := by
      rw [codex_affineHyperplane_eq_basis, ← spanEnum_card]
      exact (affine_profile_check i).1
    have hnr : rankCount (affineHyperplane i) 1 = 3 := by
      rw [codex_affineHyperplane_eq_basis, ← codeRankCount_correct]
      exact (affine_profile_check i).2
    rcases affine_upper_check j with h | h | h
    · exact h
    · exact False.elim (h (hc.symm.trans hn))
    · exact False.elim (h ((hr 1).symm.trans hnr))
  · have h := frozenWangTable.lower_le_L0 _ (affine_hyperplane_orbit i)
    change frozenWangLower _ ≤ _ at h
    simpa only [(affine_frozen_checks i).1] using h

end QiushiMatmul.FrozenL0Report
