import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc160_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc160_le :
    lineSourcePlane ⟨160, by decide⟩ ≤ actionW (codeMat 161) (codeMat 165) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc160_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 20) = codeMat 322 := by
      unfold actionA
      rw [lineSrc160_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 169 = codeMat 322
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 322
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc160_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨160, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 165) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 165) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc160_le hAct

private theorem lineSrc161_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = codeMat 141 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * codeMat 141 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc161_le :
    lineSourcePlane ⟨161, by decide⟩ ≤ actionW (codeMat 141) (codeMat 172) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 141) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc161_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 16 * codeMat 141 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 172) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 141) (codeMat 172) (codeMat 17) = codeMat 324 := by
      unfold actionA
      rw [lineSrc161_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 17 * codeMat 141 = codeMat 324
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 172) X = codeMat 324
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc161_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨161, by decide⟩) 18 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 172) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 172) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc161_le hAct

private theorem lineSrc162_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc162_le :
    lineSourcePlane ⟨162, by decide⟩ ≤ actionW (codeMat 161) (codeMat 181) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc162_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 161) (codeMat 181) (codeMat 21) = codeMat 326 := by
      unfold actionA
      rw [lineSrc162_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 21 * codeMat 489 = codeMat 326
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 181) X = codeMat 326
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc162_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨162, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 181) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 181) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc162_le hAct

private theorem lineSrc163_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc163_le :
    lineSourcePlane ⟨163, by decide⟩ ≤ actionW (codeMat 161) (codeMat 165) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc163_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 80) = codeMat 328 := by
      unfold actionA
      rw [lineSrc163_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * codeMat 169 = codeMat 328
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 328
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc163_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨163, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 165) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 165) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc163_le hAct

private theorem lineSrc164_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc164_le :
    lineSourcePlane ⟨164, by decide⟩ ≤ actionW (codeMat 161) (codeMat 165) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc164_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 84) = codeMat 330 := by
      unfold actionA
      rw [lineSrc164_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 169 = codeMat 330
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 330
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc164_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨164, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 165) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 165) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc164_le hAct

private theorem lineSrc165_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc165_le :
    lineSourcePlane ⟨165, by decide⟩ ≤ actionW (codeMat 169) (codeMat 165) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc165_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 81) = codeMat 332 := by
      unfold actionA
      rw [lineSrc165_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 81 * codeMat 169 = codeMat 332
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 165) X = codeMat 332
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc165_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨165, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 165) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 165) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc165_le hAct

private theorem lineSrc166_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc166_le :
    lineSourcePlane ⟨166, by decide⟩ ≤ actionW (codeMat 161) (codeMat 181) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc166_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 161) (codeMat 181) (codeMat 85) = codeMat 334 := by
      unfold actionA
      rw [lineSrc166_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 85 * codeMat 489 = codeMat 334
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 181) X = codeMat 334
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc166_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨166, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 181) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 181) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc166_le hAct

private theorem lineSrc167_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = codeMat 337 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * codeMat 337 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc167_le :
    lineSourcePlane ⟨167, by decide⟩ ≤ actionW (codeMat 161) (codeMat 277) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc167_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 337 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 277) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 277) (codeMat 160) = codeMat 336 := by
      unfold actionA
      rw [lineSrc167_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 337 = codeMat 336
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 277) X = codeMat 336
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc167_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨167, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 277) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 277) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc167_le hAct

private theorem lineSrc168_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = codeMat 337 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * codeMat 337 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc168_le :
    lineSourcePlane ⟨168, by decide⟩ ≤ actionW (codeMat 225) (codeMat 277) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc168_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 337 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 277) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 277) (codeMat 160) = codeMat 338 := by
      unfold actionA
      rw [lineSrc168_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 337 = codeMat 338
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 277) X = codeMat 338
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc168_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨168, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 277) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 277) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc168_le hAct

private theorem lineSrc169_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = codeMat 337 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * codeMat 337 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc169_le :
    lineSourcePlane ⟨169, by decide⟩ ≤ actionW (codeMat 169) (codeMat 277) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc169_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 337 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 277) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 277) (codeMat 161) = codeMat 340 := by
      unfold actionA
      rw [lineSrc169_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 337 = codeMat 340
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 277) X = codeMat 340
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc169_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨169, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 277) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 277) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc169_le hAct

private theorem lineSrc170_QtInv :
    (codeMat 277 : Mat3).transpose⁻¹ = codeMat 337 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 277 : Mat3).transpose * codeMat 337 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc170_le :
    lineSourcePlane ⟨170, by decide⟩ ≤ actionW (codeMat 233) (codeMat 277) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 277) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc170_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 337 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 277) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 277) (codeMat 161) = codeMat 342 := by
      unfold actionA
      rw [lineSrc170_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 337 = codeMat 342
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 277) X = codeMat 342
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc170_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨170, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 277 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 277) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 277) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc170_le hAct

private theorem lineSrc171_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = codeMat 345 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * codeMat 345 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc171_le :
    lineSourcePlane ⟨171, by decide⟩ ≤ actionW (codeMat 161) (codeMat 279) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc171_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 345 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 279) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 279) (codeMat 160) = codeMat 344 := by
      unfold actionA
      rw [lineSrc171_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 345 = codeMat 344
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 279) X = codeMat 344
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc171_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨171, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 279) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 279) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc171_le hAct

private theorem lineSrc172_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = codeMat 345 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * codeMat 345 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc172_le :
    lineSourcePlane ⟨172, by decide⟩ ≤ actionW (codeMat 225) (codeMat 279) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc172_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 345 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 279) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 279) (codeMat 161) = codeMat 346 := by
      unfold actionA
      rw [lineSrc172_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 345 = codeMat 346
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 279) X = codeMat 346
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc172_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨172, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 279) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 279) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc172_le hAct

private theorem lineSrc173_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = codeMat 345 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * codeMat 345 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc173_le :
    lineSourcePlane ⟨173, by decide⟩ ≤ actionW (codeMat 169) (codeMat 279) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc173_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 345 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 279) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 279) (codeMat 161) = codeMat 348 := by
      unfold actionA
      rw [lineSrc173_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 345 = codeMat 348
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 279) X = codeMat 348
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc173_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨173, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 279) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 279) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc173_le hAct

private theorem lineSrc174_QtInv :
    (codeMat 279 : Mat3).transpose⁻¹ = codeMat 345 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 279 : Mat3).transpose * codeMat 345 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc174_le :
    lineSourcePlane ⟨174, by decide⟩ ≤ actionW (codeMat 233) (codeMat 279) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 279) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc174_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 345 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 279) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 279) (codeMat 160) = codeMat 350 := by
      unfold actionA
      rw [lineSrc174_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 345 = codeMat 350
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 279) X = codeMat 350
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc174_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨174, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 279 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 279) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 279) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc174_le hAct

private theorem lineSrc175_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc175_le :
    lineSourcePlane ⟨175, by decide⟩ ≤ actionW (codeMat 177) (codeMat 165) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc175_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 165) (codeMat 80) = codeMat 352 := by
      unfold actionA
      rw [lineSrc175_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * codeMat 169 = codeMat 352
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 165) X = codeMat 352
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc175_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨175, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 165) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 165) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc175_le hAct

private theorem lineSrc176_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc176_le :
    lineSourcePlane ⟨176, by decide⟩ ≤ actionW (codeMat 177) (codeMat 165) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc176_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 165) (codeMat 84) = codeMat 354 := by
      unfold actionA
      rw [lineSrc176_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 169 = codeMat 354
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 165) X = codeMat 354
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc176_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨176, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 165) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 165) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc176_le hAct

private theorem lineSrc177_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc177_le :
    lineSourcePlane ⟨177, by decide⟩ ≤ actionW (codeMat 185) (codeMat 165) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc177_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 185) (codeMat 165) (codeMat 81) = codeMat 356 := by
      unfold actionA
      rw [lineSrc177_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 81 * codeMat 169 = codeMat 356
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 165) X = codeMat 356
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc177_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨177, by decide⟩) 18 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 165) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 165) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc177_le hAct

private theorem lineSrc178_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc178_le :
    lineSourcePlane ⟨178, by decide⟩ ≤ actionW (codeMat 177) (codeMat 181) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc178_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 177) (codeMat 181) (codeMat 85) = codeMat 358 := by
      unfold actionA
      rw [lineSrc178_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 85 * codeMat 489 = codeMat 358
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 181) X = codeMat 358
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc178_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨178, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 181) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 181) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc178_le hAct

private theorem lineSrc179_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = codeMat 141 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * codeMat 141 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc179_le :
    lineSourcePlane ⟨179, by decide⟩ ≤ actionW (codeMat 142) (codeMat 172) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc179_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * codeMat 141 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 172) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 172) (codeMat 1) = codeMat 360 := by
      unfold actionA
      rw [lineSrc179_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 141 = codeMat 360
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 172) X = codeMat 360
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc179_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨179, by decide⟩) 18 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 172) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 172) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc179_le hAct

private theorem lineSrc180_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc180_le :
    lineSourcePlane ⟨180, by decide⟩ ≤ actionW (codeMat 177) (codeMat 165) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc180_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 165) (codeMat 20) = codeMat 362 := by
      unfold actionA
      rw [lineSrc180_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 169 = codeMat 362
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 165) X = codeMat 362
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc180_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨180, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 165) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 165) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc180_le hAct

private theorem lineSrc181_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = codeMat 141 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * codeMat 141 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc181_le :
    lineSourcePlane ⟨181, by decide⟩ ≤ actionW (codeMat 143) (codeMat 172) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc181_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * codeMat 141 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 172) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 143) (codeMat 172) (codeMat 17) = codeMat 364 := by
      unfold actionA
      rw [lineSrc181_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 17 * codeMat 141 = codeMat 364
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 172) X = codeMat 364
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc181_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨181, by decide⟩) 18 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 172) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 172) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc181_le hAct

private theorem lineSrc182_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc182_le :
    lineSourcePlane ⟨182, by decide⟩ ≤ actionW (codeMat 177) (codeMat 181) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc182_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 177) (codeMat 181) (codeMat 21) = codeMat 366 := by
      unfold actionA
      rw [lineSrc182_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 21 * codeMat 489 = codeMat 366
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 181) X = codeMat 366
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc182_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨182, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 181) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 181) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc182_le hAct

private theorem lineSrc183_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = codeMat 369 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * codeMat 369 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc183_le :
    lineSourcePlane ⟨183, by decide⟩ ≤ actionW (codeMat 161) (codeMat 407) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 407) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc183_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 369 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 407) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 407) (codeMat 160) = codeMat 368 := by
      unfold actionA
      rw [lineSrc183_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 369 = codeMat 368
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 407) X = codeMat 368
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc183_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨183, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 407 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 407) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 407) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc183_le hAct

private theorem lineSrc184_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = codeMat 369 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * codeMat 369 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc184_le :
    lineSourcePlane ⟨184, by decide⟩ ≤ actionW (codeMat 233) (codeMat 407) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 407) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc184_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 369 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 407) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 407) (codeMat 161) = codeMat 370 := by
      unfold actionA
      rw [lineSrc184_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 369 = codeMat 370
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 407) X = codeMat 370
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc184_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨184, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 407 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 407) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 407) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc184_le hAct

private theorem lineSrc185_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = codeMat 369 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * codeMat 369 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc185_le :
    lineSourcePlane ⟨185, by decide⟩ ≤ actionW (codeMat 169) (codeMat 407) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 407) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc185_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 369 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 407) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 407) (codeMat 161) = codeMat 372 := by
      unfold actionA
      rw [lineSrc185_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 369 = codeMat 372
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 407) X = codeMat 372
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc185_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨185, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 407 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 407) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 407) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc185_le hAct

private theorem lineSrc186_QtInv :
    (codeMat 407 : Mat3).transpose⁻¹ = codeMat 369 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 407 : Mat3).transpose * codeMat 369 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc186_le :
    lineSourcePlane ⟨186, by decide⟩ ≤ actionW (codeMat 225) (codeMat 407) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 407) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc186_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 369 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 407) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 407) (codeMat 160) = codeMat 374 := by
      unfold actionA
      rw [lineSrc186_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 369 = codeMat 374
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 407) X = codeMat 374
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc186_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨186, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 407 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 407) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 407) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc186_le hAct

private theorem lineSrc187_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = codeMat 377 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * codeMat 377 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc187_le :
    lineSourcePlane ⟨187, by decide⟩ ≤ actionW (codeMat 161) (codeMat 405) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc187_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 377 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 405) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 405) (codeMat 160) = codeMat 376 := by
      unfold actionA
      rw [lineSrc187_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 377 = codeMat 376
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 405) X = codeMat 376
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc187_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨187, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 405) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 405) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc187_le hAct

private theorem lineSrc188_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = codeMat 377 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * codeMat 377 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc188_le :
    lineSourcePlane ⟨188, by decide⟩ ≤ actionW (codeMat 233) (codeMat 405) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc188_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 377 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 405) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 405) (codeMat 160) = codeMat 378 := by
      unfold actionA
      rw [lineSrc188_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 377 = codeMat 378
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 405) X = codeMat 378
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc188_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨188, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 405) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 405) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc188_le hAct

private theorem lineSrc189_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = codeMat 377 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * codeMat 377 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc189_le :
    lineSourcePlane ⟨189, by decide⟩ ≤ actionW (codeMat 169) (codeMat 405) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc189_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 377 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 405) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 405) (codeMat 161) = codeMat 380 := by
      unfold actionA
      rw [lineSrc189_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 377 = codeMat 380
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 405) X = codeMat 380
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc189_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨189, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 405) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 405) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc189_le hAct

private theorem lineSrc190_QtInv :
    (codeMat 405 : Mat3).transpose⁻¹ = codeMat 377 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 405 : Mat3).transpose * codeMat 377 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc190_le :
    lineSourcePlane ⟨190, by decide⟩ ≤ actionW (codeMat 225) (codeMat 405) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 405) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc190_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 377 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 405) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 405) (codeMat 161) = codeMat 382 := by
      unfold actionA
      rw [lineSrc190_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 377 = codeMat 382
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 405) X = codeMat 382
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc190_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨190, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 405 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 405) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 405) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc190_le hAct

private theorem lineSrc191_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc191_le :
    lineSourcePlane ⟨191, by decide⟩ ≤ actionW (codeMat 140) (codeMat 394) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc191_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 394) (codeMat 1) = codeMat 384 := by
      unfold actionA
      rw [lineSrc191_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 384
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 394) X = codeMat 384
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc191_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨191, by decide⟩) 18 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 394) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 394) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc191_le hAct

end QiushiMatmul
