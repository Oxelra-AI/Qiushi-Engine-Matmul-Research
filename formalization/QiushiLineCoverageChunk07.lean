import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc224_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc224_le :
    lineSourcePlane ⟨224, by decide⟩ ≤ actionW (codeMat 161) (codeMat 419) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc224_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 161) (codeMat 419) (codeMat 21) = codeMat 450 := by
      unfold actionA
      rw [lineSrc224_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 21 * codeMat 249 = codeMat 450
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 419) X = codeMat 450
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc224_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨224, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 419) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 419) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc224_le hAct

private theorem lineSrc225_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc225_le :
    lineSourcePlane ⟨225, by decide⟩ ≤ actionW (codeMat 161) (codeMat 403) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc225_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 20) = codeMat 452 := by
      unfold actionA
      rw [lineSrc225_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 313 = codeMat 452
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 452
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc225_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨225, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 403) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 403) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc225_le hAct

private theorem lineSrc226_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = codeMat 271 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * codeMat 271 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc226_le :
    lineSourcePlane ⟨226, by decide⟩ ≤ actionW (codeMat 141) (codeMat 410) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 141) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc226_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 16 * codeMat 271 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 410) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 141) (codeMat 410) (codeMat 17) = codeMat 454 := by
      unfold actionA
      rw [lineSrc226_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 17 * codeMat 271 = codeMat 454
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 410) X = codeMat 454
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc226_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨226, by decide⟩) 18 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 410) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 410) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc226_le hAct

private theorem lineSrc227_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc227_le :
    lineSourcePlane ⟨227, by decide⟩ ≤ actionW (codeMat 161) (codeMat 403) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc227_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 80) = codeMat 456 := by
      unfold actionA
      rw [lineSrc227_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * codeMat 313 = codeMat 456
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 456
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc227_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨227, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 403) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 403) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc227_le hAct

private theorem lineSrc228_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc228_le :
    lineSourcePlane ⟨228, by decide⟩ ≤ actionW (codeMat 161) (codeMat 419) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc228_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 161) (codeMat 419) (codeMat 85) = codeMat 458 := by
      unfold actionA
      rw [lineSrc228_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 85 * codeMat 249 = codeMat 458
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 419) X = codeMat 458
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc228_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨228, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 419) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 419) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc228_le hAct

private theorem lineSrc229_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc229_le :
    lineSourcePlane ⟨229, by decide⟩ ≤ actionW (codeMat 161) (codeMat 403) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc229_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 84) = codeMat 460 := by
      unfold actionA
      rw [lineSrc229_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 313 = codeMat 460
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 460
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc229_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨229, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 403) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 403) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc229_le hAct

private theorem lineSrc230_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc230_le :
    lineSourcePlane ⟨230, by decide⟩ ≤ actionW (codeMat 169) (codeMat 403) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc230_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 169) (codeMat 403) (codeMat 81) = codeMat 462 := by
      unfold actionA
      rw [lineSrc230_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 81 * codeMat 313 = codeMat 462
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 403) X = codeMat 462
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc230_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨230, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 403) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 403) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc230_le hAct

private theorem lineSrc231_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = codeMat 465 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * codeMat 465 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc231_le :
    lineSourcePlane ⟨231, by decide⟩ ≤ actionW (codeMat 161) (codeMat 309) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc231_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 465 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 309) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 309) (codeMat 160) = codeMat 464 := by
      unfold actionA
      rw [lineSrc231_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 465 = codeMat 464
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 309) X = codeMat 464
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc231_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨231, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 309) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 309) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc231_le hAct

private theorem lineSrc232_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = codeMat 465 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * codeMat 465 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc232_le :
    lineSourcePlane ⟨232, by decide⟩ ≤ actionW (codeMat 225) (codeMat 309) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc232_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 465 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 309) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 309) (codeMat 160) = codeMat 466 := by
      unfold actionA
      rw [lineSrc232_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 465 = codeMat 466
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 309) X = codeMat 466
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc232_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨232, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 309) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 309) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc232_le hAct

private theorem lineSrc233_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = codeMat 465 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * codeMat 465 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc233_le :
    lineSourcePlane ⟨233, by decide⟩ ≤ actionW (codeMat 233) (codeMat 309) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc233_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 465 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 309) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 309) (codeMat 161) = codeMat 468 := by
      unfold actionA
      rw [lineSrc233_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 465 = codeMat 468
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 309) X = codeMat 468
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc233_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨233, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 309) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 309) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc233_le hAct

private theorem lineSrc234_QtInv :
    (codeMat 309 : Mat3).transpose⁻¹ = codeMat 465 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 309 : Mat3).transpose * codeMat 465 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc234_le :
    lineSourcePlane ⟨234, by decide⟩ ≤ actionW (codeMat 169) (codeMat 309) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 309) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc234_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 465 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 309) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 309) (codeMat 161) = codeMat 470 := by
      unfold actionA
      rw [lineSrc234_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 465 = codeMat 470
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 309) X = codeMat 470
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc234_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨234, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 309 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 309) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 309) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc234_le hAct

private theorem lineSrc235_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc235_le :
    lineSourcePlane ⟨235, by decide⟩ ≤ actionW (codeMat 161) (codeMat 307) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc235_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 307) (codeMat 160) = codeMat 472 := by
      unfold actionA
      rw [lineSrc235_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 473 = codeMat 472
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 307) X = codeMat 472
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc235_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨235, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 307) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 307) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc235_le hAct

private theorem lineSrc236_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc236_le :
    lineSourcePlane ⟨236, by decide⟩ ≤ actionW (codeMat 225) (codeMat 307) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc236_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 307) (codeMat 161) = codeMat 474 := by
      unfold actionA
      rw [lineSrc236_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 473 = codeMat 474
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 307) X = codeMat 474
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc236_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨236, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 307) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 307) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc236_le hAct

private theorem lineSrc237_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc237_le :
    lineSourcePlane ⟨237, by decide⟩ ≤ actionW (codeMat 233) (codeMat 307) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc237_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 307) (codeMat 160) = codeMat 476 := by
      unfold actionA
      rw [lineSrc237_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 473 = codeMat 476
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 307) X = codeMat 476
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc237_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨237, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 307) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 307) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc237_le hAct

private theorem lineSrc238_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc238_le :
    lineSourcePlane ⟨238, by decide⟩ ≤ actionW (codeMat 169) (codeMat 307) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc238_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 307) (codeMat 161) = codeMat 478 := by
      unfold actionA
      rw [lineSrc238_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 473 = codeMat 478
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 307) X = codeMat 478
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc238_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨238, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 307) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 307) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc238_le hAct

private theorem lineSrc239_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = codeMat 481 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * codeMat 481 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc239_le :
    lineSourcePlane ⟨239, by decide⟩ ≤ actionW (codeMat 161) (codeMat 179) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc239_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 481 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 179) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 179) (codeMat 160) = codeMat 480 := by
      unfold actionA
      rw [lineSrc239_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 481 = codeMat 480
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 179) X = codeMat 480
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc239_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨239, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 179) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 179) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc239_le hAct

private theorem lineSrc240_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = codeMat 481 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * codeMat 481 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc240_le :
    lineSourcePlane ⟨240, by decide⟩ ≤ actionW (codeMat 233) (codeMat 179) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc240_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 481 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 179) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 179) (codeMat 161) = codeMat 482 := by
      unfold actionA
      rw [lineSrc240_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 481 = codeMat 482
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 179) X = codeMat 482
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc240_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨240, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 179) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 179) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc240_le hAct

private theorem lineSrc241_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = codeMat 481 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * codeMat 481 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc241_le :
    lineSourcePlane ⟨241, by decide⟩ ≤ actionW (codeMat 225) (codeMat 179) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc241_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 481 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 179) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 179) (codeMat 160) = codeMat 484 := by
      unfold actionA
      rw [lineSrc241_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 481 = codeMat 484
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 179) X = codeMat 484
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc241_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨241, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 179) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 179) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc241_le hAct

private theorem lineSrc242_QtInv :
    (codeMat 179 : Mat3).transpose⁻¹ = codeMat 481 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 179 : Mat3).transpose * codeMat 481 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc242_le :
    lineSourcePlane ⟨242, by decide⟩ ≤ actionW (codeMat 169) (codeMat 179) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 179) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc242_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 481 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 179) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 179) (codeMat 161) = codeMat 486 := by
      unfold actionA
      rw [lineSrc242_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 481 = codeMat 486
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 179) X = codeMat 486
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc242_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨242, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 179 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 179) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 179) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc242_le hAct

private theorem lineSrc243_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc243_le :
    lineSourcePlane ⟨243, by decide⟩ ≤ actionW (codeMat 161) (codeMat 181) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc243_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 181) (codeMat 160) = codeMat 488 := by
      unfold actionA
      rw [lineSrc243_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 489 = codeMat 488
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 181) X = codeMat 488
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc243_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨243, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 181) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 181) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc243_le hAct

private theorem lineSrc244_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc244_le :
    lineSourcePlane ⟨244, by decide⟩ ≤ actionW (codeMat 233) (codeMat 181) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc244_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 181) (codeMat 160) = codeMat 490 := by
      unfold actionA
      rw [lineSrc244_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 489 = codeMat 490
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 181) X = codeMat 490
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc244_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨244, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 181) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 181) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc244_le hAct

private theorem lineSrc245_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc245_le :
    lineSourcePlane ⟨245, by decide⟩ ≤ actionW (codeMat 225) (codeMat 181) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc245_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 181) (codeMat 161) = codeMat 492 := by
      unfold actionA
      rw [lineSrc245_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 489 = codeMat 492
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 181) X = codeMat 492
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc245_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨245, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 181) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 181) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc245_le hAct

private theorem lineSrc246_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc246_le :
    lineSourcePlane ⟨246, by decide⟩ ≤ actionW (codeMat 169) (codeMat 181) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc246_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 181) (codeMat 161) = codeMat 494 := by
      unfold actionA
      rw [lineSrc246_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 489 = codeMat 494
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 181) X = codeMat 494
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc246_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨246, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 181) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 181) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc246_le hAct

private theorem lineSrc247_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc247_le :
    lineSourcePlane ⟨247, by decide⟩ ≤ actionW (codeMat 177) (codeMat 403) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc247_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 403) (codeMat 80) = codeMat 496 := by
      unfold actionA
      rw [lineSrc247_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * codeMat 313 = codeMat 496
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 403) X = codeMat 496
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc247_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨247, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 403) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 403) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc247_le hAct

private theorem lineSrc248_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc248_le :
    lineSourcePlane ⟨248, by decide⟩ ≤ actionW (codeMat 177) (codeMat 419) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc248_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 85) = codeMat 498 := by
      unfold actionA
      rw [lineSrc248_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 85 * codeMat 249 = codeMat 498
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 419) X = codeMat 498
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc248_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨248, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc248_le hAct

private theorem lineSrc249_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc249_le :
    lineSourcePlane ⟨249, by decide⟩ ≤ actionW (codeMat 177) (codeMat 403) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc249_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 403) (codeMat 84) = codeMat 500 := by
      unfold actionA
      rw [lineSrc249_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 313 = codeMat 500
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 403) X = codeMat 500
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc249_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨249, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 403) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 403) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc249_le hAct

private theorem lineSrc250_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc250_le :
    lineSourcePlane ⟨250, by decide⟩ ≤ actionW (codeMat 185) (codeMat 403) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc250_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 185) (codeMat 403) (codeMat 81) = codeMat 502 := by
      unfold actionA
      rw [lineSrc250_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 81 * codeMat 313 = codeMat 502
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 403) X = codeMat 502
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc250_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨250, by decide⟩) 18 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 403) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 403) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc250_le hAct

private theorem lineSrc251_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = codeMat 271 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * codeMat 271 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc251_le :
    lineSourcePlane ⟨251, by decide⟩ ≤ actionW (codeMat 142) (codeMat 410) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc251_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * codeMat 271 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 410) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 410) (codeMat 1) = codeMat 504 := by
      unfold actionA
      rw [lineSrc251_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 271 = codeMat 504
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 410) X = codeMat 504
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc251_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨251, by decide⟩) 18 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 410) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 410) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc251_le hAct

private theorem lineSrc252_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc252_le :
    lineSourcePlane ⟨252, by decide⟩ ≤ actionW (codeMat 177) (codeMat 419) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc252_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 177) (codeMat 419) (codeMat 21) = codeMat 506 := by
      unfold actionA
      rw [lineSrc252_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 21 * codeMat 249 = codeMat 506
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 419) X = codeMat 506
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc252_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨252, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 419) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 419) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc252_le hAct

private theorem lineSrc253_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc253_le :
    lineSourcePlane ⟨253, by decide⟩ ≤ actionW (codeMat 177) (codeMat 403) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc253_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 403) (codeMat 20) = codeMat 508 := by
      unfold actionA
      rw [lineSrc253_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 313 = codeMat 508
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 403) X = codeMat 508
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc253_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨253, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 403) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 403) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc253_le hAct

private theorem lineSrc254_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = codeMat 271 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * codeMat 271 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc254_le :
    lineSourcePlane ⟨254, by decide⟩ ≤ actionW (codeMat 143) (codeMat 410) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc254_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * codeMat 271 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 410) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 143) (codeMat 410) (codeMat 17) = codeMat 510 := by
      unfold actionA
      rw [lineSrc254_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 17 * codeMat 271 = codeMat 510
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 410) X = codeMat 510
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc254_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨254, by decide⟩) 18 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 410) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 410) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc254_le hAct

end QiushiMatmul
