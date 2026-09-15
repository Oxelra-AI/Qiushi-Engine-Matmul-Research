import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc32_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc32_le :
    lineSourcePlane ⟨32, by decide⟩ ≤ actionW (codeMat 161) (codeMat 273) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 10) = codeMat 66 := by
      unfold actionA
      rw [lineSrc32_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 10 * codeMat 273 = codeMat 66
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 66
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc32_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨32, by decide⟩) 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc32_le hAct

private theorem lineSrc33_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc33_le :
    lineSourcePlane ⟨33, by decide⟩ ≤ actionW (codeMat 161) (codeMat 161) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc33_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 10) = codeMat 68 := by
      unfold actionA
      rw [lineSrc33_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 10 * codeMat 161 = codeMat 68
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 68
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc33_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨33, by decide⟩) 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc33_le hAct

private theorem lineSrc34_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc34_le :
    lineSourcePlane ⟨34, by decide⟩ ≤ actionW (codeMat 161) (codeMat 401) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc34_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 10) = codeMat 70 := by
      unfold actionA
      rw [lineSrc34_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 10 * codeMat 305 = codeMat 70
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 70
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc34_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨34, by decide⟩) 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 401) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 401) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc34_le hAct

private theorem lineSrc35_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc35_le :
    lineSourcePlane ⟨35, by decide⟩ ≤ actionW (codeMat 142) (codeMat 161) linePlane478T := by
  unfold lineSourcePlane lineSourceCode linePlane478T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 8 ∈ spanCodes [8, 1] :=
      spanContainsCode_implies_mem_spanCodes [8, 1] 8 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [lineSrc35_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 8 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [8, 1] ∧ actionA (codeMat 142) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 8, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [8, 1] :=
      spanContainsCode_implies_mem_spanCodes [8, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 161) (codeMat 1) = codeMat 72 := by
      unfold actionA
      rw [lineSrc35_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 72
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [8, 1] ∧ actionA (codeMat 142) (codeMat 161) X = codeMat 72
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc35_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨35, by decide⟩) 17 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane478T 17 := linePlane478T_lb h478
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 161) linePlane478T) 17 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 161) hP hQ linePlane478T 17 hBase
  exact quotientRankAtLeast_mono lineSrc35_le hAct

private theorem lineSrc36_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc36_le :
    lineSourcePlane ⟨36, by decide⟩ ≤ actionW (codeMat 177) (codeMat 273) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc36_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 10) = codeMat 74 := by
      unfold actionA
      rw [lineSrc36_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 10 * codeMat 273 = codeMat 74
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 74
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc36_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨36, by decide⟩) 17 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 273) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 273) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc36_le hAct

private theorem lineSrc37_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc37_le :
    lineSourcePlane ⟨37, by decide⟩ ≤ actionW (codeMat 177) (codeMat 161) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc37_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 10) = codeMat 76 := by
      unfold actionA
      rw [lineSrc37_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 10 * codeMat 161 = codeMat 76
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 76
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc37_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨37, by decide⟩) 17 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 161) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 161) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc37_le hAct

private theorem lineSrc38_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc38_le :
    lineSourcePlane ⟨38, by decide⟩ ≤ actionW (codeMat 177) (codeMat 401) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc38_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 10) = codeMat 78 := by
      unfold actionA
      rw [lineSrc38_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 10 * codeMat 305 = codeMat 78
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 78
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc38_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨38, by decide⟩) 17 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 401) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 401) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc38_le hAct

private theorem lineSrc39_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc39_le :
    lineSourcePlane ⟨39, by decide⟩ ≤ actionW (codeMat 273) (codeMat 273) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc39_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 80) = codeMat 80 := by
      unfold actionA
      rw [lineSrc39_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * codeMat 273 = codeMat 80
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 80
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc39_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨39, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc39_le hAct

private theorem lineSrc40_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc40_le :
    lineSourcePlane ⟨40, by decide⟩ ≤ actionW (codeMat 281) (codeMat 273) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 281) (codeMat 273) (codeMat 80) = codeMat 82 := by
      unfold actionA
      rw [lineSrc40_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 80 * codeMat 273 = codeMat 82
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 273) X = codeMat 82
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc40_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨40, by decide⟩) 18 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 273) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 273) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc40_le hAct

private theorem lineSrc41_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc41_le :
    lineSourcePlane ⟨41, by decide⟩ ≤ actionW (codeMat 273) (codeMat 273) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc41_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 84) = codeMat 84 := by
      unfold actionA
      rw [lineSrc41_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 273 = codeMat 84
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 84
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc41_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨41, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc41_le hAct

private theorem lineSrc42_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc42_le :
    lineSourcePlane ⟨42, by decide⟩ ≤ actionW (codeMat 273) (codeMat 305) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc42_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 84) = codeMat 86 := by
      unfold actionA
      rw [lineSrc42_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 401 = codeMat 86
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 305) X = codeMat 86
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc42_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨42, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 305) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 305) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc42_le hAct

private theorem lineSrc43_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc43_le :
    lineSourcePlane ⟨43, by decide⟩ ≤ actionW (codeMat 273) (codeMat 275) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc43_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 80) = codeMat 88 := by
      unfold actionA
      rw [lineSrc43_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * codeMat 281 = codeMat 88
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 275) X = codeMat 88
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc43_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨43, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc43_le hAct

private theorem lineSrc44_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc44_le :
    lineSourcePlane ⟨44, by decide⟩ ≤ actionW (codeMat 281) (codeMat 275) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc44_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 281) (codeMat 275) (codeMat 81) = codeMat 90 := by
      unfold actionA
      rw [lineSrc44_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 81 * codeMat 281 = codeMat 90
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 275) X = codeMat 90
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc44_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨44, by decide⟩) 18 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 275) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 275) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc44_le hAct

private theorem lineSrc45_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc45_le :
    lineSourcePlane ⟨45, by decide⟩ ≤ actionW (codeMat 273) (codeMat 275) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 84) = codeMat 92 := by
      unfold actionA
      rw [lineSrc45_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 281 = codeMat 92
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 275) X = codeMat 92
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc45_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨45, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc45_le hAct

private theorem lineSrc46_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc46_le :
    lineSourcePlane ⟨46, by decide⟩ ≤ actionW (codeMat 273) (codeMat 307) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc46_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 85) = codeMat 94 := by
      unfold actionA
      rw [lineSrc46_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 85 * codeMat 473 = codeMat 94
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 307) X = codeMat 94
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc46_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨46, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 307) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 307) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc46_le hAct

private theorem lineSrc47_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc47_le :
    lineSourcePlane ⟨47, by decide⟩ ≤ actionW (codeMat 273) (codeMat 161) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc47_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 80) = codeMat 96 := by
      unfold actionA
      rw [lineSrc47_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * codeMat 161 = codeMat 96
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 96
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc47_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨47, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc47_le hAct

private theorem lineSrc48_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc48_le :
    lineSourcePlane ⟨48, by decide⟩ ≤ actionW (codeMat 273) (codeMat 161) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc48_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 84) = codeMat 98 := by
      unfold actionA
      rw [lineSrc48_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 161 = codeMat 98
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 98
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc48_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨48, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc48_le hAct

private theorem lineSrc49_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc49_le :
    lineSourcePlane ⟨49, by decide⟩ ≤ actionW (codeMat 281) (codeMat 161) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 281) (codeMat 161) (codeMat 80) = codeMat 100 := by
      unfold actionA
      rw [lineSrc49_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 80 * codeMat 161 = codeMat 100
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 161) X = codeMat 100
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc49_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨49, by decide⟩) 18 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 161) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 161) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc49_le hAct

private theorem lineSrc50_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc50_le :
    lineSourcePlane ⟨50, by decide⟩ ≤ actionW (codeMat 273) (codeMat 177) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc50_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 84) = codeMat 102 := by
      unfold actionA
      rw [lineSrc50_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 417 = codeMat 102
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 177) X = codeMat 102
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc50_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨50, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 177) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 177) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc50_le hAct

private theorem lineSrc51_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc51_le :
    lineSourcePlane ⟨51, by decide⟩ ≤ actionW (codeMat 273) (codeMat 165) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc51_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 165) (codeMat 80) = codeMat 104 := by
      unfold actionA
      rw [lineSrc51_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * codeMat 169 = codeMat 104
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 165) X = codeMat 104
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc51_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨51, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 165) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 165) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc51_le hAct

private theorem lineSrc52_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc52_le :
    lineSourcePlane ⟨52, by decide⟩ ≤ actionW (codeMat 273) (codeMat 165) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc52_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 165) (codeMat 84) = codeMat 106 := by
      unfold actionA
      rw [lineSrc52_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 169 = codeMat 106
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 165) X = codeMat 106
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc52_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨52, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 165) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 165) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc52_le hAct

private theorem lineSrc53_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc53_le :
    lineSourcePlane ⟨53, by decide⟩ ≤ actionW (codeMat 281) (codeMat 165) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc53_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 281) (codeMat 165) (codeMat 81) = codeMat 108 := by
      unfold actionA
      rw [lineSrc53_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 81 * codeMat 169 = codeMat 108
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 165) X = codeMat 108
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc53_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨53, by decide⟩) 18 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 165) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 165) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc53_le hAct

private theorem lineSrc54_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc54_le :
    lineSourcePlane ⟨54, by decide⟩ ≤ actionW (codeMat 273) (codeMat 181) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc54_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 273) (codeMat 181) (codeMat 85) = codeMat 110 := by
      unfold actionA
      rw [lineSrc54_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 85 * codeMat 489 = codeMat 110
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 181) X = codeMat 110
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc54_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨54, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 181) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 181) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc54_le hAct

private theorem lineSrc55_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc55_le :
    lineSourcePlane ⟨55, by decide⟩ ≤ actionW (codeMat 273) (codeMat 401) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc55_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 80) = codeMat 112 := by
      unfold actionA
      rw [lineSrc55_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * codeMat 305 = codeMat 112
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 112
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc55_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨55, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 401) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 401) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc55_le hAct

private theorem lineSrc56_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc56_le :
    lineSourcePlane ⟨56, by decide⟩ ≤ actionW (codeMat 273) (codeMat 417) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc56_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 417) (codeMat 84) = codeMat 114 := by
      unfold actionA
      rw [lineSrc56_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 177 = codeMat 114
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 417) X = codeMat 114
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc56_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨56, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 417) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 417) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc56_le hAct

private theorem lineSrc57_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc57_le :
    lineSourcePlane ⟨57, by decide⟩ ≤ actionW (codeMat 273) (codeMat 401) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc57_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 84) = codeMat 116 := by
      unfold actionA
      rw [lineSrc57_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 305 = codeMat 116
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 116
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc57_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨57, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 401) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 401) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc57_le hAct

private theorem lineSrc58_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc58_le :
    lineSourcePlane ⟨58, by decide⟩ ≤ actionW (codeMat 281) (codeMat 401) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc58_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 281) (codeMat 401) (codeMat 80) = codeMat 118 := by
      unfold actionA
      rw [lineSrc58_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 80 * codeMat 305 = codeMat 118
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 401) X = codeMat 118
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc58_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨58, by decide⟩) 18 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 401) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 401) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc58_le hAct

private theorem lineSrc59_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc59_le :
    lineSourcePlane ⟨59, by decide⟩ ≤ actionW (codeMat 273) (codeMat 403) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc59_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 273) (codeMat 403) (codeMat 80) = codeMat 120 := by
      unfold actionA
      rw [lineSrc59_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 80 * codeMat 313 = codeMat 120
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 273) (codeMat 403) X = codeMat 120
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc59_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨59, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 403) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 403) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc59_le hAct

private theorem lineSrc60_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc60_le :
    lineSourcePlane ⟨60, by decide⟩ ≤ actionW (codeMat 273) (codeMat 419) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc60_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 273) (codeMat 419) (codeMat 85) = codeMat 122 := by
      unfold actionA
      rw [lineSrc60_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 85 * codeMat 249 = codeMat 122
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 419) X = codeMat 122
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc60_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨60, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 419) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 419) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc60_le hAct

private theorem lineSrc61_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc61_le :
    lineSourcePlane ⟨61, by decide⟩ ≤ actionW (codeMat 273) (codeMat 403) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc61_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 273) (codeMat 403) (codeMat 84) = codeMat 124 := by
      unfold actionA
      rw [lineSrc61_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 84 * codeMat 313 = codeMat 124
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 273) (codeMat 403) X = codeMat 124
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc61_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨61, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 403) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 403) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc61_le hAct

private theorem lineSrc62_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc62_le :
    lineSourcePlane ⟨62, by decide⟩ ≤ actionW (codeMat 281) (codeMat 403) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 281) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc62_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 281) (codeMat 403) (codeMat 81) = codeMat 126 := by
      unfold actionA
      rw [lineSrc62_QtInv]
      show (codeMat 281 : Mat3).transpose * codeMat 81 * codeMat 313 = codeMat 126
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 281) (codeMat 403) X = codeMat 126
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc62_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨62, by decide⟩) 18 := by
  have hP : Invertible (codeMat 281 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 281) (codeMat 403) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 281) (codeMat 403) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc62_le hAct

private theorem lineSrc63_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc63_le :
    lineSourcePlane ⟨63, by decide⟩ ≤ actionW (codeMat 140) (codeMat 266) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc63_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 266) (codeMat 1) = codeMat 128 := by
      unfold actionA
      rw [lineSrc63_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 128
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 266) X = codeMat 128
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc63_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨63, by decide⟩) 18 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 266) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 266) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc63_le hAct

end QiushiMatmul
