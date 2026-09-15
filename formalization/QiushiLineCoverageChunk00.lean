import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc0_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc0_le :
    lineSourcePlane ⟨0, by decide⟩ ≤ actionW (codeMat 161) (codeMat 266) linePlane478 := by
  unfold lineSourcePlane lineSourceCode linePlane478
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 2 ∈ spanCodes [2, 1] :=
      spanContainsCode_implies_mem_spanCodes [2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [lineSrc0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [2, 1] ∧ actionA (codeMat 161) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 2, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [2, 1] :=
      spanContainsCode_implies_mem_spanCodes [2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 266) (codeMat 1) = codeMat 2 := by
      unfold actionA
      rw [lineSrc0_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 2
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [2, 1] ∧ actionA (codeMat 161) (codeMat 266) X = codeMat 2
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc0_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨0, by decide⟩) 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane478 17 := h478
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 266) linePlane478) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 266) hP hQ linePlane478 17 hBase
  exact quotientRankAtLeast_mono lineSrc0_le hAct

private theorem lineSrc1_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc1_le :
    lineSourcePlane ⟨1, by decide⟩ ≤ actionW (codeMat 161) (codeMat 140) linePlane478 := by
  unfold lineSourcePlane lineSourceCode linePlane478
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 2 ∈ spanCodes [2, 1] :=
      spanContainsCode_implies_mem_spanCodes [2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [lineSrc1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [2, 1] ∧ actionA (codeMat 161) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 2, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [2, 1] :=
      spanContainsCode_implies_mem_spanCodes [2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 140) (codeMat 1) = codeMat 4 := by
      unfold actionA
      rw [lineSrc1_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 4
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [2, 1] ∧ actionA (codeMat 161) (codeMat 140) X = codeMat 4
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc1_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨1, by decide⟩) 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane478 17 := h478
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 140) linePlane478) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 140) hP hQ linePlane478 17 hBase
  exact quotientRankAtLeast_mono lineSrc1_le hAct

private theorem lineSrc2_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc2_le :
    lineSourcePlane ⟨2, by decide⟩ ≤ actionW (codeMat 161) (codeMat 394) linePlane478 := by
  unfold lineSourcePlane lineSourceCode linePlane478
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 2 ∈ spanCodes [2, 1] :=
      spanContainsCode_implies_mem_spanCodes [2, 1] 2 (by decide)
    have hact : actionA (codeMat 161) (codeMat 394) (codeMat 2) = codeMat 1 := by
      unfold actionA
      rw [lineSrc2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 2 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [2, 1] ∧ actionA (codeMat 161) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 2, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [2, 1] :=
      spanContainsCode_implies_mem_spanCodes [2, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 394) (codeMat 1) = codeMat 6 := by
      unfold actionA
      rw [lineSrc2_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 6
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [2, 1] ∧ actionA (codeMat 161) (codeMat 394) X = codeMat 6
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc2_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨2, by decide⟩) 17 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane478 17 := h478
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 394) linePlane478) 17 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 394) hP hQ linePlane478 17 hBase
  exact quotientRankAtLeast_mono lineSrc2_le hAct

private theorem lineSrc3_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc3_le :
    lineSourcePlane ⟨3, by decide⟩ ≤ actionW (codeMat 266) (codeMat 161) linePlane478T := by
  unfold lineSourcePlane lineSourceCode linePlane478T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 8 ∈ spanCodes [8, 1] :=
      spanContainsCode_implies_mem_spanCodes [8, 1] 8 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [lineSrc3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 8 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [8, 1] ∧ actionA (codeMat 266) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 8, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [8, 1] :=
      spanContainsCode_implies_mem_spanCodes [8, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 161) (codeMat 1) = codeMat 8 := by
      unfold actionA
      rw [lineSrc3_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 8
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [8, 1] ∧ actionA (codeMat 266) (codeMat 161) X = codeMat 8
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc3_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨3, by decide⟩) 17 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane478T 17 := linePlane478T_lb h478
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 161) linePlane478T) 17 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 161) hP hQ linePlane478T 17 hBase
  exact quotientRankAtLeast_mono lineSrc3_le hAct

private theorem lineSrc4_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc4_le :
    lineSourcePlane ⟨4, by decide⟩ ≤ actionW (codeMat 273) (codeMat 273) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 10) = codeMat 10 := by
      unfold actionA
      rw [lineSrc4_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * codeMat 273 = codeMat 10
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 10
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc4_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨4, by decide⟩) 17 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc4_le hAct

private theorem lineSrc5_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc5_le :
    lineSourcePlane ⟨5, by decide⟩ ≤ actionW (codeMat 273) (codeMat 161) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 10) = codeMat 12 := by
      unfold actionA
      rw [lineSrc5_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * codeMat 161 = codeMat 12
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 12
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc5_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨5, by decide⟩) 17 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc5_le hAct

private theorem lineSrc6_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc6_le :
    lineSourcePlane ⟨6, by decide⟩ ≤ actionW (codeMat 273) (codeMat 401) linePlane479 := by
  unfold lineSourcePlane lineSourceCode linePlane479
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 10 ∈ spanCodes [1, 10] :=
      spanContainsCode_implies_mem_spanCodes [1, 10] 10 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 10) = codeMat 14 := by
      unfold actionA
      rw [lineSrc6_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 10 * codeMat 305 = codeMat 14
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [1, 10] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 14
    exact ⟨codeMat 10, hw, hact⟩

theorem lineSrc6_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨6, by decide⟩) 17 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane479 17 := h479
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 401) linePlane479) 17 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 401) hP hQ linePlane479 17 hBase
  exact quotientRankAtLeast_mono lineSrc6_le hAct

private theorem lineSrc7_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc7_le :
    lineSourcePlane ⟨7, by decide⟩ ≤ actionW (codeMat 266) (codeMat 266) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 266) (codeMat 1) = codeMat 16 := by
      unfold actionA
      rw [lineSrc7_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 16
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 266) X = codeMat 16
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc7_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨7, by decide⟩) 18 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 266) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 266) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc7_le hAct

private theorem lineSrc8_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc8_le :
    lineSourcePlane ⟨8, by decide⟩ ≤ actionW (codeMat 267) (codeMat 266) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 267) (codeMat 266) (codeMat 1) = codeMat 18 := by
      unfold actionA
      rw [lineSrc8_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 18
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 266) X = codeMat 18
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc8_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨8, by decide⟩) 18 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 266) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 266) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc8_le hAct

private theorem lineSrc9_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc9_le :
    lineSourcePlane ⟨9, by decide⟩ ≤ actionW (codeMat 273) (codeMat 273) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 273) (codeMat 20) = codeMat 20 := by
      unfold actionA
      rw [lineSrc9_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 273 = codeMat 20
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 273) X = codeMat 20
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc9_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨9, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 273) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 273) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc9_le hAct

private theorem lineSrc10_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc10_le :
    lineSourcePlane ⟨10, by decide⟩ ≤ actionW (codeMat 273) (codeMat 305) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 305) (codeMat 20) = codeMat 22 := by
      unfold actionA
      rw [lineSrc10_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 401 = codeMat 22
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 305) X = codeMat 22
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc10_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨10, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 305) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 305) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc10_le hAct

private theorem lineSrc11_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = codeMat 267 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * codeMat 267 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc11_le :
    lineSourcePlane ⟨11, by decide⟩ ≤ actionW (codeMat 266) (codeMat 282) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * codeMat 267 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 282) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 282) (codeMat 1) = codeMat 24 := by
      unfold actionA
      rw [lineSrc11_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 267 = codeMat 24
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 282) X = codeMat 24
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc11_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨11, by decide⟩) 18 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 282) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 282) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc11_le hAct

private theorem lineSrc12_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = codeMat 267 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * codeMat 267 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc12_le :
    lineSourcePlane ⟨12, by decide⟩ ≤ actionW (codeMat 267) (codeMat 282) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * codeMat 267 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 282) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 267) (codeMat 282) (codeMat 17) = codeMat 26 := by
      unfold actionA
      rw [lineSrc12_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 17 * codeMat 267 = codeMat 26
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 282) X = codeMat 26
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc12_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨12, by decide⟩) 18 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 282) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 282) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc12_le hAct

private theorem lineSrc13_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc13_le :
    lineSourcePlane ⟨13, by decide⟩ ≤ actionW (codeMat 273) (codeMat 275) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 275) (codeMat 20) = codeMat 28 := by
      unfold actionA
      rw [lineSrc13_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 281 = codeMat 28
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 275) X = codeMat 28
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc13_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨13, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 275) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 275) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc13_le hAct

private theorem lineSrc14_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc14_le :
    lineSourcePlane ⟨14, by decide⟩ ≤ actionW (codeMat 273) (codeMat 307) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 273) (codeMat 307) (codeMat 21) = codeMat 30 := by
      unfold actionA
      rw [lineSrc14_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 21 * codeMat 473 = codeMat 30
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 307) X = codeMat 30
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc14_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨14, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 307) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 307) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc14_le hAct

private theorem lineSrc15_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc15_le :
    lineSourcePlane ⟨15, by decide⟩ ≤ actionW (codeMat 266) (codeMat 140) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 140) (codeMat 1) = codeMat 32 := by
      unfold actionA
      rw [lineSrc15_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 32
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 140) X = codeMat 32
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc15_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨15, by decide⟩) 18 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 140) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 140) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc15_le hAct

private theorem lineSrc16_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc16_le :
    lineSourcePlane ⟨16, by decide⟩ ≤ actionW (codeMat 273) (codeMat 161) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc16_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 161) (codeMat 20) = codeMat 34 := by
      unfold actionA
      rw [lineSrc16_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 161 = codeMat 34
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 161) X = codeMat 34
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc16_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨16, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 161) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 161) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc16_le hAct

private theorem lineSrc17_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc17_le :
    lineSourcePlane ⟨17, by decide⟩ ≤ actionW (codeMat 267) (codeMat 140) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc17_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 267) (codeMat 140) (codeMat 1) = codeMat 36 := by
      unfold actionA
      rw [lineSrc17_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 36
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 140) X = codeMat 36
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc17_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨17, by decide⟩) 18 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 140) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 140) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc17_le hAct

private theorem lineSrc18_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc18_le :
    lineSourcePlane ⟨18, by decide⟩ ≤ actionW (codeMat 273) (codeMat 177) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc18_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 177) (codeMat 20) = codeMat 38 := by
      unfold actionA
      rw [lineSrc18_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 417 = codeMat 38
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 177) X = codeMat 38
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc18_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨18, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 177) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 177) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc18_le hAct

private theorem lineSrc19_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = codeMat 141 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * codeMat 141 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc19_le :
    lineSourcePlane ⟨19, by decide⟩ ≤ actionW (codeMat 266) (codeMat 172) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * codeMat 141 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 172) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 172) (codeMat 1) = codeMat 40 := by
      unfold actionA
      rw [lineSrc19_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 141 = codeMat 40
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 172) X = codeMat 40
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc19_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨19, by decide⟩) 18 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 172) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 172) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc19_le hAct

private theorem lineSrc20_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc20_le :
    lineSourcePlane ⟨20, by decide⟩ ≤ actionW (codeMat 273) (codeMat 165) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc20_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 165) (codeMat 20) = codeMat 42 := by
      unfold actionA
      rw [lineSrc20_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 169 = codeMat 42
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 165) X = codeMat 42
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc20_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨20, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 165) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 165) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc20_le hAct

private theorem lineSrc21_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = codeMat 141 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * codeMat 141 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc21_le :
    lineSourcePlane ⟨21, by decide⟩ ≤ actionW (codeMat 267) (codeMat 172) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc21_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * codeMat 141 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 172) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 267) (codeMat 172) (codeMat 17) = codeMat 44 := by
      unfold actionA
      rw [lineSrc21_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 17 * codeMat 141 = codeMat 44
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 172) X = codeMat 44
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc21_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨21, by decide⟩) 18 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 172) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 172) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc21_le hAct

private theorem lineSrc22_QtInv :
    (codeMat 181 : Mat3).transpose⁻¹ = codeMat 489 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 181 : Mat3).transpose * codeMat 489 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc22_le :
    lineSourcePlane ⟨22, by decide⟩ ≤ actionW (codeMat 273) (codeMat 181) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 181) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc22_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 489 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 181) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 273) (codeMat 181) (codeMat 21) = codeMat 46 := by
      unfold actionA
      rw [lineSrc22_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 21 * codeMat 489 = codeMat 46
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 181) X = codeMat 46
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc22_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨22, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 181 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 181) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 181) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc22_le hAct

private theorem lineSrc23_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc23_le :
    lineSourcePlane ⟨23, by decide⟩ ≤ actionW (codeMat 266) (codeMat 394) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 394) (codeMat 1) = codeMat 48 := by
      unfold actionA
      rw [lineSrc23_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 48
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 394) X = codeMat 48
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc23_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨23, by decide⟩) 18 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 394) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 394) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc23_le hAct

private theorem lineSrc24_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc24_le :
    lineSourcePlane ⟨24, by decide⟩ ≤ actionW (codeMat 273) (codeMat 417) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 417) (codeMat 20) = codeMat 50 := by
      unfold actionA
      rw [lineSrc24_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 177 = codeMat 50
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 417) X = codeMat 50
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc24_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨24, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 417) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 417) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc24_le hAct

private theorem lineSrc25_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc25_le :
    lineSourcePlane ⟨25, by decide⟩ ≤ actionW (codeMat 273) (codeMat 401) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 401) (codeMat 20) = codeMat 52 := by
      unfold actionA
      rw [lineSrc25_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 305 = codeMat 52
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 401) X = codeMat 52
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc25_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨25, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 401) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 401) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc25_le hAct

private theorem lineSrc26_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc26_le :
    lineSourcePlane ⟨26, by decide⟩ ≤ actionW (codeMat 267) (codeMat 394) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc26_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 267) (codeMat 394) (codeMat 1) = codeMat 54 := by
      unfold actionA
      rw [lineSrc26_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 54
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 394) X = codeMat 54
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc26_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨26, by decide⟩) 18 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 394) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 394) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc26_le hAct

private theorem lineSrc27_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = codeMat 271 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * codeMat 271 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc27_le :
    lineSourcePlane ⟨27, by decide⟩ ≤ actionW (codeMat 266) (codeMat 410) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 266) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc27_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 16 * codeMat 271 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 410) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 266) (codeMat 410) (codeMat 1) = codeMat 56 := by
      unfold actionA
      rw [lineSrc27_QtInv]
      show (codeMat 266 : Mat3).transpose * codeMat 1 * codeMat 271 = codeMat 56
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 266) (codeMat 410) X = codeMat 56
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc27_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨27, by decide⟩) 18 := by
  have hP : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 266) (codeMat 410) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 266) (codeMat 410) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc27_le hAct

private theorem lineSrc28_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc28_le :
    lineSourcePlane ⟨28, by decide⟩ ≤ actionW (codeMat 273) (codeMat 419) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 273) (codeMat 419) (codeMat 21) = codeMat 58 := by
      unfold actionA
      rw [lineSrc28_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 21 * codeMat 249 = codeMat 58
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 419) X = codeMat 58
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc28_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨28, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 419) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 419) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc28_le hAct

private theorem lineSrc29_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc29_le :
    lineSourcePlane ⟨29, by decide⟩ ≤ actionW (codeMat 273) (codeMat 403) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 273) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc29_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 273) (codeMat 403) (codeMat 20) = codeMat 60 := by
      unfold actionA
      rw [lineSrc29_QtInv]
      show (codeMat 273 : Mat3).transpose * codeMat 20 * codeMat 313 = codeMat 60
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 273) (codeMat 403) X = codeMat 60
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc29_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨29, by decide⟩) 18 := by
  have hP : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 273) (codeMat 403) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 273) (codeMat 403) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc29_le hAct

private theorem lineSrc30_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = codeMat 271 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * codeMat 271 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc30_le :
    lineSourcePlane ⟨30, by decide⟩ ≤ actionW (codeMat 267) (codeMat 410) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 267) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc30_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 16 * codeMat 271 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 410) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 267) (codeMat 410) (codeMat 17) = codeMat 62 := by
      unfold actionA
      rw [lineSrc30_QtInv]
      show (codeMat 267 : Mat3).transpose * codeMat 17 * codeMat 271 = codeMat 62
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 267) (codeMat 410) X = codeMat 62
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc30_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨30, by decide⟩) 18 := by
  have hP : Invertible (codeMat 267 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 267) (codeMat 410) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 267) (codeMat 410) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc30_le hAct

private theorem lineSrc31_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc31_le :
    lineSourcePlane ⟨31, by decide⟩ ≤ actionW (codeMat 140) (codeMat 161) linePlane478T := by
  unfold lineSourcePlane lineSourceCode linePlane478T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 8 ∈ spanCodes [8, 1] :=
      spanContainsCode_implies_mem_spanCodes [8, 1] 8 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 8) = codeMat 1 := by
      unfold actionA
      rw [lineSrc31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 8 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [8, 1] ∧ actionA (codeMat 140) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 8, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [8, 1] :=
      spanContainsCode_implies_mem_spanCodes [8, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 161) (codeMat 1) = codeMat 64 := by
      unfold actionA
      rw [lineSrc31_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 64
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [8, 1] ∧ actionA (codeMat 140) (codeMat 161) X = codeMat 64
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc31_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨31, by decide⟩) 17 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane478T 17 := linePlane478T_lb h478
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 161) linePlane478T) 17 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 161) hP hQ linePlane478T 17 hBase
  exact quotientRankAtLeast_mono lineSrc31_le hAct

end QiushiMatmul
