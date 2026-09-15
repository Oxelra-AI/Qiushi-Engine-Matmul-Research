import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc128_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc128_le :
    lineSourcePlane ⟨128, by decide⟩ ≤ actionW (codeMat 161) (codeMat 161) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc128_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 20) = codeMat 258 := by
      unfold actionA
      rw [lineSrc128_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 161 = codeMat 258
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 258
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc128_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨128, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc128_le hAct

private theorem lineSrc129_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc129_le :
    lineSourcePlane ⟨129, by decide⟩ ≤ actionW (codeMat 141) (codeMat 140) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 141) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc129_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 16 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 141) (codeMat 140) (codeMat 1) = codeMat 260 := by
      unfold actionA
      rw [lineSrc129_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 260
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 140) X = codeMat 260
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc129_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨129, by decide⟩) 18 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 140) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 140) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc129_le hAct

private theorem lineSrc130_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc130_le :
    lineSourcePlane ⟨130, by decide⟩ ≤ actionW (codeMat 161) (codeMat 177) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc130_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 177) (codeMat 20) = codeMat 262 := by
      unfold actionA
      rw [lineSrc130_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 417 = codeMat 262
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 177) X = codeMat 262
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc130_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨130, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 177) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 177) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc130_le hAct

private theorem lineSrc131_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc131_le :
    lineSourcePlane ⟨131, by decide⟩ ≤ actionW (codeMat 161) (codeMat 161) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc131_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 80) = codeMat 264 := by
      unfold actionA
      rw [lineSrc131_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * codeMat 161 = codeMat 264
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 264
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc131_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨131, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc131_le hAct

private theorem lineSrc132_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc132_le :
    lineSourcePlane ⟨132, by decide⟩ ≤ actionW (codeMat 161) (codeMat 161) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc132_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 84) = codeMat 266 := by
      unfold actionA
      rw [lineSrc132_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 161 = codeMat 266
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 266
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc132_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨132, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc132_le hAct

private theorem lineSrc133_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc133_le :
    lineSourcePlane ⟨133, by decide⟩ ≤ actionW (codeMat 169) (codeMat 161) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc133_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 80) = codeMat 268 := by
      unfold actionA
      rw [lineSrc133_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 80 * codeMat 161 = codeMat 268
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 161) X = codeMat 268
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc133_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨133, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 161) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 161) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc133_le hAct

private theorem lineSrc134_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc134_le :
    lineSourcePlane ⟨134, by decide⟩ ≤ actionW (codeMat 161) (codeMat 177) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc134_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 177) (codeMat 84) = codeMat 270 := by
      unfold actionA
      rw [lineSrc134_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 417 = codeMat 270
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 177) X = codeMat 270
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc134_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨134, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 177) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 177) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc134_le hAct

private theorem lineSrc135_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc135_le :
    lineSourcePlane ⟨135, by decide⟩ ≤ actionW (codeMat 161) (codeMat 273) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc135_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 160) = codeMat 272 := by
      unfold actionA
      rw [lineSrc135_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 273 = codeMat 272
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 272
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc135_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨135, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc135_le hAct

private theorem lineSrc136_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc136_le :
    lineSourcePlane ⟨136, by decide⟩ ≤ actionW (codeMat 225) (codeMat 273) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc136_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 273) (codeMat 160) = codeMat 274 := by
      unfold actionA
      rw [lineSrc136_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 273 = codeMat 274
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 273) X = codeMat 274
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc136_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨136, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 273) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 273) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc136_le hAct

private theorem lineSrc137_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc137_le :
    lineSourcePlane ⟨137, by decide⟩ ≤ actionW (codeMat 169) (codeMat 273) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc137_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 273) (codeMat 160) = codeMat 276 := by
      unfold actionA
      rw [lineSrc137_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 273 = codeMat 276
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 273) X = codeMat 276
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc137_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨137, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 273) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 273) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc137_le hAct

private theorem lineSrc138_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc138_le :
    lineSourcePlane ⟨138, by decide⟩ ≤ actionW (codeMat 233) (codeMat 273) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc138_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 273) (codeMat 160) = codeMat 278 := by
      unfold actionA
      rw [lineSrc138_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 273 = codeMat 278
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 273) X = codeMat 278
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc138_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨138, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 273) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 273) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc138_le hAct

private theorem lineSrc139_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc139_le :
    lineSourcePlane ⟨139, by decide⟩ ≤ actionW (codeMat 161) (codeMat 275) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc139_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 160) = codeMat 280 := by
      unfold actionA
      rw [lineSrc139_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 281 = codeMat 280
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 280
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc139_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨139, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 275) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 275) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc139_le hAct

private theorem lineSrc140_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc140_le :
    lineSourcePlane ⟨140, by decide⟩ ≤ actionW (codeMat 225) (codeMat 275) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc140_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 275) (codeMat 161) = codeMat 282 := by
      unfold actionA
      rw [lineSrc140_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 281 = codeMat 282
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 275) X = codeMat 282
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc140_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨140, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 275) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 275) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc140_le hAct

private theorem lineSrc141_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc141_le :
    lineSourcePlane ⟨141, by decide⟩ ≤ actionW (codeMat 169) (codeMat 275) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc141_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 275) (codeMat 160) = codeMat 284 := by
      unfold actionA
      rw [lineSrc141_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 281 = codeMat 284
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 275) X = codeMat 284
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc141_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨141, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 275) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 275) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc141_le hAct

private theorem lineSrc142_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc142_le :
    lineSourcePlane ⟨142, by decide⟩ ≤ actionW (codeMat 233) (codeMat 275) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc142_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 275) (codeMat 161) = codeMat 286 := by
      unfold actionA
      rw [lineSrc142_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 281 = codeMat 286
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 275) X = codeMat 286
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc142_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨142, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 275) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 275) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc142_le hAct

private theorem lineSrc143_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc143_le :
    lineSourcePlane ⟨143, by decide⟩ ≤ actionW (codeMat 142) (codeMat 140) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc143_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 140) (codeMat 1) = codeMat 288 := by
      unfold actionA
      rw [lineSrc143_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 288
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 140) X = codeMat 288
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc143_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨143, by decide⟩) 18 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 140) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 140) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc143_le hAct

private theorem lineSrc144_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc144_le :
    lineSourcePlane ⟨144, by decide⟩ ≤ actionW (codeMat 177) (codeMat 161) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc144_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 20) = codeMat 290 := by
      unfold actionA
      rw [lineSrc144_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 161 = codeMat 290
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 290
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc144_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨144, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 161) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 161) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc144_le hAct

private theorem lineSrc145_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc145_le :
    lineSourcePlane ⟨145, by decide⟩ ≤ actionW (codeMat 143) (codeMat 140) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc145_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 143) (codeMat 140) (codeMat 1) = codeMat 292 := by
      unfold actionA
      rw [lineSrc145_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 292
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 140) X = codeMat 292
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc145_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨145, by decide⟩) 18 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 140) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 140) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc145_le hAct

private theorem lineSrc146_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc146_le :
    lineSourcePlane ⟨146, by decide⟩ ≤ actionW (codeMat 177) (codeMat 177) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc146_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 177) (codeMat 20) = codeMat 294 := by
      unfold actionA
      rw [lineSrc146_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 417 = codeMat 294
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 177) X = codeMat 294
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc146_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨146, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 177) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 177) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc146_le hAct

private theorem lineSrc147_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc147_le :
    lineSourcePlane ⟨147, by decide⟩ ≤ actionW (codeMat 177) (codeMat 161) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc147_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 80) = codeMat 296 := by
      unfold actionA
      rw [lineSrc147_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * codeMat 161 = codeMat 296
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 296
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc147_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨147, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 161) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 161) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc147_le hAct

private theorem lineSrc148_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc148_le :
    lineSourcePlane ⟨148, by decide⟩ ≤ actionW (codeMat 177) (codeMat 161) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc148_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 161) (codeMat 84) = codeMat 298 := by
      unfold actionA
      rw [lineSrc148_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 161 = codeMat 298
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 161) X = codeMat 298
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc148_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨148, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 161) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 161) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc148_le hAct

private theorem lineSrc149_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc149_le :
    lineSourcePlane ⟨149, by decide⟩ ≤ actionW (codeMat 185) (codeMat 161) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc149_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 185) (codeMat 161) (codeMat 80) = codeMat 300 := by
      unfold actionA
      rw [lineSrc149_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 80 * codeMat 161 = codeMat 300
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 161) X = codeMat 300
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc149_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨149, by decide⟩) 18 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 161) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 161) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc149_le hAct

private theorem lineSrc150_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc150_le :
    lineSourcePlane ⟨150, by decide⟩ ≤ actionW (codeMat 177) (codeMat 177) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc150_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 177) (codeMat 84) = codeMat 302 := by
      unfold actionA
      rw [lineSrc150_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 417 = codeMat 302
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 177) X = codeMat 302
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc150_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨150, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 177) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 177) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc150_le hAct

private theorem lineSrc151_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc151_le :
    lineSourcePlane ⟨151, by decide⟩ ≤ actionW (codeMat 161) (codeMat 401) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc151_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 160) = codeMat 304 := by
      unfold actionA
      rw [lineSrc151_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 305 = codeMat 304
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 304
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc151_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨151, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 401) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 401) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc151_le hAct

private theorem lineSrc152_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc152_le :
    lineSourcePlane ⟨152, by decide⟩ ≤ actionW (codeMat 233) (codeMat 401) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc152_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 401) (codeMat 160) = codeMat 306 := by
      unfold actionA
      rw [lineSrc152_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 305 = codeMat 306
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 401) X = codeMat 306
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc152_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨152, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 401) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 401) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc152_le hAct

private theorem lineSrc153_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc153_le :
    lineSourcePlane ⟨153, by decide⟩ ≤ actionW (codeMat 169) (codeMat 401) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc153_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 401) (codeMat 160) = codeMat 308 := by
      unfold actionA
      rw [lineSrc153_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 305 = codeMat 308
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 401) X = codeMat 308
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc153_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨153, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 401) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 401) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc153_le hAct

private theorem lineSrc154_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc154_le :
    lineSourcePlane ⟨154, by decide⟩ ≤ actionW (codeMat 225) (codeMat 401) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc154_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 401) (codeMat 160) = codeMat 310 := by
      unfold actionA
      rw [lineSrc154_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 305 = codeMat 310
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 401) X = codeMat 310
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc154_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨154, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 401) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 401) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc154_le hAct

private theorem lineSrc155_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc155_le :
    lineSourcePlane ⟨155, by decide⟩ ≤ actionW (codeMat 161) (codeMat 403) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc155_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 403) (codeMat 160) = codeMat 312 := by
      unfold actionA
      rw [lineSrc155_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 313 = codeMat 312
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 403) X = codeMat 312
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc155_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨155, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 403) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 403) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc155_le hAct

private theorem lineSrc156_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc156_le :
    lineSourcePlane ⟨156, by decide⟩ ≤ actionW (codeMat 233) (codeMat 403) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc156_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 403) (codeMat 161) = codeMat 314 := by
      unfold actionA
      rw [lineSrc156_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 313 = codeMat 314
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 403) X = codeMat 314
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc156_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨156, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 403) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 403) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc156_le hAct

private theorem lineSrc157_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc157_le :
    lineSourcePlane ⟨157, by decide⟩ ≤ actionW (codeMat 169) (codeMat 403) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc157_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 403) (codeMat 160) = codeMat 316 := by
      unfold actionA
      rw [lineSrc157_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 313 = codeMat 316
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 403) X = codeMat 316
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc157_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨157, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 403) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 403) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc157_le hAct

private theorem lineSrc158_QtInv :
    (codeMat 403 : Mat3).transpose⁻¹ = codeMat 313 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 403 : Mat3).transpose * codeMat 313 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc158_le :
    lineSourcePlane ⟨158, by decide⟩ ≤ actionW (codeMat 225) (codeMat 403) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 403) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc158_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 313 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 403) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 403) (codeMat 161) = codeMat 318 := by
      unfold actionA
      rw [lineSrc158_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 313 = codeMat 318
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 403) X = codeMat 318
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc158_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨158, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 403 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 403) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 403) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc158_le hAct

private theorem lineSrc159_QtInv :
    (codeMat 172 : Mat3).transpose⁻¹ = codeMat 141 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 172 : Mat3).transpose * codeMat 141 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc159_le :
    lineSourcePlane ⟨159, by decide⟩ ≤ actionW (codeMat 140) (codeMat 172) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc159_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * codeMat 141 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 172) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 172) (codeMat 1) = codeMat 320 := by
      unfold actionA
      rw [lineSrc159_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 141 = codeMat 320
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 172) X = codeMat 320
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc159_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨159, by decide⟩) 18 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 172 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 172) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 172) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc159_le hAct

end QiushiMatmul
