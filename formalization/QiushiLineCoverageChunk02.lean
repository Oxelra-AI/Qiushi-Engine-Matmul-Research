import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc64_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc64_le :
    lineSourcePlane ⟨64, by decide⟩ ≤ actionW (codeMat 141) (codeMat 266) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc64_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 16 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 141) (codeMat 266) (codeMat 1) = codeMat 130 := by
      unfold actionA
      rw [lineSrc64_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 130
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 266) X = codeMat 130
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc64_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨64, by decide⟩) 18 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 266) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 266) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc64_le hAct

private theorem lineSrc65_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc65_le :
    lineSourcePlane ⟨65, by decide⟩ ≤ actionW (codeMat 161) (codeMat 273) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc65_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 20) = codeMat 132 := by
      unfold actionA
      rw [lineSrc65_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 273 = codeMat 132
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 132
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc65_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨65, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc65_le hAct

private theorem lineSrc66_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc66_le :
    lineSourcePlane ⟨66, by decide⟩ ≤ actionW (codeMat 161) (codeMat 305) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc66_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 20) = codeMat 134 := by
      unfold actionA
      rw [lineSrc66_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 401 = codeMat 134
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 305) X = codeMat 134
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc66_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨66, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 305) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 305) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc66_le hAct

private theorem lineSrc67_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc67_le :
    lineSourcePlane ⟨67, by decide⟩ ≤ actionW (codeMat 161) (codeMat 273) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc67_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 80) = codeMat 136 := by
      unfold actionA
      rw [lineSrc67_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * codeMat 273 = codeMat 136
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 136
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc67_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨67, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc67_le hAct

private theorem lineSrc68_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc68_le :
    lineSourcePlane ⟨68, by decide⟩ ≤ actionW (codeMat 169) (codeMat 273) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc68_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 169) (codeMat 273) (codeMat 80) = codeMat 138 := by
      unfold actionA
      rw [lineSrc68_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 80 * codeMat 273 = codeMat 138
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 273) X = codeMat 138
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc68_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨68, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 273) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 273) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc68_le hAct

private theorem lineSrc69_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc69_le :
    lineSourcePlane ⟨69, by decide⟩ ≤ actionW (codeMat 161) (codeMat 273) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc69_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 273) (codeMat 84) = codeMat 140 := by
      unfold actionA
      rw [lineSrc69_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 273 = codeMat 140
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 273) X = codeMat 140
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc69_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨69, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 273) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 273) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc69_le hAct

private theorem lineSrc70_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc70_le :
    lineSourcePlane ⟨70, by decide⟩ ≤ actionW (codeMat 161) (codeMat 305) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc70_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 84) = codeMat 142 := by
      unfold actionA
      rw [lineSrc70_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 401 = codeMat 142
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 305) X = codeMat 142
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc70_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨70, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 305) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 305) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc70_le hAct

private theorem lineSrc71_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc71_le :
    lineSourcePlane ⟨71, by decide⟩ ≤ actionW (codeMat 142) (codeMat 266) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc71_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 266) (codeMat 1) = codeMat 144 := by
      unfold actionA
      rw [lineSrc71_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 144
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 266) X = codeMat 144
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc71_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨71, by decide⟩) 18 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 266) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 266) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc71_le hAct

private theorem lineSrc72_QtInv :
    (codeMat 266 : Mat3).transpose⁻¹ = codeMat 266 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 266 : Mat3).transpose * codeMat 266 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc72_le :
    lineSourcePlane ⟨72, by decide⟩ ≤ actionW (codeMat 143) (codeMat 266) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 266) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc72_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * codeMat 266 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 266) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 143) (codeMat 266) (codeMat 1) = codeMat 146 := by
      unfold actionA
      rw [lineSrc72_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 1 * codeMat 266 = codeMat 146
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 266) X = codeMat 146
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc72_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨72, by decide⟩) 18 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 266 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 266) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 266) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc72_le hAct

private theorem lineSrc73_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc73_le :
    lineSourcePlane ⟨73, by decide⟩ ≤ actionW (codeMat 177) (codeMat 273) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc73_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 20) = codeMat 148 := by
      unfold actionA
      rw [lineSrc73_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 273 = codeMat 148
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 148
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc73_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨73, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 273) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 273) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc73_le hAct

private theorem lineSrc74_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc74_le :
    lineSourcePlane ⟨74, by decide⟩ ≤ actionW (codeMat 177) (codeMat 305) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc74_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 305) (codeMat 20) = codeMat 150 := by
      unfold actionA
      rw [lineSrc74_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 401 = codeMat 150
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 305) X = codeMat 150
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc74_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨74, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 305) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 305) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc74_le hAct

private theorem lineSrc75_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc75_le :
    lineSourcePlane ⟨75, by decide⟩ ≤ actionW (codeMat 177) (codeMat 273) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 80) = codeMat 152 := by
      unfold actionA
      rw [lineSrc75_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * codeMat 273 = codeMat 152
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 152
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc75_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨75, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 273) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 273) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc75_le hAct

private theorem lineSrc76_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc76_le :
    lineSourcePlane ⟨76, by decide⟩ ≤ actionW (codeMat 185) (codeMat 273) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc76_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 185) (codeMat 273) (codeMat 80) = codeMat 154 := by
      unfold actionA
      rw [lineSrc76_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 80 * codeMat 273 = codeMat 154
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 273) X = codeMat 154
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc76_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨76, by decide⟩) 18 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 273) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 273) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc76_le hAct

private theorem lineSrc77_QtInv :
    (codeMat 273 : Mat3).transpose⁻¹ = codeMat 273 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 273 : Mat3).transpose * codeMat 273 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc77_le :
    lineSourcePlane ⟨77, by decide⟩ ≤ actionW (codeMat 177) (codeMat 273) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc77_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 273 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 273) (codeMat 84) = codeMat 156 := by
      unfold actionA
      rw [lineSrc77_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 273 = codeMat 156
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 273) X = codeMat 156
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc77_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨77, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 273 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 273) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 273) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc77_le hAct

private theorem lineSrc78_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc78_le :
    lineSourcePlane ⟨78, by decide⟩ ≤ actionW (codeMat 177) (codeMat 305) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc78_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 305) (codeMat 84) = codeMat 158 := by
      unfold actionA
      rw [lineSrc78_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 401 = codeMat 158
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 305) X = codeMat 158
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc78_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨78, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 305) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 305) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc78_le hAct

private theorem lineSrc79_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc79_le :
    lineSourcePlane ⟨79, by decide⟩ ≤ actionW (codeMat 161) (codeMat 161) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc79_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 161) (codeMat 160) = codeMat 160 := by
      unfold actionA
      rw [lineSrc79_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 161 = codeMat 160
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 161) X = codeMat 160
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc79_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨79, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 161) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 161) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc79_le hAct

private theorem lineSrc80_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc80_le :
    lineSourcePlane ⟨80, by decide⟩ ≤ actionW (codeMat 169) (codeMat 161) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc80_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 161) (codeMat 160) = codeMat 162 := by
      unfold actionA
      rw [lineSrc80_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 161 = codeMat 162
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 161) X = codeMat 162
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc80_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨80, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 161) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 161) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc80_le hAct

private theorem lineSrc81_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc81_le :
    lineSourcePlane ⟨81, by decide⟩ ≤ actionW (codeMat 225) (codeMat 161) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc81_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 161) (codeMat 160) = codeMat 164 := by
      unfold actionA
      rw [lineSrc81_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 161 = codeMat 164
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 161) X = codeMat 164
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc81_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨81, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 161) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 161) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc81_le hAct

private theorem lineSrc82_QtInv :
    (codeMat 161 : Mat3).transpose⁻¹ = codeMat 161 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 161 : Mat3).transpose * codeMat 161 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc82_le :
    lineSourcePlane ⟨82, by decide⟩ ≤ actionW (codeMat 233) (codeMat 161) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc82_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 161 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 161) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 161) (codeMat 160) = codeMat 166 := by
      unfold actionA
      rw [lineSrc82_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 161 = codeMat 166
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 161) X = codeMat 166
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc82_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨82, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 161) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 161) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc82_le hAct

private theorem lineSrc83_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc83_le :
    lineSourcePlane ⟨83, by decide⟩ ≤ actionW (codeMat 161) (codeMat 165) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc83_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 165) (codeMat 160) = codeMat 168 := by
      unfold actionA
      rw [lineSrc83_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 169 = codeMat 168
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 165) X = codeMat 168
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc83_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨83, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 165) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 165) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc83_le hAct

private theorem lineSrc84_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc84_le :
    lineSourcePlane ⟨84, by decide⟩ ≤ actionW (codeMat 169) (codeMat 165) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc84_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 165) (codeMat 160) = codeMat 170 := by
      unfold actionA
      rw [lineSrc84_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 169 = codeMat 170
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 165) X = codeMat 170
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc84_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨84, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 165) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 165) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc84_le hAct

private theorem lineSrc85_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc85_le :
    lineSourcePlane ⟨85, by decide⟩ ≤ actionW (codeMat 225) (codeMat 165) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc85_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 165) (codeMat 161) = codeMat 172 := by
      unfold actionA
      rw [lineSrc85_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 169 = codeMat 172
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 165) X = codeMat 172
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc85_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨85, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 165) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 165) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc85_le hAct

private theorem lineSrc86_QtInv :
    (codeMat 165 : Mat3).transpose⁻¹ = codeMat 169 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 165 : Mat3).transpose * codeMat 169 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc86_le :
    lineSourcePlane ⟨86, by decide⟩ ≤ actionW (codeMat 233) (codeMat 165) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 165) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc86_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 169 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 165) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 165) (codeMat 161) = codeMat 174 := by
      unfold actionA
      rw [lineSrc86_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 169 = codeMat 174
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 165) X = codeMat 174
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc86_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨86, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 165 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 165) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 165) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc86_le hAct

private theorem lineSrc87_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc87_le :
    lineSourcePlane ⟨87, by decide⟩ ≤ actionW (codeMat 161) (codeMat 417) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc87_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 417) (codeMat 160) = codeMat 176 := by
      unfold actionA
      rw [lineSrc87_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 177 = codeMat 176
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 417) X = codeMat 176
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc87_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨87, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 417) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 417) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc87_le hAct

private theorem lineSrc88_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc88_le :
    lineSourcePlane ⟨88, by decide⟩ ≤ actionW (codeMat 169) (codeMat 417) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc88_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 417) (codeMat 160) = codeMat 178 := by
      unfold actionA
      rw [lineSrc88_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 177 = codeMat 178
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 417) X = codeMat 178
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc88_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨88, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 417) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 417) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc88_le hAct

private theorem lineSrc89_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc89_le :
    lineSourcePlane ⟨89, by decide⟩ ≤ actionW (codeMat 233) (codeMat 417) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc89_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 417) (codeMat 160) = codeMat 180 := by
      unfold actionA
      rw [lineSrc89_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 177 = codeMat 180
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 417) X = codeMat 180
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc89_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨89, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 417) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 417) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc89_le hAct

private theorem lineSrc90_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc90_le :
    lineSourcePlane ⟨90, by decide⟩ ≤ actionW (codeMat 225) (codeMat 417) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc90_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 417) (codeMat 160) = codeMat 182 := by
      unfold actionA
      rw [lineSrc90_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 177 = codeMat 182
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 417) X = codeMat 182
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc90_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨90, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 417) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 417) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc90_le hAct

private theorem lineSrc91_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = codeMat 185 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * codeMat 185 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc91_le :
    lineSourcePlane ⟨91, by decide⟩ ≤ actionW (codeMat 161) (codeMat 421) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc91_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 185 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 421) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 421) (codeMat 160) = codeMat 184 := by
      unfold actionA
      rw [lineSrc91_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 185 = codeMat 184
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 421) X = codeMat 184
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc91_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨91, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 421) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 421) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc91_le hAct

private theorem lineSrc92_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = codeMat 185 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * codeMat 185 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc92_le :
    lineSourcePlane ⟨92, by decide⟩ ≤ actionW (codeMat 169) (codeMat 421) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc92_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 185 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 421) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 421) (codeMat 160) = codeMat 186 := by
      unfold actionA
      rw [lineSrc92_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 185 = codeMat 186
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 421) X = codeMat 186
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc92_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨92, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 421) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 421) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc92_le hAct

private theorem lineSrc93_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = codeMat 185 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * codeMat 185 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc93_le :
    lineSourcePlane ⟨93, by decide⟩ ≤ actionW (codeMat 233) (codeMat 421) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc93_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 185 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 421) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 421) (codeMat 161) = codeMat 188 := by
      unfold actionA
      rw [lineSrc93_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 185 = codeMat 188
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 421) X = codeMat 188
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc93_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨93, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 421) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 421) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc93_le hAct

private theorem lineSrc94_QtInv :
    (codeMat 421 : Mat3).transpose⁻¹ = codeMat 185 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 421 : Mat3).transpose * codeMat 185 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc94_le :
    lineSourcePlane ⟨94, by decide⟩ ≤ actionW (codeMat 225) (codeMat 421) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 421) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc94_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 185 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 421) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 421) (codeMat 161) = codeMat 190 := by
      unfold actionA
      rw [lineSrc94_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 185 = codeMat 190
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 421) X = codeMat 190
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc94_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨94, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 421 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 421) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 421) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc94_le hAct

private theorem lineSrc95_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = codeMat 267 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * codeMat 267 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc95_le :
    lineSourcePlane ⟨95, by decide⟩ ≤ actionW (codeMat 140) (codeMat 282) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc95_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * codeMat 267 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 282) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 282) (codeMat 1) = codeMat 192 := by
      unfold actionA
      rw [lineSrc95_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 267 = codeMat 192
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 282) X = codeMat 192
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc95_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨95, by decide⟩) 18 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 282) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 282) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc95_le hAct

end QiushiMatmul
