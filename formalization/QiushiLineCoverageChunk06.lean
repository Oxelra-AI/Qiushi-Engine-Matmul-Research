import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc192_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc192_le :
    lineSourcePlane ⟨192, by decide⟩ ≤ actionW (codeMat 161) (codeMat 417) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc192_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 417) (codeMat 20) = codeMat 386 := by
      unfold actionA
      rw [lineSrc192_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 177 = codeMat 386
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 417) X = codeMat 386
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc192_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨192, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 417) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 417) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc192_le hAct

private theorem lineSrc193_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc193_le :
    lineSourcePlane ⟨193, by decide⟩ ≤ actionW (codeMat 161) (codeMat 401) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc193_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 20) = codeMat 388 := by
      unfold actionA
      rw [lineSrc193_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 305 = codeMat 388
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 388
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc193_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨193, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 401) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 401) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc193_le hAct

private theorem lineSrc194_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc194_le :
    lineSourcePlane ⟨194, by decide⟩ ≤ actionW (codeMat 141) (codeMat 394) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 141) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc194_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 16 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 141) (codeMat 394) (codeMat 1) = codeMat 390 := by
      unfold actionA
      rw [lineSrc194_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 390
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 394) X = codeMat 390
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc194_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨194, by decide⟩) 18 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 394) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 394) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc194_le hAct

private theorem lineSrc195_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc195_le :
    lineSourcePlane ⟨195, by decide⟩ ≤ actionW (codeMat 161) (codeMat 401) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc195_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 80) = codeMat 392 := by
      unfold actionA
      rw [lineSrc195_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * codeMat 305 = codeMat 392
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 392
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc195_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨195, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 401) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 401) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc195_le hAct

private theorem lineSrc196_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc196_le :
    lineSourcePlane ⟨196, by decide⟩ ≤ actionW (codeMat 161) (codeMat 417) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc196_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 417) (codeMat 84) = codeMat 394 := by
      unfold actionA
      rw [lineSrc196_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 177 = codeMat 394
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 417) X = codeMat 394
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc196_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨196, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 417) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 417) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc196_le hAct

private theorem lineSrc197_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc197_le :
    lineSourcePlane ⟨197, by decide⟩ ≤ actionW (codeMat 161) (codeMat 401) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc197_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 401) (codeMat 84) = codeMat 396 := by
      unfold actionA
      rw [lineSrc197_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 305 = codeMat 396
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 401) X = codeMat 396
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc197_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨197, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 401) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 401) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc197_le hAct

private theorem lineSrc198_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc198_le :
    lineSourcePlane ⟨198, by decide⟩ ≤ actionW (codeMat 169) (codeMat 401) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc198_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 169) (codeMat 401) (codeMat 80) = codeMat 398 := by
      unfold actionA
      rw [lineSrc198_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 80 * codeMat 305 = codeMat 398
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 401) X = codeMat 398
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc198_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨198, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 401) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 401) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc198_le hAct

private theorem lineSrc199_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc199_le :
    lineSourcePlane ⟨199, by decide⟩ ≤ actionW (codeMat 161) (codeMat 305) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc199_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 305) (codeMat 160) = codeMat 400 := by
      unfold actionA
      rw [lineSrc199_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 401 = codeMat 400
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 305) X = codeMat 400
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc199_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨199, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 305) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 305) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc199_le hAct

private theorem lineSrc200_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc200_le :
    lineSourcePlane ⟨200, by decide⟩ ≤ actionW (codeMat 225) (codeMat 305) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc200_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 305) (codeMat 160) = codeMat 402 := by
      unfold actionA
      rw [lineSrc200_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 401 = codeMat 402
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 305) X = codeMat 402
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc200_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨200, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 305) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 305) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc200_le hAct

private theorem lineSrc201_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc201_le :
    lineSourcePlane ⟨201, by decide⟩ ≤ actionW (codeMat 233) (codeMat 305) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc201_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 305) (codeMat 160) = codeMat 404 := by
      unfold actionA
      rw [lineSrc201_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 401 = codeMat 404
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 305) X = codeMat 404
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc201_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨201, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 305) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 305) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc201_le hAct

private theorem lineSrc202_QtInv :
    (codeMat 305 : Mat3).transpose⁻¹ = codeMat 401 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 305 : Mat3).transpose * codeMat 401 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc202_le :
    lineSourcePlane ⟨202, by decide⟩ ≤ actionW (codeMat 169) (codeMat 305) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 305) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc202_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 401 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 305) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 305) (codeMat 160) = codeMat 406 := by
      unfold actionA
      rw [lineSrc202_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 401 = codeMat 406
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 305) X = codeMat 406
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc202_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨202, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 305 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 305) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 305) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc202_le hAct

private theorem lineSrc203_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = codeMat 409 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * codeMat 409 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc203_le :
    lineSourcePlane ⟨203, by decide⟩ ≤ actionW (codeMat 161) (codeMat 311) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc203_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 409 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 311) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 311) (codeMat 160) = codeMat 408 := by
      unfold actionA
      rw [lineSrc203_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 409 = codeMat 408
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 311) X = codeMat 408
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc203_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨203, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 311) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 311) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc203_le hAct

private theorem lineSrc204_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = codeMat 409 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * codeMat 409 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc204_le :
    lineSourcePlane ⟨204, by decide⟩ ≤ actionW (codeMat 225) (codeMat 311) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc204_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 409 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 311) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 311) (codeMat 161) = codeMat 410 := by
      unfold actionA
      rw [lineSrc204_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 409 = codeMat 410
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 311) X = codeMat 410
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc204_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨204, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 311) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 311) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc204_le hAct

private theorem lineSrc205_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = codeMat 409 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * codeMat 409 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc205_le :
    lineSourcePlane ⟨205, by decide⟩ ≤ actionW (codeMat 233) (codeMat 311) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc205_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 409 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 311) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 311) (codeMat 161) = codeMat 412 := by
      unfold actionA
      rw [lineSrc205_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 409 = codeMat 412
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 311) X = codeMat 412
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc205_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨205, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 311) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 311) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc205_le hAct

private theorem lineSrc206_QtInv :
    (codeMat 311 : Mat3).transpose⁻¹ = codeMat 409 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 311 : Mat3).transpose * codeMat 409 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc206_le :
    lineSourcePlane ⟨206, by decide⟩ ≤ actionW (codeMat 169) (codeMat 311) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 311) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc206_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 409 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 311) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 311) (codeMat 160) = codeMat 414 := by
      unfold actionA
      rw [lineSrc206_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 409 = codeMat 414
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 311) X = codeMat 414
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc206_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨206, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 311 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 311) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 311) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc206_le hAct

private theorem lineSrc207_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc207_le :
    lineSourcePlane ⟨207, by decide⟩ ≤ actionW (codeMat 161) (codeMat 177) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc207_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 177) (codeMat 160) = codeMat 416 := by
      unfold actionA
      rw [lineSrc207_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 417 = codeMat 416
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 177) X = codeMat 416
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc207_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨207, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 177) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 177) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc207_le hAct

private theorem lineSrc208_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc208_le :
    lineSourcePlane ⟨208, by decide⟩ ≤ actionW (codeMat 233) (codeMat 177) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc208_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 177) (codeMat 160) = codeMat 418 := by
      unfold actionA
      rw [lineSrc208_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 417 = codeMat 418
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 177) X = codeMat 418
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc208_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨208, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 177) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 177) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc208_le hAct

private theorem lineSrc209_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc209_le :
    lineSourcePlane ⟨209, by decide⟩ ≤ actionW (codeMat 225) (codeMat 177) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc209_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 177) (codeMat 160) = codeMat 420 := by
      unfold actionA
      rw [lineSrc209_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 417 = codeMat 420
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 177) X = codeMat 420
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc209_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨209, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 177) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 177) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc209_le hAct

private theorem lineSrc210_QtInv :
    (codeMat 177 : Mat3).transpose⁻¹ = codeMat 417 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 177 : Mat3).transpose * codeMat 417 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc210_le :
    lineSourcePlane ⟨210, by decide⟩ ≤ actionW (codeMat 169) (codeMat 177) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 177) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc210_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 417 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 177) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 177) (codeMat 160) = codeMat 422 := by
      unfold actionA
      rw [lineSrc210_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 417 = codeMat 422
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 177) X = codeMat 422
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc210_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨210, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 177) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 177) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc210_le hAct

private theorem lineSrc211_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = codeMat 425 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * codeMat 425 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc211_le :
    lineSourcePlane ⟨211, by decide⟩ ≤ actionW (codeMat 161) (codeMat 183) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc211_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 425 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 183) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 183) (codeMat 160) = codeMat 424 := by
      unfold actionA
      rw [lineSrc211_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 425 = codeMat 424
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 183) X = codeMat 424
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc211_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨211, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 183) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 183) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc211_le hAct

private theorem lineSrc212_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = codeMat 425 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * codeMat 425 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc212_le :
    lineSourcePlane ⟨212, by decide⟩ ≤ actionW (codeMat 233) (codeMat 183) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc212_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 425 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 183) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 183) (codeMat 161) = codeMat 426 := by
      unfold actionA
      rw [lineSrc212_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 425 = codeMat 426
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 183) X = codeMat 426
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc212_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨212, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 183) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 183) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc212_le hAct

private theorem lineSrc213_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = codeMat 425 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * codeMat 425 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc213_le :
    lineSourcePlane ⟨213, by decide⟩ ≤ actionW (codeMat 225) (codeMat 183) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc213_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 425 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 183) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 183) (codeMat 161) = codeMat 428 := by
      unfold actionA
      rw [lineSrc213_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 425 = codeMat 428
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 183) X = codeMat 428
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc213_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨213, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 183) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 183) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc213_le hAct

private theorem lineSrc214_QtInv :
    (codeMat 183 : Mat3).transpose⁻¹ = codeMat 425 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 183 : Mat3).transpose * codeMat 425 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc214_le :
    lineSourcePlane ⟨214, by decide⟩ ≤ actionW (codeMat 169) (codeMat 183) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 183) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc214_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 425 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 183) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 169) (codeMat 183) (codeMat 160) = codeMat 430 := by
      unfold actionA
      rw [lineSrc214_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 160 * codeMat 425 = codeMat 430
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 183) X = codeMat 430
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc214_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨214, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 183 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 183) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 183) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc214_le hAct

private theorem lineSrc215_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc215_le :
    lineSourcePlane ⟨215, by decide⟩ ≤ actionW (codeMat 142) (codeMat 394) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc215_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 394) (codeMat 1) = codeMat 432 := by
      unfold actionA
      rw [lineSrc215_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 432
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 394) X = codeMat 432
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc215_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨215, by decide⟩) 18 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 394) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 394) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc215_le hAct

private theorem lineSrc216_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc216_le :
    lineSourcePlane ⟨216, by decide⟩ ≤ actionW (codeMat 177) (codeMat 417) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc216_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 20) = codeMat 434 := by
      unfold actionA
      rw [lineSrc216_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 177 = codeMat 434
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 417) X = codeMat 434
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc216_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨216, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 417) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 417) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc216_le hAct

private theorem lineSrc217_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc217_le :
    lineSourcePlane ⟨217, by decide⟩ ≤ actionW (codeMat 177) (codeMat 401) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc217_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 20) = codeMat 436 := by
      unfold actionA
      rw [lineSrc217_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 305 = codeMat 436
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 436
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc217_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨217, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 401) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 401) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc217_le hAct

private theorem lineSrc218_QtInv :
    (codeMat 394 : Mat3).transpose⁻¹ = codeMat 270 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 394 : Mat3).transpose * codeMat 270 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc218_le :
    lineSourcePlane ⟨218, by decide⟩ ≤ actionW (codeMat 143) (codeMat 394) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc218_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * codeMat 270 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 394) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 143) (codeMat 394) (codeMat 1) = codeMat 438 := by
      unfold actionA
      rw [lineSrc218_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 1 * codeMat 270 = codeMat 438
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 394) X = codeMat 438
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc218_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨218, by decide⟩) 18 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 394 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 394) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 394) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc218_le hAct

private theorem lineSrc219_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc219_le :
    lineSourcePlane ⟨219, by decide⟩ ≤ actionW (codeMat 177) (codeMat 401) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc219_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 80) = codeMat 440 := by
      unfold actionA
      rw [lineSrc219_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * codeMat 305 = codeMat 440
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 440
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc219_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨219, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 401) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 401) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc219_le hAct

private theorem lineSrc220_QtInv :
    (codeMat 417 : Mat3).transpose⁻¹ = codeMat 177 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 417 : Mat3).transpose * codeMat 177 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc220_le :
    lineSourcePlane ⟨220, by decide⟩ ≤ actionW (codeMat 177) (codeMat 417) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc220_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 177 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 417) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 417) (codeMat 84) = codeMat 442 := by
      unfold actionA
      rw [lineSrc220_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 177 = codeMat 442
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 417) X = codeMat 442
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc220_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨220, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 417 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 417) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 417) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc220_le hAct

private theorem lineSrc221_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc221_le :
    lineSourcePlane ⟨221, by decide⟩ ≤ actionW (codeMat 177) (codeMat 401) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc221_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 401) (codeMat 84) = codeMat 444 := by
      unfold actionA
      rw [lineSrc221_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 305 = codeMat 444
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 401) X = codeMat 444
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc221_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨221, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 401) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 401) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc221_le hAct

private theorem lineSrc222_QtInv :
    (codeMat 401 : Mat3).transpose⁻¹ = codeMat 305 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 401 : Mat3).transpose * codeMat 305 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc222_le :
    lineSourcePlane ⟨222, by decide⟩ ≤ actionW (codeMat 185) (codeMat 401) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 401) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc222_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * codeMat 305 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 401) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 185) (codeMat 401) (codeMat 80) = codeMat 446 := by
      unfold actionA
      rw [lineSrc222_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 80 * codeMat 305 = codeMat 446
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 401) X = codeMat 446
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc222_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨222, by decide⟩) 18 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 401 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 401) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 401) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc222_le hAct

private theorem lineSrc223_QtInv :
    (codeMat 410 : Mat3).transpose⁻¹ = codeMat 271 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 410 : Mat3).transpose * codeMat 271 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc223_le :
    lineSourcePlane ⟨223, by decide⟩ ≤ actionW (codeMat 140) (codeMat 410) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc223_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * codeMat 271 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 410) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 410) (codeMat 1) = codeMat 448 := by
      unfold actionA
      rw [lineSrc223_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 271 = codeMat 448
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 410) X = codeMat 448
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc223_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨223, by decide⟩) 18 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 410 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 410) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 410) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc223_le hAct

end QiushiMatmul
