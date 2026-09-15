import QiushiLineCoverageDefs

set_option maxHeartbeats 80000000
set_option synthInstance.maxHeartbeats 80000000
set_option maxRecDepth 1000000
open BigOperators Finset Matrix
namespace QiushiMatmul

private theorem lineSrc96_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = codeMat 267 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * codeMat 267 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc96_le :
    lineSourcePlane ⟨96, by decide⟩ ≤ actionW (codeMat 141) (codeMat 282) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 141) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc96_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 16 * codeMat 267 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 282) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 141) (codeMat 282) (codeMat 17) = codeMat 194 := by
      unfold actionA
      rw [lineSrc96_QtInv]
      show (codeMat 141 : Mat3).transpose * codeMat 17 * codeMat 267 = codeMat 194
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 141) (codeMat 282) X = codeMat 194
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc96_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨96, by decide⟩) 18 := by
  have hP : Invertible (codeMat 141 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 141) (codeMat 282) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 141) (codeMat 282) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc96_le hAct

private theorem lineSrc97_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc97_le :
    lineSourcePlane ⟨97, by decide⟩ ≤ actionW (codeMat 161) (codeMat 275) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc97_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 20) = codeMat 196 := by
      unfold actionA
      rw [lineSrc97_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 20 * codeMat 281 = codeMat 196
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 196
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc97_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨97, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 275) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 275) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc97_le hAct

private theorem lineSrc98_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc98_le :
    lineSourcePlane ⟨98, by decide⟩ ≤ actionW (codeMat 161) (codeMat 307) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc98_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 161) (codeMat 307) (codeMat 21) = codeMat 198 := by
      unfold actionA
      rw [lineSrc98_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 21 * codeMat 473 = codeMat 198
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 161) (codeMat 307) X = codeMat 198
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc98_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨98, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 307) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 307) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc98_le hAct

private theorem lineSrc99_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc99_le :
    lineSourcePlane ⟨99, by decide⟩ ≤ actionW (codeMat 161) (codeMat 275) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc99_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 80) = codeMat 200 := by
      unfold actionA
      rw [lineSrc99_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 80 * codeMat 281 = codeMat 200
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 200
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc99_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨99, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 275) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 275) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc99_le hAct

private theorem lineSrc100_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc100_le :
    lineSourcePlane ⟨100, by decide⟩ ≤ actionW (codeMat 169) (codeMat 275) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc100_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 169) (codeMat 275) (codeMat 81) = codeMat 202 := by
      unfold actionA
      rw [lineSrc100_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 81 * codeMat 281 = codeMat 202
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 169) (codeMat 275) X = codeMat 202
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc100_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨100, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 275) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 275) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc100_le hAct

private theorem lineSrc101_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc101_le :
    lineSourcePlane ⟨101, by decide⟩ ≤ actionW (codeMat 161) (codeMat 275) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc101_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 161) (codeMat 275) (codeMat 84) = codeMat 204 := by
      unfold actionA
      rw [lineSrc101_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 84 * codeMat 281 = codeMat 204
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 275) X = codeMat 204
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc101_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨101, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 275) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 275) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc101_le hAct

private theorem lineSrc102_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc102_le :
    lineSourcePlane ⟨102, by decide⟩ ≤ actionW (codeMat 161) (codeMat 307) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc102_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 161) (codeMat 307) (codeMat 85) = codeMat 206 := by
      unfold actionA
      rw [lineSrc102_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 85 * codeMat 473 = codeMat 206
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 161) (codeMat 307) X = codeMat 206
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc102_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨102, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 307) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 307) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc102_le hAct

private theorem lineSrc103_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc103_le :
    lineSourcePlane ⟨103, by decide⟩ ≤ actionW (codeMat 177) (codeMat 275) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc103_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 80 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 80 (by decide)
    have hact : actionA (codeMat 177) (codeMat 275) (codeMat 80) = codeMat 208 := by
      unfold actionA
      rw [lineSrc103_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 80 * codeMat 281 = codeMat 208
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 177) (codeMat 275) X = codeMat 208
    exact ⟨codeMat 80, hw, hact⟩

theorem lineSrc103_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨103, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 275) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 275) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc103_le hAct

private theorem lineSrc104_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc104_le :
    lineSourcePlane ⟨104, by decide⟩ ≤ actionW (codeMat 185) (codeMat 275) linePlane481T := by
  unfold lineSourcePlane lineSourceCode linePlane481T
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 1 (by decide)
    have hact : actionA (codeMat 185) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc104_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 81 ∈ spanCodes [80, 1] :=
      spanContainsCode_implies_mem_spanCodes [80, 1] 81 (by decide)
    have hact : actionA (codeMat 185) (codeMat 275) (codeMat 81) = codeMat 210 := by
      unfold actionA
      rw [lineSrc104_QtInv]
      show (codeMat 185 : Mat3).transpose * codeMat 81 * codeMat 281 = codeMat 210
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [80, 1] ∧ actionA (codeMat 185) (codeMat 275) X = codeMat 210
    exact ⟨codeMat 81, hw, hact⟩

theorem lineSrc104_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨104, by decide⟩) 18 := by
  have hP : Invertible (codeMat 185 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481T 18 := linePlane481T_lb h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 185) (codeMat 275) linePlane481T) 18 :=
    @quotientRankAtLeast_action (codeMat 185) (codeMat 275) hP hQ linePlane481T 18 hBase
  exact quotientRankAtLeast_mono lineSrc104_le hAct

private theorem lineSrc105_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc105_le :
    lineSourcePlane ⟨105, by decide⟩ ≤ actionW (codeMat 177) (codeMat 275) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc105_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 84 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 84 (by decide)
    have hact : actionA (codeMat 177) (codeMat 275) (codeMat 84) = codeMat 212 := by
      unfold actionA
      rw [lineSrc105_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 84 * codeMat 281 = codeMat 212
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 275) X = codeMat 212
    exact ⟨codeMat 84, hw, hact⟩

theorem lineSrc105_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨105, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 275) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 275) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc105_le hAct

private theorem lineSrc106_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc106_le :
    lineSourcePlane ⟨106, by decide⟩ ≤ actionW (codeMat 177) (codeMat 307) linePlane482 := by
  unfold lineSourcePlane lineSourceCode linePlane482
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc106_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 85 ∈ spanCodes [84, 1] :=
      spanContainsCode_implies_mem_spanCodes [84, 1] 85 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 85) = codeMat 214 := by
      unfold actionA
      rw [lineSrc106_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 85 * codeMat 473 = codeMat 214
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [84, 1] ∧ actionA (codeMat 177) (codeMat 307) X = codeMat 214
    exact ⟨codeMat 85, hw, hact⟩

theorem lineSrc106_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨106, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane482 18 := h482
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 307) linePlane482) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 307) hP hQ linePlane482 18 hBase
  exact quotientRankAtLeast_mono lineSrc106_le hAct

private theorem lineSrc107_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = codeMat 267 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * codeMat 267 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc107_le :
    lineSourcePlane ⟨107, by decide⟩ ≤ actionW (codeMat 142) (codeMat 282) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 142) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc107_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 16 * codeMat 267 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 282) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 142) (codeMat 282) (codeMat 1) = codeMat 216 := by
      unfold actionA
      rw [lineSrc107_QtInv]
      show (codeMat 142 : Mat3).transpose * codeMat 1 * codeMat 267 = codeMat 216
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 142) (codeMat 282) X = codeMat 216
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc107_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨107, by decide⟩) 18 := by
  have hP : Invertible (codeMat 142 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 142) (codeMat 282) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 142) (codeMat 282) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc107_le hAct

private theorem lineSrc108_QtInv :
    (codeMat 282 : Mat3).transpose⁻¹ = codeMat 267 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 282 : Mat3).transpose * codeMat 267 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc108_le :
    lineSourcePlane ⟨108, by decide⟩ ≤ actionW (codeMat 143) (codeMat 282) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 143) (codeMat 282) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc108_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 16 * codeMat 267 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 282) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 17 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 17 (by decide)
    have hact : actionA (codeMat 143) (codeMat 282) (codeMat 17) = codeMat 218 := by
      unfold actionA
      rw [lineSrc108_QtInv]
      show (codeMat 143 : Mat3).transpose * codeMat 17 * codeMat 267 = codeMat 218
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 143) (codeMat 282) X = codeMat 218
    exact ⟨codeMat 17, hw, hact⟩

theorem lineSrc108_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨108, by decide⟩) 18 := by
  have hP : Invertible (codeMat 143 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 282 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 143) (codeMat 282) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 143) (codeMat 282) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc108_le hAct

private theorem lineSrc109_QtInv :
    (codeMat 275 : Mat3).transpose⁻¹ = codeMat 281 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 275 : Mat3).transpose * codeMat 281 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc109_le :
    lineSourcePlane ⟨109, by decide⟩ ≤ actionW (codeMat 177) (codeMat 275) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 275) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc109_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 281 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 275) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 20 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 20 (by decide)
    have hact : actionA (codeMat 177) (codeMat 275) (codeMat 20) = codeMat 220 := by
      unfold actionA
      rw [lineSrc109_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 20 * codeMat 281 = codeMat 220
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 275) X = codeMat 220
    exact ⟨codeMat 20, hw, hact⟩

theorem lineSrc109_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨109, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 275 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 275) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 275) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc109_le hAct

private theorem lineSrc110_QtInv :
    (codeMat 307 : Mat3).transpose⁻¹ = codeMat 473 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 307 : Mat3).transpose * codeMat 473 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc110_le :
    lineSourcePlane ⟨110, by decide⟩ ≤ actionW (codeMat 177) (codeMat 307) linePlane481 := by
  unfold lineSourcePlane lineSourceCode linePlane481
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 1 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc110_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 1 * codeMat 473 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 307) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 21 ∈ spanCodes [20, 1] :=
      spanContainsCode_implies_mem_spanCodes [20, 1] 21 (by decide)
    have hact : actionA (codeMat 177) (codeMat 307) (codeMat 21) = codeMat 222 := by
      unfold actionA
      rw [lineSrc110_QtInv]
      show (codeMat 177 : Mat3).transpose * codeMat 21 * codeMat 473 = codeMat 222
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [20, 1] ∧ actionA (codeMat 177) (codeMat 307) X = codeMat 222
    exact ⟨codeMat 21, hw, hact⟩

theorem lineSrc110_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨110, by decide⟩) 18 := by
  have hP : Invertible (codeMat 177 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 307 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane481 18 := h481
  have hAct : QuotientRankAtLeast (actionW (codeMat 177) (codeMat 307) linePlane481) 18 :=
    @quotientRankAtLeast_action (codeMat 177) (codeMat 307) hP hQ linePlane481 18 hBase
  exact quotientRankAtLeast_mono lineSrc110_le hAct

private theorem lineSrc111_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = codeMat 225 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * codeMat 225 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc111_le :
    lineSourcePlane ⟨111, by decide⟩ ≤ actionW (codeMat 161) (codeMat 163) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc111_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 225 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 163) (codeMat 160) = codeMat 224 := by
      unfold actionA
      rw [lineSrc111_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 225 = codeMat 224
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 163) X = codeMat 224
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc111_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨111, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 163) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 163) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc111_le hAct

private theorem lineSrc112_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = codeMat 225 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * codeMat 225 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc112_le :
    lineSourcePlane ⟨112, by decide⟩ ≤ actionW (codeMat 169) (codeMat 163) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc112_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 225 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 163) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 163) (codeMat 161) = codeMat 226 := by
      unfold actionA
      rw [lineSrc112_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 225 = codeMat 226
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 163) X = codeMat 226
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc112_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨112, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 163) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 163) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc112_le hAct

private theorem lineSrc113_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = codeMat 225 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * codeMat 225 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc113_le :
    lineSourcePlane ⟨113, by decide⟩ ≤ actionW (codeMat 225) (codeMat 163) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc113_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 225 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 163) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 163) (codeMat 160) = codeMat 228 := by
      unfold actionA
      rw [lineSrc113_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 225 = codeMat 228
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 163) X = codeMat 228
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc113_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨113, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 163) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 163) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc113_le hAct

private theorem lineSrc114_QtInv :
    (codeMat 163 : Mat3).transpose⁻¹ = codeMat 225 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 163 : Mat3).transpose * codeMat 225 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc114_le :
    lineSourcePlane ⟨114, by decide⟩ ≤ actionW (codeMat 233) (codeMat 163) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 163) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc114_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 225 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 163) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 163) (codeMat 161) = codeMat 230 := by
      unfold actionA
      rw [lineSrc114_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 225 = codeMat 230
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 163) X = codeMat 230
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc114_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨114, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 163 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 163) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 163) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc114_le hAct

private theorem lineSrc115_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = codeMat 233 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * codeMat 233 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc115_le :
    lineSourcePlane ⟨115, by decide⟩ ≤ actionW (codeMat 161) (codeMat 167) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc115_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 233 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 167) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 167) (codeMat 160) = codeMat 232 := by
      unfold actionA
      rw [lineSrc115_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 233 = codeMat 232
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 167) X = codeMat 232
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc115_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨115, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 167) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 167) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc115_le hAct

private theorem lineSrc116_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = codeMat 233 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * codeMat 233 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc116_le :
    lineSourcePlane ⟨116, by decide⟩ ≤ actionW (codeMat 169) (codeMat 167) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc116_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 233 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 167) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 167) (codeMat 161) = codeMat 234 := by
      unfold actionA
      rw [lineSrc116_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 233 = codeMat 234
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 167) X = codeMat 234
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc116_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨116, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 167) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 167) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc116_le hAct

private theorem lineSrc117_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = codeMat 233 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * codeMat 233 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc117_le :
    lineSourcePlane ⟨117, by decide⟩ ≤ actionW (codeMat 225) (codeMat 167) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc117_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 233 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 167) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 167) (codeMat 161) = codeMat 236 := by
      unfold actionA
      rw [lineSrc117_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 233 = codeMat 236
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 167) X = codeMat 236
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc117_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨117, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 167) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 167) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc117_le hAct

private theorem lineSrc118_QtInv :
    (codeMat 167 : Mat3).transpose⁻¹ = codeMat 233 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 167 : Mat3).transpose * codeMat 233 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc118_le :
    lineSourcePlane ⟨118, by decide⟩ ≤ actionW (codeMat 233) (codeMat 167) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 167) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc118_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 233 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 167) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 167) (codeMat 160) = codeMat 238 := by
      unfold actionA
      rw [lineSrc118_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 233 = codeMat 238
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 167) X = codeMat 238
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc118_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨118, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 167 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 167) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 167) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc118_le hAct

private theorem lineSrc119_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = codeMat 241 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * codeMat 241 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc119_le :
    lineSourcePlane ⟨119, by decide⟩ ≤ actionW (codeMat 161) (codeMat 423) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc119_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 241 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 423) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 423) (codeMat 160) = codeMat 240 := by
      unfold actionA
      rw [lineSrc119_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 241 = codeMat 240
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 423) X = codeMat 240
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc119_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨119, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 423) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 423) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc119_le hAct

private theorem lineSrc120_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = codeMat 241 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * codeMat 241 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc120_le :
    lineSourcePlane ⟨120, by decide⟩ ≤ actionW (codeMat 169) (codeMat 423) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc120_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 241 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 423) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 423) (codeMat 161) = codeMat 242 := by
      unfold actionA
      rw [lineSrc120_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 241 = codeMat 242
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 423) X = codeMat 242
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc120_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨120, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 423) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 423) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc120_le hAct

private theorem lineSrc121_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = codeMat 241 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * codeMat 241 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc121_le :
    lineSourcePlane ⟨121, by decide⟩ ≤ actionW (codeMat 233) (codeMat 423) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc121_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 241 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 423) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 233) (codeMat 423) (codeMat 161) = codeMat 244 := by
      unfold actionA
      rw [lineSrc121_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 161 * codeMat 241 = codeMat 244
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 423) X = codeMat 244
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc121_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨121, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 423) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 423) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc121_le hAct

private theorem lineSrc122_QtInv :
    (codeMat 423 : Mat3).transpose⁻¹ = codeMat 241 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 423 : Mat3).transpose * codeMat 241 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc122_le :
    lineSourcePlane ⟨122, by decide⟩ ≤ actionW (codeMat 225) (codeMat 423) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 423) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc122_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 241 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 423) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 225) (codeMat 423) (codeMat 160) = codeMat 246 := by
      unfold actionA
      rw [lineSrc122_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 160 * codeMat 241 = codeMat 246
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 423) X = codeMat 246
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc122_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨122, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 423 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 423) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 423) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc122_le hAct

private theorem lineSrc123_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc123_le :
    lineSourcePlane ⟨123, by decide⟩ ≤ actionW (codeMat 161) (codeMat 419) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 161) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc123_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 161) (codeMat 419) (codeMat 160) = codeMat 248 := by
      unfold actionA
      rw [lineSrc123_QtInv]
      show (codeMat 161 : Mat3).transpose * codeMat 160 * codeMat 249 = codeMat 248
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 161) (codeMat 419) X = codeMat 248
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc123_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨123, by decide⟩) 18 := by
  have hP : Invertible (codeMat 161 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 161) (codeMat 419) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 161) (codeMat 419) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc123_le hAct

private theorem lineSrc124_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc124_le :
    lineSourcePlane ⟨124, by decide⟩ ≤ actionW (codeMat 169) (codeMat 419) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc124_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 169) (codeMat 419) (codeMat 161) = codeMat 250 := by
      unfold actionA
      rw [lineSrc124_QtInv]
      show (codeMat 169 : Mat3).transpose * codeMat 161 * codeMat 249 = codeMat 250
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 169) (codeMat 419) X = codeMat 250
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc124_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨124, by decide⟩) 18 := by
  have hP : Invertible (codeMat 169 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 169) (codeMat 419) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 169) (codeMat 419) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc124_le hAct

private theorem lineSrc125_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc125_le :
    lineSourcePlane ⟨125, by decide⟩ ≤ actionW (codeMat 233) (codeMat 419) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 233) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc125_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 160 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 160 (by decide)
    have hact : actionA (codeMat 233) (codeMat 419) (codeMat 160) = codeMat 252 := by
      unfold actionA
      rw [lineSrc125_QtInv]
      show (codeMat 233 : Mat3).transpose * codeMat 160 * codeMat 249 = codeMat 252
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 233) (codeMat 419) X = codeMat 252
    exact ⟨codeMat 160, hw, hact⟩

theorem lineSrc125_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨125, by decide⟩) 18 := by
  have hP : Invertible (codeMat 233 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 233) (codeMat 419) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 233) (codeMat 419) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc125_le hAct

private theorem lineSrc126_QtInv :
    (codeMat 419 : Mat3).transpose⁻¹ = codeMat 249 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 419 : Mat3).transpose * codeMat 249 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc126_le :
    lineSourcePlane ⟨126, by decide⟩ ≤ actionW (codeMat 225) (codeMat 419) linePlane483 := by
  unfold lineSourcePlane lineSourceCode linePlane483
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 1 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 1 (by decide)
    have hact : actionA (codeMat 225) (codeMat 419) (codeMat 1) = codeMat 1 := by
      unfold actionA
      rw [lineSrc126_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 1 * codeMat 249 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 419) X = codeMat 1
    exact ⟨codeMat 1, hw, hact⟩
  · subst h1
    have hw : codeMat 161 ∈ spanCodes [160, 1] :=
      spanContainsCode_implies_mem_spanCodes [160, 1] 161 (by decide)
    have hact : actionA (codeMat 225) (codeMat 419) (codeMat 161) = codeMat 254 := by
      unfold actionA
      rw [lineSrc126_QtInv]
      show (codeMat 225 : Mat3).transpose * codeMat 161 * codeMat 249 = codeMat 254
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [160, 1] ∧ actionA (codeMat 225) (codeMat 419) X = codeMat 254
    exact ⟨codeMat 161, hw, hact⟩

theorem lineSrc126_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨126, by decide⟩) 18 := by
  have hP : Invertible (codeMat 225 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 419 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane483 18 := h483
  have hAct : QuotientRankAtLeast (actionW (codeMat 225) (codeMat 419) linePlane483) 18 :=
    @quotientRankAtLeast_action (codeMat 225) (codeMat 419) hP hQ linePlane483 18 hBase
  exact quotientRankAtLeast_mono lineSrc126_le hAct

private theorem lineSrc127_QtInv :
    (codeMat 140 : Mat3).transpose⁻¹ = codeMat 140 := by
  apply Matrix.inv_eq_right_inv
  show (codeMat 140 : Mat3).transpose * codeMat 140 = 1
  ext i j <;> fin_cases i <;> fin_cases j <;> decide

private theorem lineSrc127_le :
    lineSourcePlane ⟨127, by decide⟩ ≤ actionW (codeMat 140) (codeMat 140) linePlane480 := by
  unfold lineSourcePlane lineSourceCode linePlane480
  apply Submodule.span_le.mpr
  intro M hM
  rcases hM with ⟨n, hn, rfl⟩
  simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hn
  rcases hn with h0 | h1
  · subst h0
    have hw : codeMat 16 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 16 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 16) = codeMat 1 := by
      unfold actionA
      rw [lineSrc127_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 16 * codeMat 140 = codeMat 1
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 140) X = codeMat 1
    exact ⟨codeMat 16, hw, hact⟩
  · subst h1
    have hw : codeMat 1 ∈ spanCodes [16, 1] :=
      spanContainsCode_implies_mem_spanCodes [16, 1] 1 (by decide)
    have hact : actionA (codeMat 140) (codeMat 140) (codeMat 1) = codeMat 256 := by
      unfold actionA
      rw [lineSrc127_QtInv]
      show (codeMat 140 : Mat3).transpose * codeMat 1 * codeMat 140 = codeMat 256
      ext i j <;> fin_cases i <;> fin_cases j <;> decide
    change ∃ X, X ∈ spanCodes [16, 1] ∧ actionA (codeMat 140) (codeMat 140) X = codeMat 256
    exact ⟨codeMat 1, hw, hact⟩

theorem lineSrc127_bound
    (h478 : QuotientRankAtLeast linePlane478 17)
    (h479 : QuotientRankAtLeast linePlane479 17)
    (h480 : QuotientRankAtLeast linePlane480 18)
    (h481 : QuotientRankAtLeast linePlane481 18)
    (h482 : QuotientRankAtLeast linePlane482 18)
    (h483 : QuotientRankAtLeast linePlane483 18) :
    QuotientRankAtLeast (lineSourcePlane ⟨127, by decide⟩) 18 := by
  have hP : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hQ : Invertible (codeMat 140 : Mat3) := Matrix.invertibleOfIsUnitDet _ (by decide)
  have hBase : QuotientRankAtLeast linePlane480 18 := h480
  have hAct : QuotientRankAtLeast (actionW (codeMat 140) (codeMat 140) linePlane480) 18 :=
    @quotientRankAtLeast_action (codeMat 140) (codeMat 140) hP hQ linePlane480 18 hBase
  exact quotientRankAtLeast_mono lineSrc127_le hAct

end QiushiMatmul
