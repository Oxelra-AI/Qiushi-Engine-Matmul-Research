import QiushiFullOccupation

open QiushiMatmul QiushiMatmul.OccupationSystemBridge
set_option format.width 1000

example : ¬ ∃ weight : Direction (spanCodes [19, 10]) → Int,
    FullOccupation plane484GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane484_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane484_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane484_no_model

example : ¬ ∃ weight : Direction (spanCodes [20, 10]) → Int,
    FullOccupation plane485GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane485_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane485_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane485_no_model

example : ¬ ∃ weight : Direction (spanCodes [68, 10]) → Int,
    FullOccupation plane486GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane486_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane486_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane486_no_model

example : ¬ ∃ weight : Direction (spanCodes [84, 10]) → Int,
    FullOccupation plane487GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane487_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane487_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane487_no_model

example : ¬ ∃ weight : Direction (spanCodes [96, 10]) → Int,
    FullOccupation plane488GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane488_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane488_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane488_no_model

example : ¬ ∃ weight : Direction (spanCodes [258, 10]) → Int,
    FullOccupation plane489GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane489_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane489_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane489_no_model

example : ¬ ∃ weight : Direction (spanCodes [275, 10]) → Int,
    FullOccupation plane490GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane490_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane490_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane490_no_model

example : ¬ ∃ weight : Direction (spanCodes [163, 84]) → Int,
    FullOccupation plane491GenConfig frozenWangTable.L0 weight := by
  rintro ⟨weight, h⟩
  exact FrozenOccupation.plane491_no_model weight h

/-- info: 'QiushiMatmul.FrozenOccupation.plane491_no_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QiushiMatmul.FrozenOccupation.plane491_no_model
