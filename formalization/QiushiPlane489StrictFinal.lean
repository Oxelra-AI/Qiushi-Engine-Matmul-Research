import QiushiPlane489StrictSource0
import QiushiPlane489StrictSource1
import QiushiPlane489StrictSource2
import QiushiPlane489StrictSource3
import QiushiPlane489StrictSource4
import QiushiPlane489StrictSource5
import QiushiPlane489StrictSource6
import QiushiPlane489StrictSource7
import QiushiPlane489StrictSource8
import QiushiPlane489StrictSource9
import QiushiPlane489StrictSource10
import QiushiPlane489StrictSource11
import QiushiPlane489StrictDead0
import QiushiPlane489StrictDead1
import QiushiPlane489StrictDead2
import QiushiPlane489GenBool
namespace QiushiMatmul
theorem plane489SourceStrictChecks : ∀ i, plane489SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 12) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489SourceStrictBlock0
  | ⟨1, _⟩ => exact plane489SourceStrictBlock1
  | ⟨2, _⟩ => exact plane489SourceStrictBlock2
  | ⟨3, _⟩ => exact plane489SourceStrictBlock3
  | ⟨4, _⟩ => exact plane489SourceStrictBlock4
  | ⟨5, _⟩ => exact plane489SourceStrictBlock5
  | ⟨6, _⟩ => exact plane489SourceStrictBlock6
  | ⟨7, _⟩ => exact plane489SourceStrictBlock7
  | ⟨8, _⟩ => exact plane489SourceStrictBlock8
  | ⟨9, _⟩ => exact plane489SourceStrictBlock9
  | ⟨10, _⟩ => exact plane489SourceStrictBlock10
  | ⟨11, _⟩ => exact plane489SourceStrictBlock11
  | ⟨k + 12, h⟩ => omega

theorem plane489SourceStrict : ∀ i, plane489GenConfig.W < plane489GenConfig.sourceU i ∧
    plane489GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane489GenBool.hPlaneLeSource i)) (plane489SourceStrictChecks i)

theorem plane489DeadStrictChecks : ∀ i, plane489DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane489DeadStrictBlock0
  | ⟨1, _⟩ => exact plane489DeadStrictBlock1
  | ⟨2, _⟩ => exact plane489DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane489DeadStrict : ∀ i, plane489GenConfig.W < plane489GenConfig.deadU i ∧
    plane489GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane489GenBool.hPlaneLeDead i)) (plane489DeadStrictChecks i)

end QiushiMatmul
