import QiushiPlane486StrictSource0
import QiushiPlane486StrictSource1
import QiushiPlane486StrictSource2
import QiushiPlane486StrictSource3
import QiushiPlane486StrictSource4
import QiushiPlane486StrictSource5
import QiushiPlane486StrictSource6
import QiushiPlane486StrictSource7
import QiushiPlane486StrictSource8
import QiushiPlane486StrictDead0
import QiushiPlane486StrictDead1
import QiushiPlane486StrictDead2
import QiushiPlane486GenBool
namespace QiushiMatmul
theorem plane486SourceStrictChecks : ∀ i, plane486SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 9) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486SourceStrictBlock0
  | ⟨1, _⟩ => exact plane486SourceStrictBlock1
  | ⟨2, _⟩ => exact plane486SourceStrictBlock2
  | ⟨3, _⟩ => exact plane486SourceStrictBlock3
  | ⟨4, _⟩ => exact plane486SourceStrictBlock4
  | ⟨5, _⟩ => exact plane486SourceStrictBlock5
  | ⟨6, _⟩ => exact plane486SourceStrictBlock6
  | ⟨7, _⟩ => exact plane486SourceStrictBlock7
  | ⟨8, _⟩ => exact plane486SourceStrictBlock8
  | ⟨k + 9, h⟩ => omega

theorem plane486SourceStrict : ∀ i, plane486GenConfig.W < plane486GenConfig.sourceU i ∧
    plane486GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane486GenBool.hPlaneLeSource i)) (plane486SourceStrictChecks i)

theorem plane486DeadStrictChecks : ∀ i, plane486DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane486DeadStrictBlock0
  | ⟨1, _⟩ => exact plane486DeadStrictBlock1
  | ⟨2, _⟩ => exact plane486DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane486DeadStrict : ∀ i, plane486GenConfig.W < plane486GenConfig.deadU i ∧
    plane486GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane486GenBool.hPlaneLeDead i)) (plane486DeadStrictChecks i)

end QiushiMatmul
