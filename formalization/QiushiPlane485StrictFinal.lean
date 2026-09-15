import QiushiPlane485StrictSource0
import QiushiPlane485StrictSource1
import QiushiPlane485StrictSource2
import QiushiPlane485StrictSource3
import QiushiPlane485StrictSource4
import QiushiPlane485StrictSource5
import QiushiPlane485StrictSource6
import QiushiPlane485StrictSource7
import QiushiPlane485StrictSource8
import QiushiPlane485StrictSource9
import QiushiPlane485StrictSource10
import QiushiPlane485StrictSource11
import QiushiPlane485StrictSource12
import QiushiPlane485StrictSource13
import QiushiPlane485StrictDead0
import QiushiPlane485StrictDead1
import QiushiPlane485StrictDead2
import QiushiPlane485GenBool
namespace QiushiMatmul
theorem plane485SourceStrictChecks : ∀ i, plane485SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 14) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485SourceStrictBlock0
  | ⟨1, _⟩ => exact plane485SourceStrictBlock1
  | ⟨2, _⟩ => exact plane485SourceStrictBlock2
  | ⟨3, _⟩ => exact plane485SourceStrictBlock3
  | ⟨4, _⟩ => exact plane485SourceStrictBlock4
  | ⟨5, _⟩ => exact plane485SourceStrictBlock5
  | ⟨6, _⟩ => exact plane485SourceStrictBlock6
  | ⟨7, _⟩ => exact plane485SourceStrictBlock7
  | ⟨8, _⟩ => exact plane485SourceStrictBlock8
  | ⟨9, _⟩ => exact plane485SourceStrictBlock9
  | ⟨10, _⟩ => exact plane485SourceStrictBlock10
  | ⟨11, _⟩ => exact plane485SourceStrictBlock11
  | ⟨12, _⟩ => exact plane485SourceStrictBlock12
  | ⟨13, _⟩ => exact plane485SourceStrictBlock13
  | ⟨k + 14, h⟩ => omega

theorem plane485SourceStrict : ∀ i, plane485GenConfig.W < plane485GenConfig.sourceU i ∧
    plane485GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane485GenBool.hPlaneLeSource i)) (plane485SourceStrictChecks i)

theorem plane485DeadStrictChecks : ∀ i, plane485DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane485DeadStrictBlock0
  | ⟨1, _⟩ => exact plane485DeadStrictBlock1
  | ⟨2, _⟩ => exact plane485DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane485DeadStrict : ∀ i, plane485GenConfig.W < plane485GenConfig.deadU i ∧
    plane485GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane485GenBool.hPlaneLeDead i)) (plane485DeadStrictChecks i)

end QiushiMatmul
