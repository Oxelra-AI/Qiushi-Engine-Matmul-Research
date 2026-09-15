import QiushiPlane487StrictSource0
import QiushiPlane487StrictSource1
import QiushiPlane487StrictSource2
import QiushiPlane487StrictSource3
import QiushiPlane487StrictSource4
import QiushiPlane487StrictSource5
import QiushiPlane487StrictSource6
import QiushiPlane487StrictSource7
import QiushiPlane487StrictSource8
import QiushiPlane487StrictSource9
import QiushiPlane487StrictSource10
import QiushiPlane487StrictSource11
import QiushiPlane487StrictSource12
import QiushiPlane487StrictSource13
import QiushiPlane487StrictSource14
import QiushiPlane487StrictSource15
import QiushiPlane487StrictSource16
import QiushiPlane487StrictSource17
import QiushiPlane487StrictSource18
import QiushiPlane487StrictSource19
import QiushiPlane487StrictSource20
import QiushiPlane487StrictDead0
import QiushiPlane487StrictDead1
import QiushiPlane487StrictDead2
import QiushiPlane487GenBool
namespace QiushiMatmul
theorem plane487SourceStrictChecks : ∀ i, plane487SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 21) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487SourceStrictBlock0
  | ⟨1, _⟩ => exact plane487SourceStrictBlock1
  | ⟨2, _⟩ => exact plane487SourceStrictBlock2
  | ⟨3, _⟩ => exact plane487SourceStrictBlock3
  | ⟨4, _⟩ => exact plane487SourceStrictBlock4
  | ⟨5, _⟩ => exact plane487SourceStrictBlock5
  | ⟨6, _⟩ => exact plane487SourceStrictBlock6
  | ⟨7, _⟩ => exact plane487SourceStrictBlock7
  | ⟨8, _⟩ => exact plane487SourceStrictBlock8
  | ⟨9, _⟩ => exact plane487SourceStrictBlock9
  | ⟨10, _⟩ => exact plane487SourceStrictBlock10
  | ⟨11, _⟩ => exact plane487SourceStrictBlock11
  | ⟨12, _⟩ => exact plane487SourceStrictBlock12
  | ⟨13, _⟩ => exact plane487SourceStrictBlock13
  | ⟨14, _⟩ => exact plane487SourceStrictBlock14
  | ⟨15, _⟩ => exact plane487SourceStrictBlock15
  | ⟨16, _⟩ => exact plane487SourceStrictBlock16
  | ⟨17, _⟩ => exact plane487SourceStrictBlock17
  | ⟨18, _⟩ => exact plane487SourceStrictBlock18
  | ⟨19, _⟩ => exact plane487SourceStrictBlock19
  | ⟨20, _⟩ => exact plane487SourceStrictBlock20
  | ⟨k + 21, h⟩ => omega

theorem plane487SourceStrict : ∀ i, plane487GenConfig.W < plane487GenConfig.sourceU i ∧
    plane487GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane487GenBool.hPlaneLeSource i)) (plane487SourceStrictChecks i)

theorem plane487DeadStrictChecks : ∀ i, plane487DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane487DeadStrictBlock0
  | ⟨1, _⟩ => exact plane487DeadStrictBlock1
  | ⟨2, _⟩ => exact plane487DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane487DeadStrict : ∀ i, plane487GenConfig.W < plane487GenConfig.deadU i ∧
    plane487GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane487GenBool.hPlaneLeDead i)) (plane487DeadStrictChecks i)

end QiushiMatmul
