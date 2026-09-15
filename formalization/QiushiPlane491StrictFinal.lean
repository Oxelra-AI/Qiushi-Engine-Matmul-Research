import QiushiPlane491StrictSource0
import QiushiPlane491StrictSource1
import QiushiPlane491StrictSource2
import QiushiPlane491StrictSource3
import QiushiPlane491StrictSource4
import QiushiPlane491StrictSource5
import QiushiPlane491StrictSource6
import QiushiPlane491StrictSource7
import QiushiPlane491StrictSource8
import QiushiPlane491StrictSource9
import QiushiPlane491StrictSource10
import QiushiPlane491StrictSource11
import QiushiPlane491StrictSource12
import QiushiPlane491StrictSource13
import QiushiPlane491StrictSource14
import QiushiPlane491StrictSource15
import QiushiPlane491StrictSource16
import QiushiPlane491StrictSource17
import QiushiPlane491StrictSource18
import QiushiPlane491StrictSource19
import QiushiPlane491StrictSource20
import QiushiPlane491StrictSource21
import QiushiPlane491StrictSource22
import QiushiPlane491StrictDead0
import QiushiPlane491StrictDead1
import QiushiPlane491StrictDead2
import QiushiPlane491GenBool
namespace QiushiMatmul
theorem plane491SourceStrictChecks : ∀ i, plane491SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491SourceStrictBlock0
  | ⟨1, _⟩ => exact plane491SourceStrictBlock1
  | ⟨2, _⟩ => exact plane491SourceStrictBlock2
  | ⟨3, _⟩ => exact plane491SourceStrictBlock3
  | ⟨4, _⟩ => exact plane491SourceStrictBlock4
  | ⟨5, _⟩ => exact plane491SourceStrictBlock5
  | ⟨6, _⟩ => exact plane491SourceStrictBlock6
  | ⟨7, _⟩ => exact plane491SourceStrictBlock7
  | ⟨8, _⟩ => exact plane491SourceStrictBlock8
  | ⟨9, _⟩ => exact plane491SourceStrictBlock9
  | ⟨10, _⟩ => exact plane491SourceStrictBlock10
  | ⟨11, _⟩ => exact plane491SourceStrictBlock11
  | ⟨12, _⟩ => exact plane491SourceStrictBlock12
  | ⟨13, _⟩ => exact plane491SourceStrictBlock13
  | ⟨14, _⟩ => exact plane491SourceStrictBlock14
  | ⟨15, _⟩ => exact plane491SourceStrictBlock15
  | ⟨16, _⟩ => exact plane491SourceStrictBlock16
  | ⟨17, _⟩ => exact plane491SourceStrictBlock17
  | ⟨18, _⟩ => exact plane491SourceStrictBlock18
  | ⟨19, _⟩ => exact plane491SourceStrictBlock19
  | ⟨20, _⟩ => exact plane491SourceStrictBlock20
  | ⟨21, _⟩ => exact plane491SourceStrictBlock21
  | ⟨22, _⟩ => exact plane491SourceStrictBlock22
  | ⟨k + 23, h⟩ => omega

theorem plane491SourceStrict : ∀ i, plane491GenConfig.W < plane491GenConfig.sourceU i ∧
    plane491GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane491GenBool.hPlaneLeSource i)) (plane491SourceStrictChecks i)

theorem plane491DeadStrictChecks : ∀ i, plane491DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane491DeadStrictBlock0
  | ⟨1, _⟩ => exact plane491DeadStrictBlock1
  | ⟨2, _⟩ => exact plane491DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane491DeadStrict : ∀ i, plane491GenConfig.W < plane491GenConfig.deadU i ∧
    plane491GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane491GenBool.hPlaneLeDead i)) (plane491DeadStrictChecks i)

end QiushiMatmul
