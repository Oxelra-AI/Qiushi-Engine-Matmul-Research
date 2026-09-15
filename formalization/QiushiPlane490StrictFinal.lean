import QiushiPlane490StrictSource0
import QiushiPlane490StrictSource1
import QiushiPlane490StrictSource2
import QiushiPlane490StrictSource3
import QiushiPlane490StrictSource4
import QiushiPlane490StrictSource5
import QiushiPlane490StrictSource6
import QiushiPlane490StrictSource7
import QiushiPlane490StrictSource8
import QiushiPlane490StrictSource9
import QiushiPlane490StrictSource10
import QiushiPlane490StrictSource11
import QiushiPlane490StrictSource12
import QiushiPlane490StrictSource13
import QiushiPlane490StrictSource14
import QiushiPlane490StrictSource15
import QiushiPlane490StrictSource16
import QiushiPlane490StrictSource17
import QiushiPlane490StrictSource18
import QiushiPlane490StrictSource19
import QiushiPlane490StrictSource20
import QiushiPlane490StrictSource21
import QiushiPlane490StrictSource22
import QiushiPlane490StrictDead0
import QiushiPlane490StrictDead1
import QiushiPlane490StrictDead2
import QiushiPlane490GenBool
namespace QiushiMatmul
theorem plane490SourceStrictChecks : ∀ i, plane490SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 23) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490SourceStrictBlock0
  | ⟨1, _⟩ => exact plane490SourceStrictBlock1
  | ⟨2, _⟩ => exact plane490SourceStrictBlock2
  | ⟨3, _⟩ => exact plane490SourceStrictBlock3
  | ⟨4, _⟩ => exact plane490SourceStrictBlock4
  | ⟨5, _⟩ => exact plane490SourceStrictBlock5
  | ⟨6, _⟩ => exact plane490SourceStrictBlock6
  | ⟨7, _⟩ => exact plane490SourceStrictBlock7
  | ⟨8, _⟩ => exact plane490SourceStrictBlock8
  | ⟨9, _⟩ => exact plane490SourceStrictBlock9
  | ⟨10, _⟩ => exact plane490SourceStrictBlock10
  | ⟨11, _⟩ => exact plane490SourceStrictBlock11
  | ⟨12, _⟩ => exact plane490SourceStrictBlock12
  | ⟨13, _⟩ => exact plane490SourceStrictBlock13
  | ⟨14, _⟩ => exact plane490SourceStrictBlock14
  | ⟨15, _⟩ => exact plane490SourceStrictBlock15
  | ⟨16, _⟩ => exact plane490SourceStrictBlock16
  | ⟨17, _⟩ => exact plane490SourceStrictBlock17
  | ⟨18, _⟩ => exact plane490SourceStrictBlock18
  | ⟨19, _⟩ => exact plane490SourceStrictBlock19
  | ⟨20, _⟩ => exact plane490SourceStrictBlock20
  | ⟨21, _⟩ => exact plane490SourceStrictBlock21
  | ⟨22, _⟩ => exact plane490SourceStrictBlock22
  | ⟨k + 23, h⟩ => omega

theorem plane490SourceStrict : ∀ i, plane490GenConfig.W < plane490GenConfig.sourceU i ∧
    plane490GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane490GenBool.hPlaneLeSource i)) (plane490SourceStrictChecks i)

theorem plane490DeadStrictChecks : ∀ i, plane490DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane490DeadStrictBlock0
  | ⟨1, _⟩ => exact plane490DeadStrictBlock1
  | ⟨2, _⟩ => exact plane490DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane490DeadStrict : ∀ i, plane490GenConfig.W < plane490GenConfig.deadU i ∧
    plane490GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane490GenBool.hPlaneLeDead i)) (plane490DeadStrictChecks i)

end QiushiMatmul
