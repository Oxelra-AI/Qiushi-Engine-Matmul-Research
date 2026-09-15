import QiushiPlane488StrictSource0
import QiushiPlane488StrictSource1
import QiushiPlane488StrictSource2
import QiushiPlane488StrictSource3
import QiushiPlane488StrictSource4
import QiushiPlane488StrictSource5
import QiushiPlane488StrictSource6
import QiushiPlane488StrictSource7
import QiushiPlane488StrictSource8
import QiushiPlane488StrictSource9
import QiushiPlane488StrictSource10
import QiushiPlane488StrictSource11
import QiushiPlane488StrictSource12
import QiushiPlane488StrictDead0
import QiushiPlane488StrictDead1
import QiushiPlane488StrictDead2
import QiushiPlane488GenBool
namespace QiushiMatmul
theorem plane488SourceStrictChecks : ∀ i, plane488SourceStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 13) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488SourceStrictBlock0
  | ⟨1, _⟩ => exact plane488SourceStrictBlock1
  | ⟨2, _⟩ => exact plane488SourceStrictBlock2
  | ⟨3, _⟩ => exact plane488SourceStrictBlock3
  | ⟨4, _⟩ => exact plane488SourceStrictBlock4
  | ⟨5, _⟩ => exact plane488SourceStrictBlock5
  | ⟨6, _⟩ => exact plane488SourceStrictBlock6
  | ⟨7, _⟩ => exact plane488SourceStrictBlock7
  | ⟨8, _⟩ => exact plane488SourceStrictBlock8
  | ⟨9, _⟩ => exact plane488SourceStrictBlock9
  | ⟨10, _⟩ => exact plane488SourceStrictBlock10
  | ⟨11, _⟩ => exact plane488SourceStrictBlock11
  | ⟨12, _⟩ => exact plane488SourceStrictBlock12
  | ⟨k + 13, h⟩ => omega

theorem plane488SourceStrict : ∀ i, plane488GenConfig.W < plane488GenConfig.sourceU i ∧
    plane488GenConfig.sourceU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeSource_of_bool (plane488GenBool.hPlaneLeSource i)) (plane488SourceStrictChecks i)

theorem plane488DeadStrictChecks : ∀ i, plane488DeadStrictCheck i = true := by
  apply forall_fin_of_blocks (blocks := 3) (width := 32)
    (by decide) (by decide)
  intro block
  match block with
  | ⟨0, _⟩ => exact plane488DeadStrictBlock0
  | ⟨1, _⟩ => exact plane488DeadStrictBlock1
  | ⟨2, _⟩ => exact plane488DeadStrictBlock2
  | ⟨k + 3, h⟩ => omega

theorem plane488DeadStrict : ∀ i, plane488GenConfig.W < plane488GenConfig.deadU i ∧
    plane488GenConfig.deadU i < ⊤ := by
  intro i
  exact strictSpanCheck_sound _ _ _ _ _ _ (planeLeDead_of_bool (plane488GenBool.hPlaneLeDead i)) (plane488DeadStrictChecks i)

end QiushiMatmul
