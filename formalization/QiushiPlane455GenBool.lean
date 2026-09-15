import QiushiPlane455GenSectionAll
import QiushiPlane455GenDeadAll
import QiushiPlane455GenSourceAll
import QiushiPlane455GenDeadSourceAll
import QiushiPlane455GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane455GenBool : PlaneExtBool plane455GenConfig where
  hSectionCoset := plane455GenSectionAll
  hDeadCover := plane455GenDeadAll
  hPlaneLeSource := plane455GenSourceAll
  hPlaneLeDead := plane455GenDeadSourceAll
  hIndicator := plane455GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
