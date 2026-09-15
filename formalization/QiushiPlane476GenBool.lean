import QiushiPlane476GenSectionAll
import QiushiPlane476GenDeadAll
import QiushiPlane476GenSourceAll
import QiushiPlane476GenDeadSourceAll
import QiushiPlane476GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane476GenBool : PlaneExtBool plane476GenConfig where
  hSectionCoset := plane476GenSectionAll
  hDeadCover := plane476GenDeadAll
  hPlaneLeSource := plane476GenSourceAll
  hPlaneLeDead := plane476GenDeadSourceAll
  hIndicator := plane476GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
