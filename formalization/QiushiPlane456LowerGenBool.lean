import QiushiPlane456LowerGenSectionAll
import QiushiPlane456LowerGenDeadAll
import QiushiPlane456LowerGenSourceAll
import QiushiPlane456LowerGenDeadSourceAll
import QiushiPlane456LowerGenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456LowerGenBool : PlaneExtBool plane456LowerGenConfig where
  hSectionCoset := plane456LowerGenSectionAll
  hDeadCover := plane456LowerGenDeadAll
  hPlaneLeSource := plane456LowerGenSourceAll
  hPlaneLeDead := plane456LowerGenDeadSourceAll
  hIndicator := plane456LowerGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
