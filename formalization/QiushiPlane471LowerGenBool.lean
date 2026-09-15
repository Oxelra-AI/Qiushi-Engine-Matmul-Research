import QiushiPlane471LowerGenSectionAll
import QiushiPlane471LowerGenDeadAll
import QiushiPlane471LowerGenSourceAll
import QiushiPlane471LowerGenDeadSourceAll
import QiushiPlane471LowerGenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471LowerGenBool : PlaneExtBool plane471LowerGenConfig where
  hSectionCoset := plane471LowerGenSectionAll
  hDeadCover := plane471LowerGenDeadAll
  hPlaneLeSource := plane471LowerGenSourceAll
  hPlaneLeDead := plane471LowerGenDeadSourceAll
  hIndicator := plane471LowerGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
