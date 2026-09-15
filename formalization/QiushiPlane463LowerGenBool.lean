import QiushiPlane463LowerGenSectionAll
import QiushiPlane463LowerGenDeadAll
import QiushiPlane463LowerGenSourceAll
import QiushiPlane463LowerGenDeadSourceAll
import QiushiPlane463LowerGenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenBool : PlaneExtBool plane463LowerGenConfig where
  hSectionCoset := plane463LowerGenSectionAll
  hDeadCover := plane463LowerGenDeadAll
  hPlaneLeSource := plane463LowerGenSourceAll
  hPlaneLeDead := plane463LowerGenDeadSourceAll
  hIndicator := plane463LowerGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
