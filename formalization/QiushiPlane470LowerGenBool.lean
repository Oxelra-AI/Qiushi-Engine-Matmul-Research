import QiushiPlane470LowerGenSectionAll
import QiushiPlane470LowerGenDeadAll
import QiushiPlane470LowerGenSourceAll
import QiushiPlane470LowerGenDeadSourceAll
import QiushiPlane470LowerGenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenBool : PlaneExtBool plane470LowerGenConfig where
  hSectionCoset := plane470LowerGenSectionAll
  hDeadCover := plane470LowerGenDeadAll
  hPlaneLeSource := plane470LowerGenSourceAll
  hPlaneLeDead := plane470LowerGenDeadSourceAll
  hIndicator := plane470LowerGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
