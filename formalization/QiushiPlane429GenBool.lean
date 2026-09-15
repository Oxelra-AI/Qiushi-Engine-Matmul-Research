import QiushiPlane429GenSectionAll
import QiushiPlane429GenDeadAll
import QiushiPlane429GenSourceAll
import QiushiPlane429GenDeadSourceAll
import QiushiPlane429GenIndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane429GenBool : PlaneExtBool plane429GenConfig where
  hSectionCoset := plane429GenSectionAll
  hDeadCover := plane429GenDeadAll
  hPlaneLeSource := plane429GenSourceAll
  hPlaneLeDead := plane429GenDeadSourceAll
  hIndicator := plane429GenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
