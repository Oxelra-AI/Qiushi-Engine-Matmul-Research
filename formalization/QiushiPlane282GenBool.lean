import QiushiPlane282GenData

set_option maxHeartbeats 800000000
set_option maxRecDepth 100000

namespace QiushiMatmul

theorem plane282GenBool : PlaneExtBool plane282GenConfig where
  hSectionCoset := by decide +revert
  hDeadCover := by decide +revert
  hPlaneLeSource := by decide +revert
  hPlaneLeDead := by decide +revert
  hIndicator := by decide +revert
  hRhs := by decide +revert
  hTarget := by decide

end QiushiMatmul
