import FrozenRegistry.Btp265SectionAll
import FrozenRegistry.Btp265DeadAll
import FrozenRegistry.Btp265SourceAll
import FrozenRegistry.Btp265DeadSourceAll
import FrozenRegistry.Btp265IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane265BtpGenBool : PlaneExtBool plane265BtpGenConfig where
  hSectionCoset := plane265BtpGenSectionAll
  hDeadCover := plane265BtpGenDeadAll
  hPlaneLeSource := plane265BtpGenSourceAll
  hPlaneLeDead := plane265BtpGenDeadSourceAll
  hIndicator := plane265BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
