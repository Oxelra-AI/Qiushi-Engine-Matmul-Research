import FrozenRegistry.Btp263SectionAll
import FrozenRegistry.Btp263DeadAll
import FrozenRegistry.Btp263SourceAll
import FrozenRegistry.Btp263DeadSourceAll
import FrozenRegistry.Btp263IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane263BtpGenBool : PlaneExtBool plane263BtpGenConfig where
  hSectionCoset := plane263BtpGenSectionAll
  hDeadCover := plane263BtpGenDeadAll
  hPlaneLeSource := plane263BtpGenSourceAll
  hPlaneLeDead := plane263BtpGenDeadSourceAll
  hIndicator := plane263BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
