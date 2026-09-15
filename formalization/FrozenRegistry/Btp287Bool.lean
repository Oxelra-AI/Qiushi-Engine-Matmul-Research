import FrozenRegistry.Btp287SectionAll
import FrozenRegistry.Btp287DeadAll
import FrozenRegistry.Btp287SourceAll
import FrozenRegistry.Btp287DeadSourceAll
import FrozenRegistry.Btp287IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane287BtpGenBool : PlaneExtBool plane287BtpGenConfig where
  hSectionCoset := plane287BtpGenSectionAll
  hDeadCover := plane287BtpGenDeadAll
  hPlaneLeSource := plane287BtpGenSourceAll
  hPlaneLeDead := plane287BtpGenDeadSourceAll
  hIndicator := plane287BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
