import FrozenRegistry.Btp285SectionAll
import FrozenRegistry.Btp285DeadAll
import FrozenRegistry.Btp285SourceAll
import FrozenRegistry.Btp285DeadSourceAll
import FrozenRegistry.Btp285IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane285BtpGenBool : PlaneExtBool plane285BtpGenConfig where
  hSectionCoset := plane285BtpGenSectionAll
  hDeadCover := plane285BtpGenDeadAll
  hPlaneLeSource := plane285BtpGenSourceAll
  hPlaneLeDead := plane285BtpGenDeadSourceAll
  hIndicator := plane285BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
