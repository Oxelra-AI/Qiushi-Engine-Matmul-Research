import FrozenRegistry.Btp260SectionAll
import FrozenRegistry.Btp260DeadAll
import FrozenRegistry.Btp260SourceAll
import FrozenRegistry.Btp260DeadSourceAll
import FrozenRegistry.Btp260IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenBool : PlaneExtBool plane260BtpGenConfig where
  hSectionCoset := plane260BtpGenSectionAll
  hDeadCover := plane260BtpGenDeadAll
  hPlaneLeSource := plane260BtpGenSourceAll
  hPlaneLeDead := plane260BtpGenDeadSourceAll
  hIndicator := plane260BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
