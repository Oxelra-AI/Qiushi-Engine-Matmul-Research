import FrozenRegistry.Btp410SectionAll
import FrozenRegistry.Btp410DeadAll
import FrozenRegistry.Btp410SourceAll
import FrozenRegistry.Btp410DeadSourceAll
import FrozenRegistry.Btp410IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane410BtpGenBool : PlaneExtBool plane410BtpGenConfig where
  hSectionCoset := plane410BtpGenSectionAll
  hDeadCover := plane410BtpGenDeadAll
  hPlaneLeSource := plane410BtpGenSourceAll
  hPlaneLeDead := plane410BtpGenDeadSourceAll
  hIndicator := plane410BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
