import FrozenRegistry.Btp261SectionAll
import FrozenRegistry.Btp261DeadAll
import FrozenRegistry.Btp261SourceAll
import FrozenRegistry.Btp261DeadSourceAll
import FrozenRegistry.Btp261IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane261BtpGenBool : PlaneExtBool plane261BtpGenConfig where
  hSectionCoset := plane261BtpGenSectionAll
  hDeadCover := plane261BtpGenDeadAll
  hPlaneLeSource := plane261BtpGenSourceAll
  hPlaneLeDead := plane261BtpGenDeadSourceAll
  hIndicator := plane261BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
