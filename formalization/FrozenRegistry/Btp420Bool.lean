import FrozenRegistry.Btp420SectionAll
import FrozenRegistry.Btp420DeadAll
import FrozenRegistry.Btp420SourceAll
import FrozenRegistry.Btp420DeadSourceAll
import FrozenRegistry.Btp420IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane420BtpGenBool : PlaneExtBool plane420BtpGenConfig where
  hSectionCoset := plane420BtpGenSectionAll
  hDeadCover := plane420BtpGenDeadAll
  hPlaneLeSource := plane420BtpGenSourceAll
  hPlaneLeDead := plane420BtpGenDeadSourceAll
  hIndicator := plane420BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
