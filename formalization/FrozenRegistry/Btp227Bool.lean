import FrozenRegistry.Btp227SectionAll
import FrozenRegistry.Btp227DeadAll
import FrozenRegistry.Btp227SourceAll
import FrozenRegistry.Btp227DeadSourceAll
import FrozenRegistry.Btp227IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane227BtpGenBool : PlaneExtBool plane227BtpGenConfig where
  hSectionCoset := plane227BtpGenSectionAll
  hDeadCover := plane227BtpGenDeadAll
  hPlaneLeSource := plane227BtpGenSourceAll
  hPlaneLeDead := plane227BtpGenDeadSourceAll
  hIndicator := plane227BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
