import FrozenRegistry.Btp224SectionAll
import FrozenRegistry.Btp224DeadAll
import FrozenRegistry.Btp224SourceAll
import FrozenRegistry.Btp224DeadSourceAll
import FrozenRegistry.Btp224IndicatorAll
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane224BtpGenBool : PlaneExtBool plane224BtpGenConfig where
  hSectionCoset := plane224BtpGenSectionAll
  hDeadCover := plane224BtpGenDeadAll
  hPlaneLeSource := plane224BtpGenSourceAll
  hPlaneLeDead := plane224BtpGenDeadSourceAll
  hIndicator := plane224BtpGenIndicatorAll
  hRhs := by intro i; rfl
  hTarget := rfl
end QiushiMatmul
