import FrozenRegistry.Btp224CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane224BtpGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 15,
    plane224BtpGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane224BtpGenIndicatorProperty, plane224BtpGenConfig, plane224BtpGenOccSys]
  decide +kernel
end QiushiMatmul
