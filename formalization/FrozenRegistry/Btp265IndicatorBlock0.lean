import FrozenRegistry.Btp265CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane265BtpGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 31,
    plane265BtpGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane265BtpGenIndicatorProperty, plane265BtpGenConfig, plane265BtpGenOccSys]
  decide +kernel
end QiushiMatmul
