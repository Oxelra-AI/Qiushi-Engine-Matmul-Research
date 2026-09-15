import FrozenRegistry.Btp265CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane265BtpGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane265BtpGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane265BtpGenSectionProperty, plane265BtpGenConfig, plane265BtpGenOccSys]
  decide +kernel
end QiushiMatmul
