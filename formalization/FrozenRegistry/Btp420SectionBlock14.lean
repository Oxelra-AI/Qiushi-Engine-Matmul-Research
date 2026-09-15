import FrozenRegistry.Btp420CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane420BtpGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane420BtpGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane420BtpGenSectionProperty, plane420BtpGenConfig, plane420BtpGenOccSys]
  decide +kernel
end QiushiMatmul
