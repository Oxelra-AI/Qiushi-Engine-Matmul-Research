import FrozenRegistry.Btp285CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane285BtpGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane285BtpGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane285BtpGenSectionProperty, plane285BtpGenConfig, plane285BtpGenOccSys]
  decide +kernel
end QiushiMatmul
