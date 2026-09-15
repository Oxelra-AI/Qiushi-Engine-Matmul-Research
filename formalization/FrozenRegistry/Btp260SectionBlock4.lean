import FrozenRegistry.Btp260CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane260BtpGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane260BtpGenSectionProperty, plane260BtpGenConfig, plane260BtpGenOccSys]
  decide +kernel
end QiushiMatmul
