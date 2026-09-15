import FrozenRegistry.Btp260CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane260BtpGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane260BtpGenSectionProperty, plane260BtpGenConfig, plane260BtpGenOccSys]
  decide +kernel
end QiushiMatmul
