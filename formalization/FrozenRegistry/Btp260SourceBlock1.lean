import FrozenRegistry.Btp260CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 33,
    plane260BtpGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane260BtpGenSourceProperty, plane260BtpGenConfig, plane260BtpGenOccSys]
  decide +kernel
end QiushiMatmul
