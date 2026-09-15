import FrozenRegistry.Btp263CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane263BtpGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 31,
    plane263BtpGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane263BtpGenSourceProperty, plane263BtpGenConfig, plane263BtpGenOccSys]
  decide +kernel
end QiushiMatmul
