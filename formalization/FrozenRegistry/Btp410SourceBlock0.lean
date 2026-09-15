import FrozenRegistry.Btp410CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane410BtpGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 63,
    plane410BtpGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane410BtpGenSourceProperty, plane410BtpGenConfig, plane410BtpGenOccSys]
  decide +kernel
end QiushiMatmul
