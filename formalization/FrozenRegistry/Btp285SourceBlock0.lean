import FrozenRegistry.Btp285CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane285BtpGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 39,
    plane285BtpGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane285BtpGenSourceProperty, plane285BtpGenConfig, plane285BtpGenOccSys]
  decide +kernel
end QiushiMatmul
