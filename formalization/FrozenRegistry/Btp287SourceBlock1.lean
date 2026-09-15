import FrozenRegistry.Btp287CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane287BtpGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 68,
    plane287BtpGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane287BtpGenSourceProperty, plane287BtpGenConfig, plane287BtpGenOccSys]
  decide +kernel
end QiushiMatmul
