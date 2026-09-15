import FrozenRegistry.Btp261CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane261BtpGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 34,
    plane261BtpGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane261BtpGenSourceProperty, plane261BtpGenConfig, plane261BtpGenOccSys]
  decide +kernel
end QiushiMatmul
