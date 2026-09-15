import FrozenRegistry.Btp285CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane285BtpGenDeadBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane285BtpGenDeadProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane285BtpGenDeadProperty, plane285BtpGenConfig, plane285BtpGenOccSys]
  decide +kernel
end QiushiMatmul
