import FrozenRegistry.Btp261CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane261BtpGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane261BtpGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane261BtpGenDeadProperty, plane261BtpGenConfig, plane261BtpGenOccSys]
  decide +kernel
end QiushiMatmul
