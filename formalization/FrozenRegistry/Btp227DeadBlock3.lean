import FrozenRegistry.Btp227CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane227BtpGenDeadBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane227BtpGenDeadProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane227BtpGenDeadProperty, plane227BtpGenConfig, plane227BtpGenOccSys]
  decide +kernel
end QiushiMatmul
