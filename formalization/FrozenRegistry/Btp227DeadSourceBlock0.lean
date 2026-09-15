import FrozenRegistry.Btp227CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane227BtpGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 1,
    plane227BtpGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane227BtpGenDeadSourceProperty, plane227BtpGenConfig, plane227BtpGenOccSys]
  decide +kernel
end QiushiMatmul
