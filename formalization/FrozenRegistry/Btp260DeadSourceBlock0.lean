import FrozenRegistry.Btp260CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane260BtpGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 1,
    plane260BtpGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane260BtpGenDeadSourceProperty, plane260BtpGenConfig, plane260BtpGenOccSys]
  decide +kernel
end QiushiMatmul
