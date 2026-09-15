import FrozenRegistry.Btp263CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane263BtpGenDeadBlock11 : forall offset : Fin 32,
    forall hlt : 11 * 32 + offset.val < 512,
    plane263BtpGenDeadProperty (Fin.mk (11 * 32 + offset.val) hlt) := by
  simp only [plane263BtpGenDeadProperty, plane263BtpGenConfig, plane263BtpGenOccSys]
  decide +kernel
end QiushiMatmul
