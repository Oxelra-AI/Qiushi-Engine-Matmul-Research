import FrozenRegistry.Btp420CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane420BtpGenDeadBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane420BtpGenDeadProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane420BtpGenDeadProperty, plane420BtpGenConfig, plane420BtpGenOccSys]
  decide +kernel
end QiushiMatmul
