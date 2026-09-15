import FrozenRegistry.Btp265CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane265BtpGenDeadBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane265BtpGenDeadProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane265BtpGenDeadProperty, plane265BtpGenConfig, plane265BtpGenOccSys]
  decide +kernel
end QiushiMatmul
