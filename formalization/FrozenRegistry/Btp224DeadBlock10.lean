import FrozenRegistry.Btp224CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane224BtpGenDeadBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane224BtpGenDeadProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane224BtpGenDeadProperty, plane224BtpGenConfig, plane224BtpGenOccSys]
  decide +kernel
end QiushiMatmul
