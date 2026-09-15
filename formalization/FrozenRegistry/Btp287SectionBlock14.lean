import FrozenRegistry.Btp287CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane287BtpGenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane287BtpGenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane287BtpGenSectionProperty, plane287BtpGenConfig, plane287BtpGenOccSys]
  decide +kernel
end QiushiMatmul
