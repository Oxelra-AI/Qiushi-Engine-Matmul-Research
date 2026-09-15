import FrozenRegistry.Btp410CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane410BtpGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane410BtpGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane410BtpGenSectionProperty, plane410BtpGenConfig, plane410BtpGenOccSys]
  decide +kernel
end QiushiMatmul
