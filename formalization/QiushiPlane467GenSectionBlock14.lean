import QiushiPlane467GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane467GenSectionBlock14 : forall offset : Fin 32,
    forall hlt : 14 * 32 + offset.val < 512,
    plane467GenSectionProperty (Fin.mk (14 * 32 + offset.val) hlt) := by
  simp only [plane467GenSectionProperty, plane467GenConfig, plane467GenOccSys]
  decide +kernel
end QiushiMatmul
