import QiushiPlane456GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane456GenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane456GenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane456GenSectionProperty, plane456GenConfig, plane456GenOccSys]
  decide +kernel
end QiushiMatmul
