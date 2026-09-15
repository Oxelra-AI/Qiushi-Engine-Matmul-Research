import QiushiPlane449GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane449GenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane449GenSectionProperty, plane449GenConfig, plane449GenOccSys]
  decide +kernel
end QiushiMatmul
