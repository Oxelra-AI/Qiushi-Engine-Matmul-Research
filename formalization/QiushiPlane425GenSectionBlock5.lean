import QiushiPlane425GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane425GenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane425GenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane425GenSectionProperty, plane425GenConfig, plane425GenOccSys]
  decide +kernel
end QiushiMatmul
