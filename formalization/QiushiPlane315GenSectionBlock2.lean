import QiushiPlane315GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane315GenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane315GenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane315GenSectionProperty, plane315GenConfig, plane315GenOccSys]
  decide +kernel
end QiushiMatmul
