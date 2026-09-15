import QiushiPlane485GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane485GenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane485GenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane485GenSectionProperty, plane485GenConfig, plane485GenOccSys]
  decide +kernel
end QiushiMatmul
