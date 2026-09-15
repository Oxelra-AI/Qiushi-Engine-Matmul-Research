import QiushiPlane490GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane490GenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane490GenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane490GenSectionProperty, plane490GenConfig, plane490GenOccSys]
  decide +kernel
end QiushiMatmul
