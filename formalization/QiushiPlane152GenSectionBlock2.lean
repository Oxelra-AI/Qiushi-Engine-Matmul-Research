import QiushiPlane152GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane152GenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane152GenSectionProperty, plane152GenConfig, plane152GenOccSys]
  decide +kernel
end QiushiMatmul
