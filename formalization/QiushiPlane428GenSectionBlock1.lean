import QiushiPlane428GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane428GenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane428GenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane428GenSectionProperty, plane428GenConfig, plane428GenOccSys]
  decide +kernel
end QiushiMatmul
