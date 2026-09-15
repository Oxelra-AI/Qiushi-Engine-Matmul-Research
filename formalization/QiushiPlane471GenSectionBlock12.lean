import QiushiPlane471GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane471GenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane471GenSectionProperty, plane471GenConfig, plane471GenOccSys]
  decide +kernel
end QiushiMatmul
