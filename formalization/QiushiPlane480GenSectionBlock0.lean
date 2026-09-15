import QiushiPlane480GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane480GenSectionBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 512,
    plane480GenSectionProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane480GenSectionProperty, plane480GenConfig, plane480GenOccSys]
  decide +kernel
end QiushiMatmul
