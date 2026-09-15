import QiushiPlane275GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane275GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 29,
    plane275GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane275GenIndicatorProperty, plane275GenConfig, plane275GenOccSys]
  decide +kernel
end QiushiMatmul
