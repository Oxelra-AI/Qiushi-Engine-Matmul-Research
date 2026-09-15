import QiushiPlane488GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 413,
    plane488GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane488GenIndicatorProperty, plane488GenConfig, plane488GenOccSys]
  decide +kernel
end QiushiMatmul
