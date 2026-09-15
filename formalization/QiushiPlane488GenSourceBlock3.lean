import QiushiPlane488GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenSourceBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 413,
    plane488GenSourceProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane488GenSourceProperty, plane488GenConfig, plane488GenOccSys]
  decide +kernel
end QiushiMatmul
