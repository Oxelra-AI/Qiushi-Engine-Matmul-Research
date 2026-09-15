import QiushiPlane488GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane488GenDeadBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane488GenDeadProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane488GenDeadProperty, plane488GenConfig, plane488GenOccSys]
  decide +kernel
end QiushiMatmul
