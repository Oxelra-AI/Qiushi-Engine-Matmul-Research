import QiushiPlane278GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane278GenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 8,
    plane278GenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane278GenDeadSourceProperty, plane278GenConfig, plane278GenOccSys]
  decide +kernel
end QiushiMatmul
