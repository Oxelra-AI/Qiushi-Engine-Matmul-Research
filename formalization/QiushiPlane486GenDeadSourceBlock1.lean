import QiushiPlane486GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 86,
    plane486GenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane486GenDeadSourceProperty, plane486GenConfig, plane486GenOccSys]
  decide +kernel
end QiushiMatmul
