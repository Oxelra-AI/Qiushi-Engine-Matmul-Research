import QiushiPlane486GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane486GenSourceBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 262,
    plane486GenSourceProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane486GenSourceProperty, plane486GenConfig, plane486GenOccSys]
  decide +kernel
end QiushiMatmul
