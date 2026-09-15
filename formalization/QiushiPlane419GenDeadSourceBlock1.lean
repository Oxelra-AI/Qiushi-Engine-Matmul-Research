import QiushiPlane419GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane419GenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 38,
    plane419GenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane419GenDeadSourceProperty, plane419GenConfig, plane419GenOccSys]
  decide +kernel
end QiushiMatmul
