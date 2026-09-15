import QiushiPlane466GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane466GenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane466GenDeadSourceProperty, plane466GenConfig, plane466GenOccSys]
  decide +kernel
end QiushiMatmul
