import QiushiPlane413GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane413GenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 41,
    plane413GenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane413GenDeadSourceProperty, plane413GenConfig, plane413GenOccSys]
  decide +kernel
end QiushiMatmul
