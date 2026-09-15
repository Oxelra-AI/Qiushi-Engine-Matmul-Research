import QiushiPlane484GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane484GenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 84,
    plane484GenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane484GenDeadSourceProperty, plane484GenConfig, plane484GenOccSys]
  decide +kernel
end QiushiMatmul
