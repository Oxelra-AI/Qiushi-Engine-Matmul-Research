import QiushiPlane447GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane447GenDeadSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 50,
    plane447GenDeadSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane447GenDeadSourceProperty, plane447GenConfig, plane447GenOccSys]
  decide +kernel
end QiushiMatmul
