import QiushiPlane447GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane447GenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 55,
    plane447GenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane447GenSourceProperty, plane447GenConfig, plane447GenOccSys]
  decide +kernel
end QiushiMatmul
