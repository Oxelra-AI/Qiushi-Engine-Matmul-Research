import QiushiPlane482GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane482GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 118,
    plane482GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane482GenSourceProperty, plane482GenConfig, plane482GenOccSys]
  decide +kernel
end QiushiMatmul
