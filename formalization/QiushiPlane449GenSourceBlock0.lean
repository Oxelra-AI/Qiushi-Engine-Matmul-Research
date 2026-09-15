import QiushiPlane449GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane449GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 56,
    plane449GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane449GenSourceProperty, plane449GenConfig, plane449GenOccSys]
  decide +kernel
end QiushiMatmul
