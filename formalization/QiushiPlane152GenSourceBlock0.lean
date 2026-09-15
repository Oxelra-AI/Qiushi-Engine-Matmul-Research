import QiushiPlane152GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane152GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 16,
    plane152GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane152GenSourceProperty, plane152GenConfig, plane152GenOccSys]
  decide +kernel
end QiushiMatmul
