import QiushiPlane428GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane428GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 51,
    plane428GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane428GenSourceProperty, plane428GenConfig, plane428GenOccSys]
  decide +kernel
end QiushiMatmul
