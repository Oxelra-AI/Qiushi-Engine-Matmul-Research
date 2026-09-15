import QiushiPlane254GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane254GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 26,
    plane254GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane254GenSourceProperty, plane254GenConfig, plane254GenOccSys]
  decide +kernel
end QiushiMatmul
