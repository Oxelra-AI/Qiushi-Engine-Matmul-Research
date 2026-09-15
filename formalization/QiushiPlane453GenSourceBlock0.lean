import QiushiPlane453GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane453GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 210,
    plane453GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane453GenSourceProperty, plane453GenConfig, plane453GenOccSys]
  decide +kernel
end QiushiMatmul
