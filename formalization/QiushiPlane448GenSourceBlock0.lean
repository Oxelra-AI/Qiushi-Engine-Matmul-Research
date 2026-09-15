import QiushiPlane448GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane448GenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 56,
    plane448GenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane448GenSourceProperty, plane448GenConfig, plane448GenOccSys]
  decide +kernel
end QiushiMatmul
