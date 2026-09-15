import QiushiPlane458GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane458GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 203,
    plane458GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane458GenIndicatorProperty, plane458GenConfig, plane458GenOccSys]
  decide +kernel
end QiushiMatmul
