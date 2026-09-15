import QiushiPlane274GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane274GenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 29,
    plane274GenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane274GenIndicatorProperty, plane274GenConfig, plane274GenOccSys]
  decide +kernel
end QiushiMatmul
