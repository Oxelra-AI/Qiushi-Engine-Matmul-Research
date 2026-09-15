import QiushiPlane471GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane471GenIndicatorBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 304,
    plane471GenIndicatorProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane471GenIndicatorProperty, plane471GenConfig, plane471GenOccSys]
  decide +kernel
end QiushiMatmul
