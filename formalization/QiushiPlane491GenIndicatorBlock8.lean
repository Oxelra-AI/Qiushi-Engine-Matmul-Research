import QiushiPlane491GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane491GenIndicatorBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 726,
    plane491GenIndicatorProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane491GenIndicatorProperty, plane491GenConfig, plane491GenOccSys]
  decide +kernel
end QiushiMatmul
