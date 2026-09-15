import QiushiPlane466GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane466GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 210,
    plane466GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane466GenIndicatorProperty, plane466GenConfig, plane466GenOccSys]
  decide +kernel
end QiushiMatmul
