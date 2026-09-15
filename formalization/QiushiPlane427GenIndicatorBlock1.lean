import QiushiPlane427GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane427GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 237,
    plane427GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane427GenIndicatorProperty, plane427GenConfig, plane427GenOccSys]
  decide +kernel
end QiushiMatmul
