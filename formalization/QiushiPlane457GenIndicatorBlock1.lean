import QiushiPlane457GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane457GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 178,
    plane457GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane457GenIndicatorProperty, plane457GenConfig, plane457GenOccSys]
  decide +kernel
end QiushiMatmul
