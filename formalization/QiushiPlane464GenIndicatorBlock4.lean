import QiushiPlane464GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane464GenIndicatorBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 202,
    plane464GenIndicatorProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane464GenIndicatorProperty, plane464GenConfig, plane464GenOccSys]
  decide +kernel
end QiushiMatmul
