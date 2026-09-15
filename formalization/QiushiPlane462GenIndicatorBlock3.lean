import QiushiPlane462GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane462GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 294,
    plane462GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane462GenIndicatorProperty, plane462GenConfig, plane462GenOccSys]
  decide +kernel
end QiushiMatmul
