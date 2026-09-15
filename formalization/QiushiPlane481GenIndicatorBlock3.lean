import QiushiPlane481GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane481GenIndicatorBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 116,
    plane481GenIndicatorProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane481GenIndicatorProperty, plane481GenConfig, plane481GenOccSys]
  decide +kernel
end QiushiMatmul
