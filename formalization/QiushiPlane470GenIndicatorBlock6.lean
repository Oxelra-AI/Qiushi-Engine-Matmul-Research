import QiushiPlane470GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470GenIndicatorBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 232,
    plane470GenIndicatorProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane470GenIndicatorProperty, plane470GenConfig, plane470GenOccSys]
  decide +kernel
end QiushiMatmul
