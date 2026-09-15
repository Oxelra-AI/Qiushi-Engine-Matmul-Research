import QiushiPlane426GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenIndicatorBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 340,
    plane426GenIndicatorProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane426GenIndicatorProperty, plane426GenConfig, plane426GenOccSys]
  decide +kernel
end QiushiMatmul
