import QiushiPlane426GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane426GenIndicatorBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 340,
    plane426GenIndicatorProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane426GenIndicatorProperty, plane426GenConfig, plane426GenOccSys]
  decide +kernel
end QiushiMatmul
