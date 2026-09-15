import QiushiPlane336GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane336GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 34,
    plane336GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane336GenIndicatorProperty, plane336GenConfig, plane336GenOccSys]
  decide +kernel
end QiushiMatmul
