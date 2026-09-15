import QiushiPlane430GenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane430GenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 57,
    plane430GenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane430GenIndicatorProperty, plane430GenConfig, plane430GenOccSys]
  decide +kernel
end QiushiMatmul
