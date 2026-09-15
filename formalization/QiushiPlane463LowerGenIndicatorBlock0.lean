import QiushiPlane463LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane463LowerGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 49,
    plane463LowerGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane463LowerGenIndicatorProperty, plane463LowerGenConfig, plane463LowerGenOccSys]
  decide +kernel
end QiushiMatmul
