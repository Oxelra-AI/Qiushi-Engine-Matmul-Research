import QiushiPlane470LowerGenCheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane470LowerGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 52,
    plane470LowerGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane470LowerGenIndicatorProperty, plane470LowerGenConfig, plane470LowerGenOccSys]
  decide +kernel
end QiushiMatmul
