import QiushiGlobalOrbitUnused356CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane356UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 27,
    plane356UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane356UnusedGenIndicatorProperty, plane356UnusedGenConfig, plane356UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
