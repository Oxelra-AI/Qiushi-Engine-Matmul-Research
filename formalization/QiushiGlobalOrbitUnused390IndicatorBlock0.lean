import QiushiGlobalOrbitUnused390CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane390UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 26,
    plane390UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane390UnusedGenIndicatorProperty, plane390UnusedGenConfig, plane390UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
