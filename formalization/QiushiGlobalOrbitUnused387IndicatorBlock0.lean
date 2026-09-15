import QiushiGlobalOrbitUnused387CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane387UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 32,
    plane387UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane387UnusedGenIndicatorProperty, plane387UnusedGenConfig, plane387UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
