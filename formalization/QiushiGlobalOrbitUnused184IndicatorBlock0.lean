import QiushiGlobalOrbitUnused184CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane184UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 14,
    plane184UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane184UnusedGenIndicatorProperty, plane184UnusedGenConfig, plane184UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
