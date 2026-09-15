import QiushiGlobalOrbitUnused291CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane291UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 33,
    plane291UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane291UnusedGenIndicatorProperty, plane291UnusedGenConfig, plane291UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
