import QiushiGlobalOrbitUnused383CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane383UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 28,
    plane383UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane383UnusedGenIndicatorProperty, plane383UnusedGenConfig, plane383UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
