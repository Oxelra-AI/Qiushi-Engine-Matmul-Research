import QiushiGlobalOrbitUnused306CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane306UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 30,
    plane306UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane306UnusedGenIndicatorProperty, plane306UnusedGenConfig, plane306UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
