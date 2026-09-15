import QiushiGlobalOrbitUnused353CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane353UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 39,
    plane353UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane353UnusedGenIndicatorProperty, plane353UnusedGenConfig, plane353UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
