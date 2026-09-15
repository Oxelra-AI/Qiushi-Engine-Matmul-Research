import QiushiGlobalOrbitUnused353CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane353UnusedGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 39,
    plane353UnusedGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane353UnusedGenSourceProperty, plane353UnusedGenConfig, plane353UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
