import QiushiGlobalOrbitUnused353CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane353UnusedGenDeadBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane353UnusedGenDeadProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane353UnusedGenDeadProperty, plane353UnusedGenConfig, plane353UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
