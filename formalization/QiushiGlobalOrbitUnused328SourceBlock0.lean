import QiushiGlobalOrbitUnused328CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane328UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 29,
    plane328UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane328UnusedGenSourceProperty, plane328UnusedGenConfig, plane328UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
