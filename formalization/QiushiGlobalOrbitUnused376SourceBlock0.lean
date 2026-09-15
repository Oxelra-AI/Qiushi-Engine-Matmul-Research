import QiushiGlobalOrbitUnused376CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane376UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 15,
    plane376UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane376UnusedGenSourceProperty, plane376UnusedGenConfig, plane376UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
