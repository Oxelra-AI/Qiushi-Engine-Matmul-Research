import QiushiGlobalOrbitUnused406CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane406UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 18,
    plane406UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane406UnusedGenSourceProperty, plane406UnusedGenConfig, plane406UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
