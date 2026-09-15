import QiushiGlobalOrbitUnused249CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane249UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 29,
    plane249UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane249UnusedGenSourceProperty, plane249UnusedGenConfig, plane249UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
