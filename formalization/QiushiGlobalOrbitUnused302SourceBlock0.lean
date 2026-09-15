import QiushiGlobalOrbitUnused302CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 25,
    plane302UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane302UnusedGenSourceProperty, plane302UnusedGenConfig, plane302UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
