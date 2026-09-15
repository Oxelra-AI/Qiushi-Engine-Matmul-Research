import QiushiGlobalOrbitUnused308CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 28,
    plane308UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane308UnusedGenSourceProperty, plane308UnusedGenConfig, plane308UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
