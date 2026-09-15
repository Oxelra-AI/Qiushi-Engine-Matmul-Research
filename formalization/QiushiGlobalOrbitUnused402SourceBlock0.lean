import QiushiGlobalOrbitUnused402CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane402UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 31,
    plane402UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane402UnusedGenSourceProperty, plane402UnusedGenConfig, plane402UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
