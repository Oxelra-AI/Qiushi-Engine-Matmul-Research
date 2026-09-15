import QiushiGlobalOrbitUnused333CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane333UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 36,
    plane333UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane333UnusedGenSourceProperty, plane333UnusedGenConfig, plane333UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
