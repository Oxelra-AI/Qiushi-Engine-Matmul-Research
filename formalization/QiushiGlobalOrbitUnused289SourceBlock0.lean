import QiushiGlobalOrbitUnused289CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane289UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 27,
    plane289UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane289UnusedGenSourceProperty, plane289UnusedGenConfig, plane289UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
