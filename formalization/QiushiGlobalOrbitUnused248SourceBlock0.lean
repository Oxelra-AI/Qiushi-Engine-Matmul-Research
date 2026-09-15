import QiushiGlobalOrbitUnused248CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane248UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 23,
    plane248UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane248UnusedGenSourceProperty, plane248UnusedGenConfig, plane248UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
