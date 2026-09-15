import QiushiGlobalOrbitUnused321CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane321UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 49,
    plane321UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane321UnusedGenSourceProperty, plane321UnusedGenConfig, plane321UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
