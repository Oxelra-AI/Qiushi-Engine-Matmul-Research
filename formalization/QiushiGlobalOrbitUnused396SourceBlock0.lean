import QiushiGlobalOrbitUnused396CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane396UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 32,
    plane396UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane396UnusedGenSourceProperty, plane396UnusedGenConfig, plane396UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
