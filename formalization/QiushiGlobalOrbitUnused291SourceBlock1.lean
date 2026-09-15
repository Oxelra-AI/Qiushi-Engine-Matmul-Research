import QiushiGlobalOrbitUnused291CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane291UnusedGenSourceBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 33,
    plane291UnusedGenSourceProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane291UnusedGenSourceProperty, plane291UnusedGenConfig, plane291UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
