import QiushiGlobalOrbitUnused312CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane312UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 20,
    plane312UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane312UnusedGenSourceProperty, plane312UnusedGenConfig, plane312UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
