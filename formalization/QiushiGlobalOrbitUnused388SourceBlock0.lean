import QiushiGlobalOrbitUnused388CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane388UnusedGenSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 28,
    plane388UnusedGenSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane388UnusedGenSourceProperty, plane388UnusedGenConfig, plane388UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
