import QiushiGlobalOrbitUnused386CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane386UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane386UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane386UnusedGenDeadSourceProperty, plane386UnusedGenConfig, plane386UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
