import QiushiGlobalOrbitUnused308CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 19,
    plane308UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane308UnusedGenDeadSourceProperty, plane308UnusedGenConfig, plane308UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
