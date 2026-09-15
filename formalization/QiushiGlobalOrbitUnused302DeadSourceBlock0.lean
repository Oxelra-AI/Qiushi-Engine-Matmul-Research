import QiushiGlobalOrbitUnused302CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 22,
    plane302UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane302UnusedGenDeadSourceProperty, plane302UnusedGenConfig, plane302UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
