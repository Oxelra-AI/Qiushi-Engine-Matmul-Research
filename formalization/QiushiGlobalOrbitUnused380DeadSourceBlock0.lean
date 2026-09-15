import QiushiGlobalOrbitUnused380CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 21,
    plane380UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane380UnusedGenDeadSourceProperty, plane380UnusedGenConfig, plane380UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
