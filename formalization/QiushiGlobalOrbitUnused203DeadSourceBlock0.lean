import QiushiGlobalOrbitUnused203CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane203UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 11,
    plane203UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane203UnusedGenDeadSourceProperty, plane203UnusedGenConfig, plane203UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
