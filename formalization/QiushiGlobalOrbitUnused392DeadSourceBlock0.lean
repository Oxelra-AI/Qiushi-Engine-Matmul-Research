import QiushiGlobalOrbitUnused392CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane392UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 24,
    plane392UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane392UnusedGenDeadSourceProperty, plane392UnusedGenConfig, plane392UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
