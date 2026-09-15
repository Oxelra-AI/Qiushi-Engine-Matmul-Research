import QiushiGlobalOrbitUnused306CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane306UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 14,
    plane306UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane306UnusedGenDeadSourceProperty, plane306UnusedGenConfig, plane306UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
