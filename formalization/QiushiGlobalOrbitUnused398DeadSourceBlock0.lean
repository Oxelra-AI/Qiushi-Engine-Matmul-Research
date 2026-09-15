import QiushiGlobalOrbitUnused398CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane398UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 14,
    plane398UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane398UnusedGenDeadSourceProperty, plane398UnusedGenConfig, plane398UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
