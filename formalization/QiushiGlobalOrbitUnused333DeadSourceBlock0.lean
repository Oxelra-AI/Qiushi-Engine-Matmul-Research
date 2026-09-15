import QiushiGlobalOrbitUnused333CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane333UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 29,
    plane333UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane333UnusedGenDeadSourceProperty, plane333UnusedGenConfig, plane333UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
