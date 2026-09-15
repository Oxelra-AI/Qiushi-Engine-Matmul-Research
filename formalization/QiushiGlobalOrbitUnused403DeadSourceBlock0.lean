import QiushiGlobalOrbitUnused403CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane403UnusedGenDeadSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 13,
    plane403UnusedGenDeadSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane403UnusedGenDeadSourceProperty, plane403UnusedGenConfig, plane403UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
