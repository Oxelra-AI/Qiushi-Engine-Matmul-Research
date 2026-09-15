import QiushiGlobalOrbitUnused301CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane301UnusedGenDeadSourceBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 18,
    plane301UnusedGenDeadSourceProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane301UnusedGenDeadSourceProperty, plane301UnusedGenConfig, plane301UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
