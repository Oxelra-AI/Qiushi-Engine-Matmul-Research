import QiushiGlobalOrbitUnused380CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenSourceBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 26,
    plane380UnusedGenSourceProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane380UnusedGenSourceProperty, plane380UnusedGenConfig, plane380UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
