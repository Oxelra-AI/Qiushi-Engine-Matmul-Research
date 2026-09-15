import QiushiGlobalOrbitUnused380CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane380UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 26,
    plane380UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane380UnusedGenIndicatorProperty, plane380UnusedGenConfig, plane380UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
