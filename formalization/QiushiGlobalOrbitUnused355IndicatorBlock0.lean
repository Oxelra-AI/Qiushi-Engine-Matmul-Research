import QiushiGlobalOrbitUnused355CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane355UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 21,
    plane355UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane355UnusedGenIndicatorProperty, plane355UnusedGenConfig, plane355UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
