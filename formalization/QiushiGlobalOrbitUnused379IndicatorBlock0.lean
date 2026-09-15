import QiushiGlobalOrbitUnused379CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane379UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 22,
    plane379UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane379UnusedGenIndicatorProperty, plane379UnusedGenConfig, plane379UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
