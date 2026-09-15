import QiushiGlobalOrbitUnused401CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane401UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 30,
    plane401UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane401UnusedGenIndicatorProperty, plane401UnusedGenConfig, plane401UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
