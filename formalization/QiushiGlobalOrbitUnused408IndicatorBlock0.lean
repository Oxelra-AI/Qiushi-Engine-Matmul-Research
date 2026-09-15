import QiushiGlobalOrbitUnused408CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane408UnusedGenIndicatorBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 25,
    plane408UnusedGenIndicatorProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane408UnusedGenIndicatorProperty, plane408UnusedGenConfig, plane408UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
