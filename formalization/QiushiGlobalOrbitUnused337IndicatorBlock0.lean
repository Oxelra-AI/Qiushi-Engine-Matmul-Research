import QiushiGlobalOrbitUnused337CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane337UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 30,
    plane337UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane337UnusedGenIndicatorProperty, plane337UnusedGenConfig, plane337UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
