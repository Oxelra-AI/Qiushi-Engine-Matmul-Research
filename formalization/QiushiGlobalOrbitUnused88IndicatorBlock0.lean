import QiushiGlobalOrbitUnused88CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane88UnusedGenIndicatorBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 13,
    plane88UnusedGenIndicatorProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane88UnusedGenIndicatorProperty, plane88UnusedGenConfig, plane88UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
