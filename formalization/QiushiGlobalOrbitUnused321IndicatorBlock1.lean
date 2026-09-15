import QiushiGlobalOrbitUnused321CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane321UnusedGenIndicatorBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 49,
    plane321UnusedGenIndicatorProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane321UnusedGenIndicatorProperty, plane321UnusedGenConfig, plane321UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
