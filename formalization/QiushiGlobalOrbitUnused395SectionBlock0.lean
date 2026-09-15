import QiushiGlobalOrbitUnused395CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane395UnusedGenSectionBlock0 : forall offset : Fin 32,
    forall hlt : 0 * 32 + offset.val < 512,
    plane395UnusedGenSectionProperty (Fin.mk (0 * 32 + offset.val) hlt) := by
  simp only [plane395UnusedGenSectionProperty, plane395UnusedGenConfig, plane395UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
