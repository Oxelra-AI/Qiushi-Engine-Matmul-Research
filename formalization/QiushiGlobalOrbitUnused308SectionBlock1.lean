import QiushiGlobalOrbitUnused308CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane308UnusedGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane308UnusedGenSectionProperty, plane308UnusedGenConfig, plane308UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
