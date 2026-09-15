import QiushiGlobalOrbitUnused308CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane308UnusedGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane308UnusedGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane308UnusedGenSectionProperty, plane308UnusedGenConfig, plane308UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
