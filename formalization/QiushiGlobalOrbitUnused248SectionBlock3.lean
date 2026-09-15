import QiushiGlobalOrbitUnused248CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane248UnusedGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane248UnusedGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane248UnusedGenSectionProperty, plane248UnusedGenConfig, plane248UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
