import QiushiGlobalOrbitUnused321CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane321UnusedGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane321UnusedGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane321UnusedGenSectionProperty, plane321UnusedGenConfig, plane321UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
