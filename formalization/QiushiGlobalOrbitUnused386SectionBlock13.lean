import QiushiGlobalOrbitUnused386CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane386UnusedGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane386UnusedGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane386UnusedGenSectionProperty, plane386UnusedGenConfig, plane386UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
