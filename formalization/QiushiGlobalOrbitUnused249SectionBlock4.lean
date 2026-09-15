import QiushiGlobalOrbitUnused249CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane249UnusedGenSectionBlock4 : forall offset : Fin 32,
    forall hlt : 4 * 32 + offset.val < 512,
    plane249UnusedGenSectionProperty (Fin.mk (4 * 32 + offset.val) hlt) := by
  simp only [plane249UnusedGenSectionProperty, plane249UnusedGenConfig, plane249UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
