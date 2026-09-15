import QiushiGlobalOrbitUnused390CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane390UnusedGenSectionBlock12 : forall offset : Fin 32,
    forall hlt : 12 * 32 + offset.val < 512,
    plane390UnusedGenSectionProperty (Fin.mk (12 * 32 + offset.val) hlt) := by
  simp only [plane390UnusedGenSectionProperty, plane390UnusedGenConfig, plane390UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
