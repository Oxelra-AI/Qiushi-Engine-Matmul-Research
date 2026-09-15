import QiushiGlobalOrbitUnused291CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane291UnusedGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane291UnusedGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane291UnusedGenSectionProperty, plane291UnusedGenConfig, plane291UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
