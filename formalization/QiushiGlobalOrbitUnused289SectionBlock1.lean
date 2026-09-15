import QiushiGlobalOrbitUnused289CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane289UnusedGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane289UnusedGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane289UnusedGenSectionProperty, plane289UnusedGenConfig, plane289UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
