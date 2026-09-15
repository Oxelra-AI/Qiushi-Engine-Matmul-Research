import QiushiGlobalOrbitUnused289CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane289UnusedGenSectionBlock15 : forall offset : Fin 32,
    forall hlt : 15 * 32 + offset.val < 512,
    plane289UnusedGenSectionProperty (Fin.mk (15 * 32 + offset.val) hlt) := by
  simp only [plane289UnusedGenSectionProperty, plane289UnusedGenConfig, plane289UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
