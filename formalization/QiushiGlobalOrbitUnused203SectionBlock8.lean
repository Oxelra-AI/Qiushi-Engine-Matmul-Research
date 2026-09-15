import QiushiGlobalOrbitUnused203CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane203UnusedGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane203UnusedGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane203UnusedGenSectionProperty, plane203UnusedGenConfig, plane203UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
