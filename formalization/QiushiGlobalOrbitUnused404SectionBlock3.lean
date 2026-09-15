import QiushiGlobalOrbitUnused404CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane404UnusedGenSectionBlock3 : forall offset : Fin 128,
    forall hlt : 3 * 128 + offset.val < 512,
    plane404UnusedGenSectionProperty (Fin.mk (3 * 128 + offset.val) hlt) := by
  simp only [plane404UnusedGenSectionProperty, plane404UnusedGenConfig, plane404UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
