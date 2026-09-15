import QiushiGlobalOrbitUnused309CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane309UnusedGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane309UnusedGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane309UnusedGenSectionProperty, plane309UnusedGenConfig, plane309UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
