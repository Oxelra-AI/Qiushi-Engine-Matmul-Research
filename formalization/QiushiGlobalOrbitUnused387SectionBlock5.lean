import QiushiGlobalOrbitUnused387CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane387UnusedGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane387UnusedGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane387UnusedGenSectionProperty, plane387UnusedGenConfig, plane387UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
