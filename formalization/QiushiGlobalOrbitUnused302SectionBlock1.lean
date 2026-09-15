import QiushiGlobalOrbitUnused302CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane302UnusedGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane302UnusedGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane302UnusedGenSectionProperty, plane302UnusedGenConfig, plane302UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
