import QiushiGlobalOrbitUnused406CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane406UnusedGenSectionBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane406UnusedGenSectionProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane406UnusedGenSectionProperty, plane406UnusedGenConfig, plane406UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
