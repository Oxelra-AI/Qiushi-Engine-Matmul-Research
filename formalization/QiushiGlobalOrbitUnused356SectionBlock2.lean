import QiushiGlobalOrbitUnused356CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane356UnusedGenSectionBlock2 : forall offset : Fin 128,
    forall hlt : 2 * 128 + offset.val < 512,
    plane356UnusedGenSectionProperty (Fin.mk (2 * 128 + offset.val) hlt) := by
  simp only [plane356UnusedGenSectionProperty, plane356UnusedGenConfig, plane356UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
