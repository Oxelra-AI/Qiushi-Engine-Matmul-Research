import QiushiGlobalOrbitUnused307CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane307UnusedGenSectionBlock3 : forall offset : Fin 128,
    forall hlt : 3 * 128 + offset.val < 512,
    plane307UnusedGenSectionProperty (Fin.mk (3 * 128 + offset.val) hlt) := by
  simp only [plane307UnusedGenSectionProperty, plane307UnusedGenConfig, plane307UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
