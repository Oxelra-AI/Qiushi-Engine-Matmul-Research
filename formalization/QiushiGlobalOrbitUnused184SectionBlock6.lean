import QiushiGlobalOrbitUnused184CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane184UnusedGenSectionBlock6 : forall offset : Fin 32,
    forall hlt : 6 * 32 + offset.val < 512,
    plane184UnusedGenSectionProperty (Fin.mk (6 * 32 + offset.val) hlt) := by
  simp only [plane184UnusedGenSectionProperty, plane184UnusedGenConfig, plane184UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
