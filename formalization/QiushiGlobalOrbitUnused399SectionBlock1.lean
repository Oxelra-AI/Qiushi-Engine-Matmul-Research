import QiushiGlobalOrbitUnused399CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane399UnusedGenSectionBlock1 : forall offset : Fin 128,
    forall hlt : 1 * 128 + offset.val < 512,
    plane399UnusedGenSectionProperty (Fin.mk (1 * 128 + offset.val) hlt) := by
  simp only [plane399UnusedGenSectionProperty, plane399UnusedGenConfig, plane399UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
