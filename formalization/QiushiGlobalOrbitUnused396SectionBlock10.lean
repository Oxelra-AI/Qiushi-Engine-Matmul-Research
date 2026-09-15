import QiushiGlobalOrbitUnused396CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane396UnusedGenSectionBlock10 : forall offset : Fin 32,
    forall hlt : 10 * 32 + offset.val < 512,
    plane396UnusedGenSectionProperty (Fin.mk (10 * 32 + offset.val) hlt) := by
  simp only [plane396UnusedGenSectionProperty, plane396UnusedGenConfig, plane396UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
