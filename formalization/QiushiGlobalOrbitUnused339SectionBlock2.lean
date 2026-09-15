import QiushiGlobalOrbitUnused339CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane339UnusedGenSectionBlock2 : forall offset : Fin 32,
    forall hlt : 2 * 32 + offset.val < 512,
    plane339UnusedGenSectionProperty (Fin.mk (2 * 32 + offset.val) hlt) := by
  simp only [plane339UnusedGenSectionProperty, plane339UnusedGenConfig, plane339UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
