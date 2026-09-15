import QiushiGlobalOrbitUnused284CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane284UnusedGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane284UnusedGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane284UnusedGenSectionProperty, plane284UnusedGenConfig, plane284UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
