import QiushiGlobalOrbitUnused392CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane392UnusedGenSectionBlock13 : forall offset : Fin 32,
    forall hlt : 13 * 32 + offset.val < 512,
    plane392UnusedGenSectionProperty (Fin.mk (13 * 32 + offset.val) hlt) := by
  simp only [plane392UnusedGenSectionProperty, plane392UnusedGenConfig, plane392UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
