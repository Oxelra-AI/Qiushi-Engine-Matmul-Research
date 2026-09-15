import QiushiGlobalOrbitUnused389CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane389UnusedGenSectionBlock3 : forall offset : Fin 32,
    forall hlt : 3 * 32 + offset.val < 512,
    plane389UnusedGenSectionProperty (Fin.mk (3 * 32 + offset.val) hlt) := by
  simp only [plane389UnusedGenSectionProperty, plane389UnusedGenConfig, plane389UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
