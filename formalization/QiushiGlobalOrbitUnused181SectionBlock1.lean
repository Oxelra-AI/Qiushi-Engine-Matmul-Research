import QiushiGlobalOrbitUnused181CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane181UnusedGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane181UnusedGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane181UnusedGenSectionProperty, plane181UnusedGenConfig, plane181UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
