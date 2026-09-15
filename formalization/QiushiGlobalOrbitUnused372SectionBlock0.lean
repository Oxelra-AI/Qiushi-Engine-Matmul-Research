import QiushiGlobalOrbitUnused372CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane372UnusedGenSectionBlock0 : forall offset : Fin 128,
    forall hlt : 0 * 128 + offset.val < 512,
    plane372UnusedGenSectionProperty (Fin.mk (0 * 128 + offset.val) hlt) := by
  simp only [plane372UnusedGenSectionProperty, plane372UnusedGenConfig, plane372UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
