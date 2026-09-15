import QiushiGlobalOrbitUnused312CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane312UnusedGenSectionBlock5 : forall offset : Fin 32,
    forall hlt : 5 * 32 + offset.val < 512,
    plane312UnusedGenSectionProperty (Fin.mk (5 * 32 + offset.val) hlt) := by
  simp only [plane312UnusedGenSectionProperty, plane312UnusedGenConfig, plane312UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
