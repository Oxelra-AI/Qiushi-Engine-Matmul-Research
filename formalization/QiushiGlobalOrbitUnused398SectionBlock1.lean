import QiushiGlobalOrbitUnused398CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane398UnusedGenSectionBlock1 : forall offset : Fin 128,
    forall hlt : 1 * 128 + offset.val < 512,
    plane398UnusedGenSectionProperty (Fin.mk (1 * 128 + offset.val) hlt) := by
  simp only [plane398UnusedGenSectionProperty, plane398UnusedGenConfig, plane398UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
