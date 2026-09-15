import QiushiGlobalOrbitUnused92CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane92UnusedGenSectionBlock1 : forall offset : Fin 32,
    forall hlt : 1 * 32 + offset.val < 512,
    plane92UnusedGenSectionProperty (Fin.mk (1 * 32 + offset.val) hlt) := by
  simp only [plane92UnusedGenSectionProperty, plane92UnusedGenConfig, plane92UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
