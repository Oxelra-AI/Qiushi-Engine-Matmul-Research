import QiushiGlobalOrbitUnused394CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane394UnusedGenSectionBlock8 : forall offset : Fin 32,
    forall hlt : 8 * 32 + offset.val < 512,
    plane394UnusedGenSectionProperty (Fin.mk (8 * 32 + offset.val) hlt) := by
  simp only [plane394UnusedGenSectionProperty, plane394UnusedGenConfig, plane394UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
