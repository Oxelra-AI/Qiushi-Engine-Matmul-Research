import QiushiGlobalOrbitUnused273CheckProperties
set_option maxHeartbeats 80000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 512
namespace QiushiMatmul
theorem plane273UnusedGenSectionBlock7 : forall offset : Fin 32,
    forall hlt : 7 * 32 + offset.val < 512,
    plane273UnusedGenSectionProperty (Fin.mk (7 * 32 + offset.val) hlt) := by
  simp only [plane273UnusedGenSectionProperty, plane273UnusedGenConfig, plane273UnusedGenOccSys]
  decide +kernel
end QiushiMatmul
